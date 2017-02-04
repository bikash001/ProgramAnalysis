#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include <set>
#include <string>
#include <map>
#include <queue>
#include "llvm/IR/CFG.h"

using namespace llvm;

class Liveness : public ModulePass {
	public:
		static char ID;
		Liveness() : ModulePass(ID) {
		}

		bool runOnModule(Module &M);
		void computeLiveness(Function &F);
	// private:
	// 	// std::set<std::string> vars;
	// 	std::map<std::string,BlockData> bblocks;
};

class BlockData
{
public:
	std::set<StringRef> use, def, in, out;
	BlockData() {}
	~BlockData() {}
	
};

bool Liveness::runOnModule(Module &M) {
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
		if (!F->isDeclaration()) {
			computeLiveness(*F);
		}
	}
	return false;
}

void Liveness::computeLiveness(Function &F) {
	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	BasicBlock *print_block = NULL;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
		std::set<StringRef> &def = temp.def;
		std::set<StringRef> &use = temp.use;
		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						Value *val = dyn_cast<Value>(I->getOperand(1));
						if (val->hasName()) {
							def.insert(val->getName());
						}
						// StoreInst *SI = dyn_cast<StoreInst>(I);
						// SI->print(outs()); outs() << "\n";
						break;
					}
				case Instruction::Load:
					{
						Value *val = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							StringRef str = val->getName();
							if (def.find(str) == def.end()) {
								use.insert(str);
							}
						}
						// LoadInst *LI = dyn_cast<LoadInst>(I);
						// LI->print(outs()); outs() << "\n";
						break;
					}
				case Instruction::Call:
					{
						CallInst *CI = dyn_cast<CallInst>(I);
						Function *f = CI->getCalledFunction();
						std::string fname = f->getName();
						// outs() << fname << " fnc\n";
						if (f != NULL && fname.compare("printf") == 0) {
							// outs() << "\ninside printf\n";
							print_block = dyn_cast<BasicBlock>(BB);
						}
						break;
					}
				default:
						break;
			}
			temp.in.insert(use.begin(),use.end());
		}
	}

	unsigned int in_size = 0;
	std::set<StringRef> *setptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		BlockData &block_data = bblocks.at(basic_block.getName());
		in_size = block_data.in.size();
		for (succ_iterator SI = succ_begin(&basic_block), E = succ_end(&basic_block); SI != E; ++SI) {
			setptr = &(bblocks.at(SI->getName()).in);
			block_data.out.insert(setptr->begin(),setptr->end());
		}
		block_data.in.insert(block_data.use.begin(), block_data.use.end());
		for (std::set<StringRef>::iterator begin=block_data.out.begin(), end=block_data.out.end(); begin!=end; ++begin) {
			if (block_data.def.find(*begin) == block_data.def.end()) {
				block_data.in.insert(*begin);
			}
		}
		if (block_data.in.size() > in_size) {
			worklist.push_back(&basic_block);
		}
	} while (!worklist.empty());

	if (print_block == NULL) {
		outs() << "\nnull!!! not able to find print basic block\n";
		return;
	}

	BlockData &print_block_data = bblocks.at(print_block->getName());
	std::set<StringRef> live_at_print(print_block_data.out.begin(), print_block_data.out.end());
	std::set<StringRef> def, use;
	std::map<Value*, std::set<StringRef> > track_data;
	bool after_call = false;

	for (BasicBlock::iterator I = print_block->begin(), E = print_block->end(); I != E; ++I) {
		switch (I->getOpcode()) {
				case Instruction::Store:
					{
						Value *val = dyn_cast<Value>(I->getOperand(1));
						if (val->hasName()) {
							def.insert(val->getName());
							std::map<Value*,std::set<StringRef> >::iterator it = track_data.find(dyn_cast<Value>(I->getOperand(0)));
							if (it != track_data.end()) {
								track_data.erase(it);
							}
						}
						break;
					}
				case Instruction::Load:
					{
						Value *val = NULL;
						if (after_call) {
							val = dyn_cast<Value>(I->getOperand(0));
							if (val->hasName()) {
								StringRef str = val->getName();
								if (def.find(str) == def.end()) {
									live_at_print.insert(str);
								}
							}
						} else {
							val = dyn_cast<Value>(I->getOperand(0));
							if (val->hasName()) {
								StringRef str = val->getName();
								std::set<StringRef> temp;
								temp.insert(str);
								track_data.insert(std::pair<Value*,std::set<StringRef> > (dyn_cast<Value>(I), temp));
							}
						}
						break;
					}
				case Instruction::Call:
					{
						if (!after_call) {
							CallInst *CI = dyn_cast<CallInst>(I);
							Function *f = CI->getCalledFunction();
							std::string fname = f->getName();
							if (f != NULL && fname.compare("printf") == 0) {
								after_call = true;
								std::map<Value*, std::set<StringRef> >::iterator itr;
								for (Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end(); it != end; ++it) {
									itr = track_data.find(dyn_cast<Value>(it));
									if (itr != track_data.end()) {
										live_at_print.insert(itr->second.begin(), itr->second.end());
									}
								}
								track_data.clear();
							}
						}
						break;
					}
				default:
					{
						if (!after_call) {
							std::set<StringRef> temp;
							std::map<Value*, std::set<StringRef> >::iterator itr;
							for (Instruction::value_op_iterator val=I->value_op_begin(), end=I->value_op_end(); val != end; ++val) {
								itr = track_data.find(dyn_cast<Value>(*val));
								if (itr != track_data.end()) {
									temp.insert(itr->second.begin(), itr->second.end());
									track_data.erase(itr);
								}
							}
							track_data.insert(std::pair<Value*,std::set<StringRef> >(dyn_cast<Value>(I), temp));
						}
						break;
					}
			}
	}

	for (std::set<StringRef>::iterator b=live_at_print.begin(), e=live_at_print.end(); b != e; ++b) {
		outs() << *b << " ";
	}
	outs()<< "\n";
}


// Register the pass.
char Liveness::ID = 0;
static RegisterPass<Liveness> X("liveness", "Liveness Pass");
