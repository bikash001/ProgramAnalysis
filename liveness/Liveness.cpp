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

class BlockData
{
public:
	std::set<StringRef> use, def, in, out;
	BlockData() {}
	~BlockData() {}
	
};

class Liveness : public ModulePass {
	public:
		static char ID;
		Liveness() : ModulePass(ID) {
		}

		bool runOnModule(Module &M);
		void computeLiveness(Function &F);
		void print_sets(const std::map<StringRef,BlockData> &);
};


void Liveness::print_sets(const std::map<StringRef,BlockData> &map) {
	std::map<StringRef,BlockData>::const_iterator it = map.begin(), end = map.end();
	for (; it != end; ++it) {
		outs() << "---------" << it->first << "-----------\n";
		const BlockData &bd = it->second;
		outs() << "USE\n";
		for (std::set<StringRef>::const_iterator b=bd.use.begin(), e=bd.use.end(); b!=e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\nDEF\n";
		for (std::set<StringRef>::const_iterator b=bd.def.begin(), e=bd.def.end(); b!=e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\nIN\n";
		for (std::set<StringRef>::const_iterator b=bd.in.begin(), e=bd.in.end(); b!=e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\nOUT\n";
		for (std::set<StringRef>::const_iterator b=bd.out.begin(), e=bd.out.end(); b!=e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\nxxxxxxxxxxxxxxxxxxxxxxxxxxx\n";
	}
}

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
		// outs() << "basicblock: " << BB->getName() << "\n";
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		std::set<StringRef> &def = temp.def;
		std::set<StringRef> &use = temp.use;

		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						Value *val = dyn_cast<Value>(I->getOperand(1));
						if (val->hasName()) {
							def.insert(val->getName());
							// outs() << "def: " << val->getName() << "\n";
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
								// outs() << "use: " << val->getName() << "\n";
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
		}
		// outs() << "def size: " << temp.def.size() << "\n";
		temp.in.insert(use.begin(),use.end());
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
		// outs() << "in def size: " << bblocks.at(BB->getName()).def.size() << "\n";
		// print_sets(bblocks.at(BB->getName()));
		// outs() << temp.in.size() << ", " << temp.def.size() << ", " << temp.use.size() << "\n";
		// std::map<Value*, 
	}

	// outs() << "initialization\n\n";
	// print_sets(bblocks);
	
	unsigned int in_size = 0;
	std::set<StringRef> *setptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		BlockData &block_data = bblocks.at(basic_block.getName());
		in_size = block_data.in.size();
		// int count = 0;
		for (succ_iterator SI = succ_begin(&basic_block), E = succ_end(&basic_block); SI != E; ++SI) {
			// count++;
			setptr = &(bblocks.at(SI->getName()).in);
			block_data.out.insert(setptr->begin(),setptr->end());
		}
		// outs() << count << ", " << in_size << "\n";
		block_data.in.insert(block_data.use.begin(), block_data.use.end());
		for (std::set<StringRef>::iterator begin=block_data.out.begin(), end=block_data.out.end(); begin!=end; ++begin) {
			if (block_data.def.find(*begin) == block_data.def.end()) {
				block_data.in.insert(*begin);
			}
		}
		// outs() << block_data.in.size() << "\n";
		if (block_data.in.size() > in_size) {
			// outs() << "inside\n";
			worklist.push_back(&basic_block);
		}
	} while (!worklist.empty());

	// outs() << "\n\nafter algo\n\n";
	// print_sets(bblocks);

	if (print_block == NULL) {
		outs() << "\nnull!!! not able to find print basic block\n";
		return;
	}

	BlockData &print_block_data = bblocks.at(print_block->getName());
	// std::set<StringRef> live_at_print(print_block_data.out.begin(), print_block_data.out.end());
	std::set<StringRef> live_at_print;
	std::set<StringRef> def;
	std::map<Value*, std::set<StringRef> > track_data;
	bool after_call = false;

	for (BasicBlock::iterator I = print_block->begin(), E = print_block->end(); I != E; ++I) {
		switch (I->getOpcode()) {
				case Instruction::Store:
					{
						Value *val = NULL;
						if (after_call) {
							val = dyn_cast<Value>(I->getOperand(1));
							if (val->hasName()) {
								def.insert(val->getName());
								std::map<Value*,std::set<StringRef> >::iterator it = track_data.find(dyn_cast<Value>(I->getOperand(0)));
								if (it != track_data.end()) {
									track_data.erase(it);
								}
								// std::set<StringRef>::iterator elem = live_at_print.find(val->getName());
								// if (elem != live_at_print.end()) {
								// 	live_at_print.erase(elem);
								// }
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

	for (std::set<StringRef>::iterator begin=print_block_data.out.begin(), end=print_block_data.out.end(); begin!=end; ++begin) {
		if (def.find(*begin) == def.end()) {
			live_at_print.insert(*begin);
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
