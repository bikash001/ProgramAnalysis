#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm-c/Core.h"
#include "llvm/IR/Constant.h"
#include <set>
#include <map>
#include <queue>
#include "llvm/IR/CFG.h"

using namespace llvm;

class BlockData
{
public:
	std::set<StringRef> gen, in, out;
	BlockData() {}
	~BlockData() {}
	
};

class Safety : public ModulePass {
	public:
		static char ID;
		Safety() : ModulePass(ID) {
		}

		bool runOnModule(Module &M);
		void computeSafety(Function &F);
};

bool Safety::runOnModule(Module &M) {
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
		if (!F->isDeclaration()) {
			computeSafety(*F);
		}
	}
	return false;
}

void Safety::computeSafety(Function &F) {
	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	BasicBlock *print_block = NULL;
	std::set<StringRef>::iterator itr, itrTop;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		/*std::map<StringRef,std::set<StringRef> > &gen = temp.gen;
		Value *prev = NULL;

		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						// I->print(outs());
						// outs() << "\n";
						// Instruction::value_op_iterator bg, en;
						// bg = I->value_op_begin();
						// en = I->value_op_end();
						// int i=0;
						// Constant *con;
						// for(; bg!=en; bg++){
						// 	if (bg->getValueID() == Value::ConstantPointerNullVal)
						// 		outs() << " || ";
						// 	outs() << i++ << "= " << bg->getName() << ", ";
						// }
						// outs() << "\n\n";
						Value *val = dyn_cast<Value>(I->getOperand(1));
						Value *fop = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							StringRef name = val->getName();
							itrTop = gen.find(name);
							if (fop->getValueID() == Value::ConstantPointerNullVal) {	//ptr = NULL
								gen.erase(name);
							} else if (prev != NULL) {	// ptr = ptr2
								StringRef pName = prev->getName();
								if (itrTop == gen.end()) {	//not exist earlier
									itr = gen.find(pName);
									if (itr != gen.end()) {	//if ptr2 data exist
										std::set<StringRef> mset(itr->second);
										gen.insert(std::pair<StringRef,std::set<StringRef> >(name, mset));
									}
								} else {
									std::set<StringRef> &mset = itrTop->second;
									mset.clear();
									itr = gen.find(pName);
									if (itr != gen.end()) {	//if ptr2 exist
										mset.insert(itr->second.begin(), itr->second.end());
									} else {	//ptr2 not exist so delete data
										gen.erase(name);
									}
								}
							} else {	// ptr = &x
								if (itrTop == gen.end()) {		//if ptr not present in gen, then null ptr
									std::set<StringRef> mset;	//if set empty, then malloc data
									gen.insert(std::pair<StringRef,std::set<StringRef> >(name, mset));
								} else {
									std::set<StringRef> &mset = itrTop->second;
									mset.clear();
								}
							}
						}
						prev = NULL;
						break;
					}
				case Instruction::Load:
					{
						// I->print(outs());
						// outs() << "\n";
						// Instruction::value_op_iterator bg, en;
						// bg = I->value_op_begin();
						// en = I->value_op_end();
						// int i=0;
						// for(; bg!=en; bg++){
						// 	outs() << i++ << "= " << bg->getName() << ", ";
						// }
						// outs() << "\n\n";
						Value *val = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							prev = val;
						}
						break;
					}
				case Instruction::Call:
					{
						// I->print(outs());
						// outs() << "\n";
						// Instruction::value_op_iterator bg, en;
						// bg = I->value_op_begin();
						// en = I->value_op_end();
						// int i=0;
						// for(; bg!=en; bg++){
						// 	outs() << i++ << "= " << bg->getName() << ", ";
						// }
						// outs() << "\n\n";
						CallInst *CI = dyn_cast<CallInst>(I);
						Function *f = CI->getCalledFunction();
						StringRef fname = "printf";
						if (f != NULL && fname.equals(f->getName())) {
							print_block = dyn_cast<BasicBlock>(BB);
						}
						prev = NULL;
						break;
					}
				// case Instruction::BitCast:
				// 	{
				// 		I->print(outs());
				// 		outs() << "\n";
				// 		Instruction::value_op_iterator bg, en;
				// 		bg = I->value_op_begin();
				// 		en = I->value_op_end();
				// 		int i=0;
				// 		for(; bg!=en; bg++){
				// 			outs() << i++ << "= " << bg->getName() << ", ";
				// 		}
				// 		outs() << "\n\n";
				// 		break;
				// 	}
				default:
						prev = NULL;
						break;
			}
		}*/
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
	}

	unsigned int out_size = 0;
	std::set<StringRef> *setptr, *dataptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::set<StringRef> &gen = block_data.gen;
		Value *prev = NULL;

		for (BasicBlock::iterator I = basic_block.begin(), E = basic_block.end(); I != E; ++I) {
			
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						Value *val = dyn_cast<Value>(I->getOperand(1));
						Value *fop = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							StringRef name = val->getName();
							itrTop = gen.find(name);
							if (fop->getValueID() == Value::ConstantPointerNullVal) {	//ptr = NULL
								gen.erase(name);
							} else if (prev != NULL) {	// ptr = ptr2
								StringRef pName = prev->getName();
								if (itrTop == gen.end() && gen.find(pName) != gen.end()) {	//not exist earlier
									gen.insert(name);
								} else if (gen.find(pName) == gen.end()) {	//if ptr2 not exist
									gen.erase(name);
								}
							} else {	// ptr = &x
								if (itrTop == gen.end()) {		//if ptr not present in gen, then null ptr
									gen.insert(name);
								}
							}
						}
						prev = NULL;
						break;
					}
				case Instruction::Load:
					{
						Value *val = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							prev = val;
						}
						break;
					}
				case Instruction::Call:
					{
						CallInst *CI = dyn_cast<CallInst>(I);
						Function *f = CI->getCalledFunction();
						StringRef fname = "printf";
						if (f != NULL && fname.equals(f->getName())) {
							print_block = &basic_block;
						} 
						prev = NULL;
						break;
					}
				default:
						prev = NULL;
						break;
			}
		}

		out_size = block_data.out.size();
		pred_iterator PI = pred_begin(&basic_block), PE = pred_end(&basic_block);
		if (PE != PI) {
			BlockData &bdata = bblocks.at((*PI)->getName());
			setptr = &(bdata.out);
			block_data.in.clear();
			block_data.in.insert(setptr->begin(), setptr->end());
			++PI;

			for (; PI != PE; ++PI) {
				setptr = &(bblocks.at((*PI)->getName()).out);
				dataptr = &(block_data.in);
				for (itrTop = dataptr->begin(), itr = dataptr->end(); itrTop != itr; ++itrTop) {
					if (setptr->find(*itrTop) == setptr->end()) {
						dataptr->erase(*itrTop);
					}
				}
			}
		}
		block_data.out.insert(block_data.in.begin(),block_data.in.end());
		block_data.out.insert(block_data.gen.begin(), block_data.gen.end());
		
		if (block_data.out.size() != out_size) {
			for (succ_iterator SI=succ_begin(&basic_block), E=succ_end(&basic_block); SI != E; ++SI) {
				worklist.push_back(dyn_cast<BasicBlock>(*SI));
			}
		}
	} while (!worklist.empty());
	
	std::map<Value*, StringRef> argData;
	Value *prev = NULL;

	std::set<StringRef> &out = bblocks.at(print_block->getName()).out;
	for (BasicBlock::iterator I = print_block->begin(), E = print_block->end(); I != E; ++I) {
			
		switch (I->getOpcode()) {
			case Instruction::Load:
				{
					Value *val = dyn_cast<Value>(I->getOperand(0));
					if (val->hasName()) {
						prev = dyn_cast<Value>(I);
						argData.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),val->getName()));
					} else if (val == prev) {
						argData.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),argData.at(prev)));
					}
					break;
				}
			case Instruction::Call:
				{
					CallInst *CI = dyn_cast<CallInst>(I);
					Function *f = CI->getCalledFunction();
					StringRef fname = "printf";
					if (f != NULL && fname.equals(f->getName())) {
						Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end();
						for (++it; it != end; ++it) {
							StringRef str = argData.at(dyn_cast<Value>(it));
							if (out.find(str) != out.end()) {
								outs() << "safe ";
							} else {
								outs() << "unsafe ";
							}
						}
					}
					break;
				}
			default:
					break;
		}
	}
	outs()<< "\n";
}


// Register the pass.
char Safety::ID = 0;
static RegisterPass<Safety> X("safety", "Safety Pass");
