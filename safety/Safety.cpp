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
	std::map<StringRef,std::set<StringRef> > gen, in, out;
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
	std::map<StringRef,std::set<StringRef> >::iterator itr, itrTop;

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

	unsigned int in_size = 0;
	std::map<StringRef,std::set<StringRef> > *mapptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::map<StringRef,std::set<StringRef> > &gen = block_data.gen;
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
							print_block = dyn_cast<BasicBlock>(BB);
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
		for (pred_iterator PI = pred_begin(&basic_block), E = pred_end(&basic_block); PI != E; ++PI) {
			mapptr = &(bblocks.at(PI->getName()).out);
			block_data.out.insert(setptr->begin(),setptr->end());
		}
		block_data.in.insert(block_data.use.begin(), block_data.use.end());
		for (std::set<StringRef>::iterator begin=block_data.out.begin(), end=block_data.out.end(); begin!=end; ++begin) {
			if (block_data.def.find(*begin) == block_data.def.end()) {
				block_data.in.insert(*begin);
			}
		}
		if (block_data.in.size() > out_size) {
			for (pred_iterator PI=pred_begin(&basic_block), E=pred_end(&basic_block); PI != E; ++PI) {
				worklist.push_back(dyn_cast<BasicBlock>(*PI));
			}
		}
	} while (!worklist.empty());
	
	// outs()<< "\n";
}


// Register the pass.
char Safety::ID = 0;
static RegisterPass<Safety> X("safety", "Safety Pass");
