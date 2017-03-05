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
	private:
		void computeFunction(std::set<std::string> &, std::set<std::string> &, std::set<std::string> &, Function &);
};

bool Safety::runOnModule(Module &M) {
	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
		if (!F->isDeclaration()) {
			StringRef fname = "main";
			if (fname.equals(F->getName())) {
				computeSafety(*F);
			}
		}
	}
	return false;
}

void Safety::computeFunction(std::set<std::string> &locals, std::set<std::string> &globalsadd, std::set<std::string> &globalsrem, Function &F) {
	
	// for (Function::arg_iterator it=F.arg_begin(), end=F.arg_end(); it != end; ++it) {
	// 	if (it->hasName()) {
	// 		outs() << it->getName() << ", ";
	// 	} else {
	// 		outs() << "noName, ";
	// 	}
	// }
	// outs() << "\n";
	// exit(0);
	// outs() << "function begin\n";
	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	std::set<StringRef>::iterator itr, itrTop;
	std::set<StringRef> flocals, fglobals;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		// outs() << "l 67\n";
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			// outs() << "l 72\n";
			switch (I->getOpcode()) {
				case Instruction::Alloca:
					{
						if (I->hasName()) {
							flocals.insert(I->getName());
						}
						break;
					}
				case Instruction::Store:
					{
						Value *val = dyn_cast<Value>(I->getOperand(1));
						if (val->hasName() && flocals.find(val->getName()) == flocals.end()) {
							fglobals.insert(val->getName());
						}
						break;
					}
				default:
						break;
			}
		}
	}

	BasicBlock &last_block = *(worklist.back());
	unsigned int out_size = 0;
	std::set<StringRef> *setptr, *dataptr;
	do {
		// outs() << "l 100\n";
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::set<StringRef> &gen = block_data.gen;
		Value *prev = NULL;

		for (BasicBlock::iterator I = basic_block.begin(), E = basic_block.end(); I != E; ++I) {
			// outs() << "l 109\n";
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
				// outs() << "l 160\n";
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
				// outs() << "l 175\n";
				worklist.push_back(dyn_cast<BasicBlock>(*SI));
			}
		}

	} while (!worklist.empty());

	BlockData &bdata = bblocks.at(last_block.getName());
	std::set<StringRef> &out = bdata.out;
	for (itrTop=out.begin(), itr=out.end(); itrTop != itr; ++itrTop) {
		// outs() << "l 186\n";
		if (flocals.find(*itrTop) == flocals.end()) {
			globalsadd.insert(itrTop->str());
		} else {
			locals.insert(itrTop->str());
		}
	}
	
	for (itrTop=fglobals.begin(), itr=fglobals.end(); itrTop != itr; ++itrTop) {
		// outs() << "l 195\n";
		if (globalsadd.find(*itrTop) == globalsadd.end()) {
			globalsrem.insert(itrTop->str());
		}
	}
	// outs() << "function end\n";
	// outs() << "size " << globalsadd.size() << ", " << globalsrem.size() << "\n";
}

void Safety::computeSafety(Function &F) {
	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	BasicBlock *print_block = NULL;
	std::set<StringRef>::iterator itr, itrTop;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		// outs() << "l 213\n";
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
	}

	unsigned int out_size = 0;
	std::set<StringRef> *setptr, *dataptr;
	do {
		// outs() << "l 220\n";
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::set<StringRef> &gen = block_data.gen;
		Value *prev = NULL, *lastLoad = NULL;
		std::map<Value*, StringRef> argVals;
	
		for (BasicBlock::iterator I = basic_block.begin(), E = basic_block.end(); I != E; ++I) {
			
			// outs() << "l 231\n";
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						// outs() << "l--------->344\n";
			
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
						// outs() << "l--------->366\n";
						prev = NULL;
						break;
					}
				case Instruction::Load:
					{
						// outs() << "l--------->372\n";
						Value *val = dyn_cast<Value>(I->getOperand(0));
						if (val->hasName()) {
							prev = val;
							lastLoad = dyn_cast<Value>(I);
							argVals.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),val->getName()));
						} else if (val == lastLoad) {
							argVals.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),argVals.at(lastLoad)));
						}
						// outs() << "l--------->381\n";
						break;
					}
				case Instruction::Call:
					{
						// outs() << "l--------->386\n";
						CallInst *CI = dyn_cast<CallInst>(I);
						Function *f = CI->getCalledFunction();
						StringRef fname = "printf";
						if (f != NULL && fname.equals(f->getName())) {
							print_block = &basic_block;
						} else if (!f->isDeclaration()) {
							std::set<std::string> locals;
							std::set<std::string> globalsadd;
							std::set<std::string> globalsrem;

							computeFunction(locals, globalsadd, globalsrem, *f);
							
							Function::arg_iterator arg_bg = f->arg_begin();

							for (Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end(); it != end; ++it, ++arg_bg) {
								// outs() << "l 293\n";
								std::string strref = arg_bg->getName().str() + ".addr";
								// outs() << "--> "<< strref << "\n";
								
								if (locals.find(strref) == locals.end()) {
									gen.erase(argVals.at(*it));
								} else {
									gen.insert(argVals.at(*it));
								}
							}
							// outs() << " inside for loop end\n";
							gen.insert(globalsadd.begin(), globalsadd.end());							
							// outs() << "first end\n";
							for (std::set<std::string>::iterator jj=globalsrem.begin(), kk=globalsrem.end(); jj != kk; ++jj) {
								StringRef str = *jj;
								gen.erase(str);
							}
							// gen.erase(globalsrem.begin(), globalsrem.end());							
							// outs() << "second end\n";
							// locals.clear();
							// outs() << "local cler\n";
							// globalsrem.clear();
							// outs() << "rem cler\n";
							// globalsadd.clear();
							// outs() << "add clr\n";
							// outs() << f->getName() << "\n";
						}
						// outs() << "argval end\n";
							
						argVals.clear();
						// outs() << "argval clear\n";
						lastLoad = NULL;
						prev = NULL;

						// outs() << "l--------->429\n";
						break;
					}
				default:
						lastLoad = NULL;
						prev = NULL;
						break;
			}
			// outs() << "for loop end\n";
		}

		out_size = block_data.out.size();
		// outs() << "out size "<< out_size << "\n";
		pred_iterator PI = pred_begin(&basic_block), PE = pred_end(&basic_block);
		if (PE != PI) {
			BlockData &bdata = bblocks.at((*PI)->getName());
			setptr = &(bdata.out);
			block_data.in.clear();
			block_data.in.insert(setptr->begin(), setptr->end());
			++PI;

			for (; PI != PE; ++PI) {
				// outs() << "l 345\n";
				setptr = &(bblocks.at((*PI)->getName()).out);
				dataptr = &(block_data.in);
				for (itrTop = dataptr->begin(), itr = dataptr->end(); itrTop != itr; ++itrTop) {
					if (setptr->find(*itrTop) == setptr->end()) {
						dataptr->erase(*itrTop);
					}
				}
			}
		}

		// outs() << "pt 1-->\n";
		block_data.out.insert(block_data.in.begin(),block_data.in.end());
		block_data.out.insert(block_data.gen.begin(), block_data.gen.end());
		
		// outs() << "block size "<< block_data.out.size() << "\n";
		if (block_data.out.size() != out_size) {
			for (succ_iterator SI=succ_begin(&basic_block), E=succ_end(&basic_block); SI != E; ++SI) {
				// outs() << "l 363\n";
				worklist.push_back(dyn_cast<BasicBlock>(*SI));
			}
		}
		// outs() << "loop running-->\n";
	} while (!worklist.empty());
	
	std::map<Value*, StringRef> argData;
	Value *prev = NULL;
	std::set<StringRef> &out = bblocks.at(print_block->getName()).out;
	for (BasicBlock::iterator I = print_block->begin(), E = print_block->end(); I != E; ++I) {
		// outs() << "l 375\n";	
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
							// outs() << "l 396\n";	
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
