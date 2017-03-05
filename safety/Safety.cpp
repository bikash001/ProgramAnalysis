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
		void printSet(std::set<StringRef>&);
		void debug(std::string str);
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

void Safety::debug(std::string str) {
	outs() << str << "\n";
}

void Safety::printSet(std::set<StringRef> &set){
	for (std::set<StringRef>::iterator bg=set.begin(), en=set.end(); bg != en; ++bg) {
		outs() << *bg <<", ";
	}
	outs() << "\n";
}

void Safety::computeFunction(std::set<std::string> &locals, std::set<std::string> &globalsadd, std::set<std::string> &globalsrem, Function &F) {

	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	std::set<StringRef>::iterator itr, itrTop;
	std::set<StringRef> flocals, fglobals;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
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
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		Value *prev = NULL;
	
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::set<StringRef> &gen = block_data.gen;

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
							} else if (fop->hasName()) {
								if (locals.find(fop->getName().str()) == locals.end()) {
									gen.erase(name);
								} else {
									gen.insert(name);
								}
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

	BlockData &bdata = bblocks.at(last_block.getName());
	std::set<StringRef> &out = bdata.out;
	for (itrTop=out.begin(), itr=out.end(); itrTop != itr; ++itrTop) {
		if (flocals.find(*itrTop) == flocals.end()) {
			globalsadd.insert(itrTop->str());
		} else {
			locals.insert(itrTop->str());
		}
	}
	
	for (itrTop=fglobals.begin(), itr=fglobals.end(); itrTop != itr; ++itrTop) {
		if (globalsadd.find(*itrTop) == globalsadd.end()) {
			globalsrem.insert(itrTop->str());
		}
	}
}

void Safety::computeSafety(Function &F) {
	std::map<StringRef,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;
	BasicBlock *print_block = NULL;
	std::set<StringRef>::iterator itr, itrTop;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		bblocks.insert(std::pair<StringRef,BlockData>(BB->getName(),temp));
	}

	unsigned int out_size = 0;
	std::set<StringRef> *setptr, *dataptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		
		BlockData &block_data = bblocks.at(basic_block.getName());
		std::set<StringRef> &gen = block_data.gen;
		Value *prev = NULL;//, *lastLoad = NULL;
		// std::map<Value*, StringRef> argVals;
		out_size = block_data.out.size();

		pred_iterator PI = pred_begin(&basic_block), PE = pred_end(&basic_block);
		if (PE != PI) {
			BlockData &bdata = bblocks.at((*PI)->getName());
			setptr = &(bdata.out);
			block_data.gen.clear();
			block_data.gen.insert(setptr->begin(), setptr->end());
			++PI;
			for (; PI != PE; ++PI) {
				setptr = &(bblocks.at((*PI)->getName()).out);
				dataptr = &(block_data.gen);
				for (itrTop = dataptr->begin(), itr = dataptr->end(); itrTop != itr; ++itrTop) {
					if (setptr->find(*itrTop) == setptr->end()) {
						dataptr->erase(*itrTop);
					}
				}
			}
		}
		block_data.in.insert(block_data.gen.begin(), block_data.gen.end());

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
							// lastLoad = dyn_cast<Value>(I);
							// argVals.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),val->getName()));
						// } else if (val == lastLoad) {
							// argVals.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),argVals.at(lastLoad)));
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
						} else if (!f->isDeclaration()) {
							std::set<std::string> locals;
							std::set<std::string> globalsadd;
							std::set<std::string> globalsrem;


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
							//before passing argument, send points-to info
							Function::arg_iterator arg_bg = f->arg_begin();
							for (Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end(); it != end; ++it, ++arg_bg) {
								
								if (block_data.out.find(dyn_cast<Value>(it)->getName()) != block_data.out.end()) {
									locals.insert(arg_bg->getName().str());
								}
							}

							computeFunction(locals, globalsadd, globalsrem, *f);
							
							gen.insert(globalsadd.begin(), globalsadd.end());							
							for (std::set<std::string>::iterator jj=globalsrem.begin(), kk=globalsrem.end(); jj != kk; ++jj) {
								StringRef str = *jj;
								gen.erase(str);
							}
						}
							
						// argVals.clear();
						// lastLoad = NULL;
						prev = NULL;

						break;
					}
				default:
						// lastLoad = NULL;
						prev = NULL;
						break;
			}
		}

		// pred_iterator PI = pred_begin(&basic_block), PE = pred_end(&basic_block);
		// if (PE != PI) {
		// 	BlockData &bdata = bblocks.at((*PI)->getName());
		// 	setptr = &(bdata.out);
		// 	block_data.in.clear();
		// 	block_data.in.insert(setptr->begin(), setptr->end());
		// 	++PI;
		// 	for (; PI != PE; ++PI) {
		// 		setptr = &(bblocks.at((*PI)->getName()).out);
		// 		dataptr = &(block_data.in);
		// 		for (itrTop = dataptr->begin(), itr = dataptr->end(); itrTop != itr; ++itrTop) {
		// 			if (setptr->find(*itrTop) == setptr->end()) {
		// 				dataptr->erase(*itrTop);
		// 			}
		// 		}
		// 	}
		// }

		// block_data.out.insert(block_data.in.begin(),block_data.in.end());
		block_data.out.insert(block_data.gen.begin(), block_data.gen.end());
		
		// outs() << "Basic Block-----" << basic_block.getName() << "\n";
		// printSet(block_data.gen);
		// printSet(block_data.out);
		// outs() << "\n";

		if (block_data.out.size() != out_size) {
			for (succ_iterator SI=succ_begin(&basic_block), E=succ_end(&basic_block); SI != E; ++SI) {
				worklist.push_back(dyn_cast<BasicBlock>(*SI));
			}
		}
		// outs() << "itr-->\n";
	} while (!worklist.empty());
	
	std::map<Value*, StringRef> argData;
	Value *prev = NULL, *lastLoad = NULL;
	std::set<StringRef> &gen = bblocks.at(print_block->getName()).in;
	// outs() << "gen\n";
	// printSet(gen);
	BasicBlock &basic_block = *print_block;
	BlockData &block_data = bblocks.at(basic_block.getName());

	for (BasicBlock::iterator I = print_block->begin(), E = print_block->end(); I != E; ++I) {
		switch (I->getOpcode()) {
			case Instruction::Store:
				{
					// debug("store");
					Value *val = dyn_cast<Value>(I->getOperand(1));
					Value *fop = dyn_cast<Value>(I->getOperand(0));
					if (val->hasName()) {
						StringRef name = val->getName();
						itrTop = gen.find(name);
						if (fop->getValueID() == Value::ConstantPointerNullVal) {	//ptr = NULL
							// debug("null");
							gen.erase(name);
						} else if (prev != NULL) {	// ptr = ptr2
							StringRef pName = prev->getName();
							// outs() << pName << "\n";
							if (itrTop == gen.end() && gen.find(pName) != gen.end()) {	//not exist earlier
								// debug("1");
								gen.insert(name);
							} else if (gen.find(pName) == gen.end()) {	//if ptr2 not exist
								// debug("2");
								gen.erase(name);
							}
						} else {	// ptr = &x
							if (itrTop == gen.end()) {		//if ptr not present in gen, then null ptr
								// debug("3");
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
						// debug("4");
						lastLoad = dyn_cast<Value>(I);
						prev = val;
						argData.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),val->getName()));
					} else if (val == lastLoad) {
						argData.insert(std::pair<Value*, StringRef>(dyn_cast<Value>(I),argData.at(lastLoad)));
					}
					break;
				}
			case Instruction::Call:
				{
					// debug("call");
					CallInst *CI = dyn_cast<CallInst>(I);
					Function *f = CI->getCalledFunction();
					StringRef fname = "printf";
					if (f != NULL && fname.equals(f->getName())) {
						Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end();
						for (++it; it != end; ++it) {
							StringRef str = argData.at(dyn_cast<Value>(it));
							if (gen.find(str) != gen.end()) {
								outs() << "safe ";
							} else {
								outs() << "unsafe ";
							}
						}
					}  else if (!f->isDeclaration()) {
						std::set<std::string> locals;
						std::set<std::string> globalsadd;
						std::set<std::string> globalsrem;


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
						//before passing argument, send points-to info
						Function::arg_iterator arg_bg = f->arg_begin();
						for (Instruction::op_iterator it=CI->arg_begin(), end=CI->arg_end(); it != end; ++it, ++arg_bg) {
							
							if (block_data.out.find(dyn_cast<Value>(it)->getName()) != block_data.out.end()) {
								locals.insert(arg_bg->getName().str());
							}
						}

						computeFunction(locals, globalsadd, globalsrem, *f);
						
						gen.insert(globalsadd.begin(), globalsadd.end());							
						
						for (std::set<std::string>::iterator jj=globalsrem.begin(), kk=globalsrem.end(); jj != kk; ++jj) {
							StringRef str = *jj;
							gen.erase(str);
						}
					}
					lastLoad = NULL;
					prev = NULL;
					break;
				}
			default:
					prev = NULL;
					lastLoad = NULL;
					break;
		}
	}
	outs()<< "\n";
}


// Register the pass.
char Safety::ID = 0;
static RegisterPass<Safety> X("safety", "Safety Pass");
