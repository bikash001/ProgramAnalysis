#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Argument.h"
#include <set>
#include <string>

using namespace llvm;

class Liveness : public ModulePass {
	public:
		static char ID;
		Liveness() : ModulePass(ID) {
		}

		bool runOnModule(Module &M);
		void computeLiveness(Function &F);
	private:
		std::set<std::string> vars;
		std::set<std::string> use;
		std::set<std::string> def;
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
	vars.clear();
	for (Function::arg_iterator beg = F.arg_begin(), end = F.arg_end(); beg != end; ++beg) {
		if (beg->hasName()) {
			vars.insert(beg->getName());
		}
	}
	// int count = 0;
	// Value *old = NULL;
	// int prev = 0;
	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		def.clear();
		use.clear();
		outs() << BB->getName() << ":\n";
		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			// outs() << "inst:" << ++count << " ";
			// for (Instruction::value_op_iterator it=I->value_op_begin(), end=I->value_op_end(); it != end; ++it) {
			// 	if (it->hasName()) {
					
			// 	} else {
			// 		outs() << " false | ";
			// 	}
			// 	it->printAsOperand(outs()); outs() << " | ";
			// 	outs() << it->getName() << " | ";
			// 	it->print(outs());
			// 	outs() << " ";
			// 	vars.insert(it->getName());
			// }
			
			// if (I->getNumOperands() == 3 && prev == 2) {
			// 	outs() << "----"<< old->getName() << "---\n";
			// 	for (Instruction::value_op_iterator it=I->value_op_begin(), end=I->value_op_end(); it != end; ++it) {
			// 		if (it->hasName()) {
			// 			outs() << it->getName() << "->";
			// 			if ( old && dyn_cast<Value>(*it) == old) {
			// 				outs() << "yes, ";
			// 			} else {
			// 				outs() << "no, ";
			// 			}
			// 		}
			// 	}
			// 	outs() << "\n------------\n";
			// }
			// prev = I->getNumOperands();
			// old = dyn_cast<Value>(I);
			// outs() << I->getName() << "\n";
			
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
							use.insert(val->getName());
						}
						// LoadInst *LI = dyn_cast<LoadInst>(I);
						// LI->print(outs()); outs() << "\n";
						break;
					}
				case Instruction::Alloca:
					{
						// if (I->hasName())
						// 	vals.insert(I->name());
						// outs() << I->getName() << ", " << I->getNumOperands() << "\n";
						break;
					}
			}
		}
		outs() << "def-----\n";
		for (std::set<std::string>::iterator b=def.begin(), e=def.end(); b != e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\nuse-------\n";
		for (std::set<std::string>::iterator b=use.begin(), e=use.end(); b != e; ++b) {
			outs() << *b << ", ";
		}
		outs() << "\n\n";
	}
	// std::set<std::string>::iterator b, e;
	// for (b=vars.begin(), e=vars.end(); b != e; ++b) {
	// 	outs() << *b << " ";
	// }
	// outs()<< "\n";
}


// Register the pass.
char Liveness::ID = 0;
static RegisterPass<Liveness> X("liveness", "Liveness Pass");
