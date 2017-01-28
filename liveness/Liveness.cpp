#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

class Liveness : public ModulePass {
	public:
		static char ID;
		Liveness() : ModulePass(ID) {
		}

		bool runOnModule(Module &M);
		void computeLiveness(Function &F);
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
	int count = 0;
	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		outs() << "Basic Block: " << ++count << "\n";
		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
			switch (I->getOpcode()) {
				case Instruction::Store:
					{
						StoreInst *SI = dyn_cast<StoreInst>(I);
						SI->print(outs()); outs() << "\n";
						break;
					}
				case Instruction::Load:
					{
						LoadInst *LI = dyn_cast<LoadInst>(I);
						LI->print(outs()); outs() << "\n";
						break;
					}
			}
		}
	}
}


// Register the pass.
char Liveness::ID = 0;
static RegisterPass<Liveness> X("liveness", "Liveness Pass");
