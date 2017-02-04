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
	std::set<std::string> use, def, in, out;
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
	std::map<std::string,BlockData> bblocks;
	std::deque<BasicBlock*> worklist;

	for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		worklist.push_back(dyn_cast<BasicBlock>(BB));
		BlockData temp;
		bblocks.insert(std::pair<std::string,BlockData>(BB->getName(),temp));
		std::set<std::string> &def = temp.def;
		std::set<std::string> &use = temp.use;
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
							std::string str = val->getName();
							if (def.find(str) == def.end())
								use.insert(str);
						}
						// LoadInst *LI = dyn_cast<LoadInst>(I);
						// LI->print(outs()); outs() << "\n";
						break;
					}
				default:
						break;
			}
			temp.in.insert(use.begin(),use.end());
		}
	}

	unsigned int in_size = 0;
	std::string child;
	std::set<std::string> *setptr;
	do {
		BasicBlock &basic_block = *(worklist.front());
		worklist.pop_front();
		BlockData &block_data = bblocks[basic_block.getName()];
		in_size = block_data.in.size();
		for (succ_iterator SI = succ_begin(&basic_block), E = succ_end(&basic_block); SI != E; ++SI) {
			setptr = &(bblocks[SI->getName()].in);
			block_data.out.insert(setptr->begin(),setptr->end());
		}
		block_data.in.insert(block_data.use.begin(), block_data.use.end());
		for (std::set<std::string>::iterator begin=block_data.out.begin(), end=block_data.out.end(); begin!=end; ++begin) {
			if (block_data.def.find(*begin) == block_data.def.end()) {
				block_data.in.insert(*begin);
			}
		}
		if (block_data.in.size() > in_size) {
			worklist.push_back(&basic_block);
		}
	} while (!worklist.empty());

	// for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
		
	// }
	
	// std::set<std::string>::iterator b, e;
	// for (b=vars.begin(), e=vars.end(); b != e; ++b) {
	// 	outs() << *b << " ";
	// }
	// outs()<< "\n";
}


// Register the pass.
char Liveness::ID = 0;
static RegisterPass<Liveness> X("liveness", "Liveness Pass");
