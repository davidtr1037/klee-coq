#include "Passes.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/BasicBlock.h>

using namespace llvm;

char klee::UndefCleanerPass::ID = 0;

bool klee::UndefCleanerPass::runOnFunction(Function &f) {
  bool changed = false;
  for (BasicBlock &bb : f) {
    for (Instruction &inst : bb) {
      for (unsigned i = 0; i < inst.getNumOperands(); ++i) {
        Value *operand = inst.getOperand(i);
        if (isa<UndefValue>(operand)) {
          Value *v = Constant::getNullValue(operand->getType());
          inst.setOperand(i, v);
          changed = true;
        }
      }
    }
  }

  return changed;
}
