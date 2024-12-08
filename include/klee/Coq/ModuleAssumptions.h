#ifndef KLEE_MODULEASSUMPTIONS_H
#define KLEE_MODULEASSUMPTIONS_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"

#include <vector>

namespace klee {

class ModuleSupport {

public:

  llvm::Module &m;

  ModuleTranslator &moduleTranslator;

  std::vector<ref<CoqLemma>> functionLemmas;

  std::vector<ref<CoqLemma>> bbLemmas;

  std::vector<ref<CoqLemma>> instLemmas;

  ModuleSupport(llvm::Module &m, ModuleTranslator &moduleTranslator);

  ref<CoqLemma> generateProof();

  ref<CoqLemma> getLemmaForModule();

  ref<CoqTactic> getTacticForModule();

  ref<CoqLemma> getLemmaForFunction(llvm::Function &f);

  ref<CoqTactic> getTacticForFunction(llvm::Function &f);

  ref<CoqLemma> getLemmaForBasicBlock(llvm::BasicBlock &bb);

  ref<CoqTactic> getTacticForBasicBlock(llvm::BasicBlock &bb);

  ref<CoqLemma> getLemmaForInst(llvm::Instruction &inst);

  ref<CoqTactic> getTacticForInst(llvm::Instruction &inst);

  ref<CoqTactic> getTacticForAssignment(llvm::Instruction &inst);

  ref<CoqTactic> getTacticForBinaryOperatorExpr(llvm::BinaryOperator *inst);

  ref<CoqTactic> getTacticForDivOperator(llvm::BinaryOperator *inst);

  ref<CoqTactic> getTacticForShiftOperator(llvm::BinaryOperator *inst);

  ref<CoqTactic> getTacticForCmpExpr(llvm::CmpInst *inst);

  ref<CoqTactic> getTacticForCastExpr(llvm::CastInst *inst);

  ref<CoqTactic> getTacticForBranchInst(llvm::BranchInst *inst);

  ref<CoqTactic> getTacticForPHINode(llvm::PHINode *inst);

  ref<CoqTactic> getTacticForCallInst(llvm::CallInst *inst);

  ref<CoqTactic> getTacticForReturnInst(llvm::ReturnInst *inst);

  ref<CoqTactic> getTacticForUnreachableInst(llvm::UnreachableInst *inst);

  ref<CoqTactic> getTacticForValue(llvm::Value *value);

  bool isDivOperator(llvm::BinaryOperator *inst);

  bool isShiftOperator(llvm::BinaryOperator *inst);

  ~ModuleSupport();
};

}

#endif
