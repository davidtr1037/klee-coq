#ifndef KLEE_MODULEASSUMPTIONS_H
#define KLEE_MODULEASSUMPTIONS_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

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

  ref<CoqExpr> generateProof();

  ref<CoqExpr> getLemmaForModule();

  ref<CoqTactic> getTacticForModule();

  ref<CoqLemma> getLemmaForFunction(llvm::Function &f);

  ref<CoqTactic> getTacticForFunction(llvm::Function &f);

  ref<CoqLemma> getLemmaForBasicBlock(llvm::BasicBlock &bb);

  ref<CoqTactic> getTacticForBasicBlock(llvm::BasicBlock &bb);

  ref<CoqLemma> getLemmaForInst(llvm::Instruction &inst);

  ref<CoqTactic> getTacticForInst(llvm::Instruction &inst);

  ~ModuleSupport();
};

}

#endif
