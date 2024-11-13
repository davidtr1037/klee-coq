#ifndef KLEE_STATE_TRANSLATION_H
#define KLEE_STATE_TRANSLATION_H

#include "ExecutionState.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <list>
#include <string>
#include <vector>

namespace klee {

class StateTranslator {

private:

  ref<CoqExpr> coqGlobalStoreAlias;

public:

  llvm::Module &m;

  ModuleTranslator *moduleTranslator;

  ExprTranslator *exprTranslator;

  StateTranslator(llvm::Module &m,
                  ModuleTranslator *moduleTranslator,
                  ExprTranslator *exprTranslator);

  void generateGlobalDefs(std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateState(ExecutionState &es, std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createInstCounter(ExecutionState &es);

  ref<CoqExpr> createInstCounter(llvm::Instruction *inst);

  ref<CoqExpr> createCommand(ExecutionState &es);

  ref<CoqExpr> createTrailingCommands(ExecutionState &es);

  ref<CoqExpr> createPrevBID(ExecutionState &es);

  ref<CoqExpr> createPrevBID(StackFrame &sf);

  ref<CoqExpr> createLocalStore(ExecutionState &es,
                                std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateRegisterUpdates(ExecutionState &es,
                                        std::list<RegisterUpdate> &updates,
                                        std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createStack(ExecutionState &es,
                           std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createFrame(ExecutionState &es,
                           unsigned inex,
                           std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createGlobalStore();

  ref<CoqExpr> createSymbolics(ExecutionState &es,
                               std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createPC(ExecutionState &es, std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createModule();

  std::string getICAliasName(uint64_t stepID);

  ref<CoqVariable> getICAlias(uint64_t stepID);

  std::string getCommandAliasName(uint64_t stepID);

  ref<CoqVariable> getCommandAlias(uint64_t stepID);

  std::string getCommandsAliasName(uint64_t stepID);

  ref<CoqVariable> getCommandsAlias(uint64_t stepID);

  std::string getPrevBIDAliasName(uint64_t stepID);

  ref<CoqVariable> getPrevBIDAlias(uint64_t stepID);

  std::string getLocalStoreAliasName(uint64_t stepID);

  ref<CoqVariable> getLocalStoreAlias(uint64_t stepID);

  std::string getStackAliasName(uint64_t stepID);

  ref<CoqVariable> getStackAlias(uint64_t stepID);

  std::string getSymbolicsAliasName(uint64_t stepID);

  ref<CoqVariable> getSymbolicsAlias(uint64_t stepID);

  std::string getPCAliasName(uint64_t stepID);

  ref<CoqVariable> getPCAlias(uint64_t stepID);

};

}

#endif
