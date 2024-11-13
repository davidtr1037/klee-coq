#include "StateTranslation.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"
#include "klee/Module/KModule.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/Cell.h"

#include <string>
#include <sstream>

using namespace std;
using namespace llvm;
using namespace klee;

cl::opt<bool> klee::DecomposeState(
  "decompose-state",
  cl::init(false),
  cl::desc("")
);

cl::opt<bool> CachePCExpr(
  "cache-pc-expr",
  cl::init(false),
  cl::desc("")
);

cl::opt<bool> CacheRegisterExpr(
  "cache-register-expr",
  cl::init(false),
  cl::desc("")
);

cl::opt<bool> CacheStackExpr(
  "cache-stack-expr",
  cl::init(false),
  cl::desc("")
);

cl::opt<bool> klee::CacheSymNames(
  "cache-sym-names",
  cl::init(false),
  cl::desc("")
);

StateTranslator::StateTranslator(Module &m,
                                 ModuleTranslator *moduleTranslator,
                                 ExprTranslator *exprTranslator) :
  m(m), moduleTranslator(moduleTranslator), exprTranslator(exprTranslator) {

}

void StateTranslator::generateGlobalDefs(vector<ref<CoqExpr>> &defs) {
  vector<ref<CoqExpr>> requiredDefs;

  /* TODO: add a general mechanism for aliasing */
  string globalStoreAlias = "gs";
  ref<CoqExpr> coqGlobalStoreDef = new CoqDefinition(
    globalStoreAlias,
    "smt_store",
    {new CoqVariable("empty_smt_store")}
  );
  defs.push_back(coqGlobalStoreDef);
  coqGlobalStoreAlias = new CoqVariable(globalStoreAlias);
}

klee::ref<CoqExpr> StateTranslator::translateState(ExecutionState &es,
                                                   vector<ref<CoqExpr>> &defs) {
  if (!DecomposeState) {
    return new CoqApplication(
      new CoqVariable("mk_sym_state"),
      {
        createInstCounter(es),
        createCommand(es),
        createTrailingCommands(es),
        createPrevBID(es),
        createLocalStore(es, defs),
        createStack(es, defs),
        createGlobalStore(),
        createSymbolics(es, defs),
        createPC(es, defs),
        createModule(),
      }
    );
  }

  defs.push_back(
    new CoqDefinition(
      getICAliasName(es.stepID),
      "inst_counter",
      createInstCounter(es)
   )
  );
  defs.push_back(
    new CoqDefinition(
      getCommandAliasName(es.stepID),
      "llvm_cmd",
      createCommand(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getCommandsAliasName(es.stepID),
      "list llvm_cmd",
      createTrailingCommands(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getPrevBIDAliasName(es.stepID),
      "option block_id",
      createPrevBID(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getLocalStoreAliasName(es.stepID),
      "smt_store",
      createLocalStore(es, defs)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getStackAliasName(es.stepID),
      "list sym_frame",
      createStack(es, defs)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getSymbolicsAliasName(es.stepID),
      "list string",
      createSymbolics(es, defs)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getPCAliasName(es.stepID),
      "smt_ast_bool",
      createPC(es, defs)
    )
  );

  return new CoqApplication(
    new CoqVariable("mk_sym_state"),
    {
      getICAlias(es.stepID),
      getCommandAlias(es.stepID),
      getCommandsAlias(es.stepID),
      getPrevBIDAlias(es.stepID),
      getLocalStoreAlias(es.stepID),
      getStackAlias(es.stepID),
      createGlobalStore(),
      getSymbolicsAlias(es.stepID),
      getPCAlias(es.stepID),
      createModule(),
    }
  );
}

klee::ref<CoqExpr> StateTranslator::createInstCounter(ExecutionState &es) {
  return createInstCounter(es.prevPC->inst);
}

klee::ref<CoqExpr> StateTranslator::createInstCounter(Instruction *inst) {
  BasicBlock *bb = inst->getParent();
  Function *f = bb->getParent();

  return new CoqApplication(
    new CoqVariable("mk_inst_counter"),
    {
      moduleTranslator->createName(f->getName().str()),
      moduleTranslator->createName(bb->getName().str()),
      new CoqInteger(moduleTranslator->getInstID(inst)),
    }
  );
}

klee::ref<CoqExpr> StateTranslator::createCommand(ExecutionState &es) {
  return moduleTranslator->translateInstCached(*es.prevPC->inst);
}

klee::ref<CoqExpr> StateTranslator::createTrailingCommands(ExecutionState &es) {
  BasicBlock *bb = es.prevPC->inst->getParent();

  vector<ref<CoqExpr>> coqInsts;

  /* TODO: use the pc/prevPC iterators */
  bool found = false;
  for (Instruction &inst : *bb) {
    if (found && moduleTranslator->isSupportedInst(inst)) {
      ref<CoqExpr> e = moduleTranslator->translateInstCached(inst);
      coqInsts.push_back(e);
    }
    if (&inst == es.prevPC->inst) {
      found = true;
    }
  }

  return new CoqList(coqInsts);
}

klee::ref<CoqExpr> StateTranslator::createPrevBID(ExecutionState &es) {
  return createPrevBID(es.stack.back());
}

klee::ref<CoqExpr> StateTranslator::createPrevBID(StackFrame &sf) {
  if (sf.incomingBB) {
    return createSome(moduleTranslator->createName(sf.incomingBB->getName().str()));
  } else {
    return createNone();
  }
}

klee::ref<CoqExpr> StateTranslator::createLocalStore(ExecutionState &es,
                                                     vector<ref<CoqExpr>> &defs) {
  return translateRegisterUpdates(es, es.stack.back().updates, defs);
}

klee::ref<CoqExpr> StateTranslator::translateRegisterUpdates(ExecutionState &es,
                                                             list<RegisterUpdate> &updates,
                                                             vector<ref<CoqExpr>> &defs) {
  ostringstream output;

  output << "(";
  for (auto i = updates.rbegin(); i != updates.rend(); i++) {
    RegisterUpdate &ru = *i;
    if (ru.value.isNull()) {
      continue;
    }

    ref<CoqExpr> coqName = moduleTranslator->createName(ru.name);
    ref<CoqExpr> coqExpr;
    if (CacheRegisterExpr) {
      coqExpr = exprTranslator->translateAsSMTExpr(ru.value, &es.arrayTranslation, true, true, defs);
    } else {
      coqExpr = exprTranslator->translateAsSMTExpr(ru.value, &es.arrayTranslation);
    }
    assert(coqName && coqExpr);
    output << coqName->dump() << " !-> " << "Some (" << coqExpr->dump() << "); ";
  }

  output << "empty_smt_store)";
  return new CoqVariable(output.str());
}

/* TODO: avoid reversed iteration? */
klee::ref<CoqExpr> StateTranslator::createStack(ExecutionState &es,
                                                vector<ref<CoqExpr>> &defs) {
  vector<ref<CoqExpr>> frames;

  ref<CoqExpr> tail = nullptr;

  for (int i = es.stack.size() - 2; i >= 0; i--) {
    StackFrame &sf = es.stack[i];
    if (sf.alias.isNull()) {
      ref<CoqExpr> frame = createFrame(es, i, defs);
      frames.push_back(frame);
    } else {
      tail = sf.alias;
      break;
    }
  }

  ref<CoqExpr> stack;
  if (tail.isNull()) {
    stack = new CoqList(frames);
  } else {
    stack = tail;
    for (auto i = frames.rbegin(); i != frames.rend(); i++) {
      ref<CoqExpr> frame = *i;
      stack = new CoqListCons(frame, stack);
    }
  }

  if (CacheStackExpr && es.stack.size() >= 2) {
    StackFrame &sf = es.stack[es.stack.size() - 2];
    if (sf.alias.isNull()) {
      string aliasName = "sf_" + to_string(es.stepID);
      sf.alias = new CoqVariable(aliasName);
      ref<CoqExpr> def = new CoqDefinition(
        aliasName,
        "list sym_frame",
        stack
      );
      defs.push_back(def);
    }
    return sf.alias;
  }

  return stack;
}

klee::ref<CoqExpr> StateTranslator::createFrame(ExecutionState &es,
                                                unsigned index,
                                                vector<ref<CoqExpr>> &defs) {
  assert(es.stack.size() != 0 && index < es.stack.size() - 1);
  StackFrame &sf = es.stack[index];
  StackFrame &next_sf = es.stack[index + 1];

  KInstruction *ki = next_sf.caller;
  assert(ki);
  CallInst *callInst = dyn_cast<CallInst>(ki->inst);
  assert(callInst);
  ref<CoqExpr> v;
  if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
    v = createNone();
  } else {
    v = createSome(moduleTranslator->createName(callInst->getName().str()));
  }

  Instruction *next = callInst->getNextNode();
  assert(next);

  return new CoqApplication(
    new CoqVariable("Sym_Frame"),
    {
      translateRegisterUpdates(es, sf.updates, defs),
      createInstCounter(next),
      createPrevBID(sf),
      v,
    }
  );
}

klee::ref<CoqExpr> StateTranslator::createGlobalStore() {
  /* TODO: generate the definition lazily? */
  assert(coqGlobalStoreAlias);
  return coqGlobalStoreAlias;
}

klee::ref<CoqExpr> StateTranslator::createSymbolics(ExecutionState &es,
                                                    vector<ref<CoqExpr>> &defs) {
  if (CacheSymNames) {
    return createSymbolicNamesCached(es.symbolics.size(), defs);
  } else {
    return createSymbolicNames(es.symbolics.size());
  }
}

klee::ref<CoqExpr> StateTranslator::createSymbolicNameCached(unsigned index,
                                                             vector<ref<CoqExpr>> &defs) {
  auto i = symbolicNameCache.find(index);
  if (i != symbolicNameCache.end()) {
    return i->second;
  }

  ref<CoqExpr> e = createSymbolicName(index);
  string aliasName = "sym_name_" + to_string(index);
  ref<CoqExpr> def = new CoqDefinition(aliasName, "string", e);
  ref<CoqExpr> alias = new CoqVariable(aliasName);
  symbolicNameCache[index] = alias;
  defs.push_back(def);
  return alias;
}

/* TODO: add an alias */
klee::ref<CoqExpr> StateTranslator::createSymbolicName(unsigned index) {
  ref<CoqExpr> arg;
  if (index == 0) {
    arg = createEmptyList();
  } else {
    arg = createSymbolicNames(index);
  }
  return new CoqApplication(
    new CoqVariable("fresh_name"),
    {arg}
  );
}

klee::ref<CoqExpr> StateTranslator::createSymbolicNamesCached(unsigned size,
                                                              vector<ref<CoqExpr>> &defs) {
  auto i = symbolicNamesCache.find(size);
  if (i != symbolicNamesCache.end()) {
    return i->second;
  }

  ref<CoqExpr> e = createSymbolicNames(size);
  string aliasName = "sym_names_" + to_string(size);
  ref<CoqExpr> def = new CoqDefinition(aliasName, "list string", e);
  ref<CoqExpr> alias = new CoqVariable(aliasName);
  symbolicNamesCache[size] = alias;
  defs.push_back(def);
  return alias;
}

/* TODO: add an alias */
klee::ref<CoqExpr> StateTranslator::createSymbolicNames(unsigned size) {
  ref<CoqExpr> arg;
  switch (size) {
  case 0:
    return createEmptyList();
  case 1:
    arg = createEmptyList();
    break;
  default:
    arg = createSymbolicNames(size - 1);
    break;
  }

  return new CoqApplication(
    new CoqVariable("extend_names"),
    {arg}
  );
}

klee::ref<CoqExpr> StateTranslator::createPC(ExecutionState &es,
                                             vector<ref<CoqExpr>> &defs) {
  ref<Expr> pc = es.getPC();
  if (CachePCExpr) {
    return exprTranslator->translate(pc, &es.arrayTranslation, true, true, defs);
  } else {
    return exprTranslator->translate(pc, &es.arrayTranslation);
  }
}

klee::ref<CoqExpr> StateTranslator::createModule() {
  return moduleTranslator->translateModuleCached();
}

string StateTranslator::getICAliasName(uint64_t stepID) {
  return "s_ic_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getICAlias(uint64_t stepID) {
  return new CoqVariable(getICAliasName(stepID));
}

string StateTranslator::getCommandAliasName(uint64_t stepID) {
  return "s_cmd_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getCommandAlias(uint64_t stepID) {
  return new CoqVariable(getCommandAliasName(stepID));
}

string StateTranslator::getCommandsAliasName(uint64_t stepID) {
  return "s_cmds_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getCommandsAlias(uint64_t stepID) {
  return new CoqVariable(getCommandsAliasName(stepID));
}

string StateTranslator::getPrevBIDAliasName(uint64_t stepID) {
  return "s_prev_bid_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getPrevBIDAlias(uint64_t stepID) {
  return new CoqVariable(getPrevBIDAliasName(stepID));
}

string StateTranslator::getLocalStoreAliasName(uint64_t stepID) {
  return "s_local_store_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getLocalStoreAlias(uint64_t stepID) {
  return new CoqVariable(getLocalStoreAliasName(stepID));
}

string StateTranslator::getStackAliasName(uint64_t stepID) {
  return "s_stack_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getStackAlias(uint64_t stepID) {
  return new CoqVariable(getStackAliasName(stepID));
}

string StateTranslator::getSymbolicsAliasName(uint64_t stepID) {
  return "s_symbolics_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getSymbolicsAlias(uint64_t stepID) {
  return new CoqVariable(getSymbolicsAliasName(stepID));
}

string StateTranslator::getPCAliasName(uint64_t stepID) {
  return "s_pc_" + to_string(stepID);
}

klee::ref<CoqVariable> StateTranslator::getPCAlias(uint64_t stepID) {
  return new CoqVariable(getPCAliasName(stepID));
}
