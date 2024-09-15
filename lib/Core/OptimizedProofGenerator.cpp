#include "OptimizedProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"

#include <string>

using namespace std;
using namespace llvm;
using namespace klee;

OptimizedProofGenerator::OptimizedProofGenerator(Module &m, raw_ostream &output)
  : ProofGenerator(m, output) {

}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivAssignment(StateInfo &si,
                                                                          ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    vector<ref<CoqExpr>> pairs;
    for (RegisterUpdate &ru : si.suffix) {
      ref<CoqExpr> pair = new CoqPair(
        moduleTranslator->createName(ru.name),
        createPlaceHolder()
      );
      pairs.push_back(pair);
    }
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_optimized_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqList(pairs),
          }
        ),
        new Inversion("Heval"),
        new Subst(),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  } else {
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("Heval"),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }

  return new Block(
    {
      new Apply("inversion_instr_op", "Hstep"),
      new Destruct("Hstep", {{"se", "Hstep"}}),
      new Destruct("Hstep", {{"Heval", "Heq"}}),
      new Rewrite("Heq"),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivPHI(StateInfo &si,
                                                                   ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    vector<ref<CoqExpr>> pairs;
    for (RegisterUpdate &ru : si.suffix) {
      ref<CoqExpr> pair = new CoqPair(
        moduleTranslator->createName(ru.name),
        createPlaceHolder()
      );
      pairs.push_back(pair);
    }
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_optimized_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqList(pairs),
          }
        ),
        new Inversion("Heval"),
        new Subst(),
        new Apply("equiv_smt_expr_refl"),
      }
    );
  } else {
    t = new Block(
      {
        new Inversion("Heval"),
        new Subst(),
        new Apply("equiv_smt_store_refl"),
      }
    );
  }
  return new Block(
    {
      new Apply("inversion_phi", "Hstep"),
      new Destruct("Hstep", {{"se", "Hstep"}}),
      new Destruct("Hstep", {{"Heval", "Heq"}}),
      new Rewrite("Heq"),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivBranch(StateInfo &si,
                                                                      ExecutionState &successor,
                                                                      ProofHint *hint) {

  BranchInst *bi = cast<BranchInst>(si.inst);
  if (bi->isConditional()) {
    return ProofGenerator::getTacticForEquivBranch(si, successor, hint);
  } else {
    return new Block(
      {
        new Apply("inversion_unconditional_br", "Hstep"),
        new Destruct("Hstep", {{"d", "Hstep"}}),
        new Destruct("Hstep", {{"b", "Hstep"}}),
        new Destruct("Hstep", {{"c", "Hstep"}}),
        new Destruct("Hstep", {{"cs", "Hstep"}}),
        new Destruct("Hstep", {{"Hd", "Hb"}}),
        new Destruct("Hb", {{"Hb", "Hc"}}),
        new Destruct("Hc", {{"Hc", "Hcs"}}),
        new Inversion("Hd"),
        new Subst(),
        new Inversion("Hb"),
        new Subst(),
        new Inversion("Hc"),
        new Subst(),
        new Apply("EquivSymState"),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_smt_expr_refl")}),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivCall(StateInfo &si,
                                                                    ExecutionState &successor) {
  return ProofGenerator::getTacticForEquivCall(si, successor);
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivReturn(StateInfo &si,
                                                                      ExecutionState &successor) {
  return ProofGenerator::getTacticForEquivReturn(si, successor);
}
