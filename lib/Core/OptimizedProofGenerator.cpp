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
