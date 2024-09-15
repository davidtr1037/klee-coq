#ifndef KLEE_OPTIMIZED_PROOF_GENERATOR_H
#define KLEE_OPTIMIZED_PROOF_GENERATOR_H

#include "ExecutionState.h"
#include "ProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <vector>

namespace klee {

class OptimizedProofGenerator : public ProofGenerator {

public:

  OptimizedProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  ref<CoqTactic> getTacticForEquivAssignment(StateInfo &si,
                                             ExecutionState &successor);

};

}

#endif
