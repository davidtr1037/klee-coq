#ifndef KLEE_STATE_TRANSLATION_H
#define KLEE_STATE_TRANSLATION_H

#include "ExecutionState.h"

#include "klee/Coq/CoqLanguage.h"

#include <map>

namespace klee {

class StateTranslator {

public:

  StateTranslator();

  ref<CoqExpr> translate(ExecutionState &es);

  ~StateTranslator();
};

}

#endif
