#ifndef KLEE_TRANSLATION_H
#define KLEE_TRANSLATION_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "klee/Coq/CoqLanguage.h"

namespace klee {

class ModuleTranslator {

public:

    llvm::Module &m;

    ModuleTranslator(llvm::Module &m);

    ref<CoqExpr> translate();

    ~ModuleTranslator();
};

}

#endif
