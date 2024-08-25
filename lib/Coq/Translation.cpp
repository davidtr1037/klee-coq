#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

using namespace llvm;
using namespace klee;

ModuleTranslator::ModuleTranslator(Module &m) : m(m) {

}

ref<CoqExpr> ModuleTranslator::translate() {
    //for (Function &f : m) {
    //    for (BasicBlock &bb : f) {
    //        for (Instruction &i : bb) {
    //            errs() << i << "\n";
    //        }
    //    }
    //}

    ref<CoqExpr> coq_module = new CoqApplication(
        new CoqVariable("mk_module"),
        {
            new CoqVariable("None"),
            new CoqVariable("None"),
            new CoqVariable("None"),
            new CoqList({}),
            new CoqList({}),
            new CoqList({}),
            new CoqList({}),
        }
    );

    return coq_module;
}

ref<CoqExpr> ModuleTranslator::translateFunction(Function &f) {
    return new CoqVariable("None");
}

ModuleTranslator::~ModuleTranslator() {

}
