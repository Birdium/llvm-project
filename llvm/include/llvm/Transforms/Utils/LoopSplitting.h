//===- llvm/include/llvm/Transforms/Utils/MyHello.h ----------*- C++ -*-===//

#ifndef LLVM_TRANSFORMS_UTILS_LOOPSPLITTING_H
#define LLVM_TRANSFORMS_UTILS_LOOPSPLITTING_H

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

namespace llvm {
class LoopSplittingPass : public PassInfoMixin<LoopSplittingPass> {
public:
    // run方法可以被new PassManager识别
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};
}



#endif