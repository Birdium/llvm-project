//===- llvm/include/llvm/Transforms/Utils/MyHello.h ----------*- C++ -*-===//

#ifndef LLVM_TRANSFORMS_UTILS_LOOPSPLITTING_H
#define LLVM_TRANSFORMS_UTILS_LOOPSPLITTING_H

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Instructions.h"

namespace llvm {
class LoopSplittingPass : public PassInfoMixin<LoopSplittingPass> {
private:
  SmallPtrSet<llvm::BasicBlock *, 16> panicBBs;
  SmallPtrSet<llvm::BranchInst *, 16> panicBranchInsts;
  SmallPtrSet<llvm::Value *, 16> bdchkInsts;
  SmallPtrSet<llvm::Value *, 16> bdchkInstsInv;
  void initialization(Function *F);

public:
  // run方法可以被new PassManager识别
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};
} // namespace llvm

#endif