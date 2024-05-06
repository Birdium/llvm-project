#include "llvm/Transforms/Utils/LoopSplitting.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

static SmallPtrSet<Value *, 16> getBdchkInsts(Function *F) {
  SmallPtrSet<BasicBlock *, 16> PanicBBs;
  SmallPtrSet<Value *, 16> BdchkInsts;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      // dbgs() << "Instruction: " << I << "\n";
      if (auto *LI = dyn_cast<CallInst>(&I)) {
        if (auto cf = LI->getCalledFunction()) {
          if (auto name = cf->getName(); name.contains("panic_bounds_check")) {
            // dbgs() << "panic BB: " << BB << "\n";
            PanicBBs.insert(&BB);
          }
        }
      }
      if (auto *LI = dyn_cast<InvokeInst>(&I)) {
        if (auto cf = LI->getCalledFunction()) {
          if (auto name = cf->getName(); name.contains("panic_bounds_check")) {
            // dbgs() << "panic BB: " << BB << "\n";
            PanicBBs.insert(&BB);
          }
        }
      }
    }
  }
  for (auto *BB : PanicBBs) {
    // dbgs() << "panic BB: " << BB->getName() << "\n";
    for (auto *PredBB : predecessors(BB)) {
      if (auto *TI = PredBB->getTerminator()) {
        // PanicInsts.insert(TI);
        if (auto *BI = dyn_cast<BranchInst>(TI)) {
          if (BI->isConditional()) {
            BdchkInsts.insert(BI->getCondition());
          }
        }
      }
    }
  }
  for (auto *I : BdchkInsts) {
    dbgs() << "bdchk inst: " << *I << "\n";
  }
  return BdchkInsts;
}

static SmallPtrSet<Value *, 16>
findBdchkInstsInLoop(Loop *L, SmallPtrSet<Value *, 16> &BdchkInsts) {
  SmallPtrSet<Value *, 16> bdchks;
  for (auto *BB : L->getBlocks()) {
    for (auto &I : *BB) {
      if (BdchkInsts.count(&I)) {
        bdchks.insert(&I);
      }
    }
  }
  return bdchks;
}

PreservedAnalyses LoopSplittingPass::run(Function &F,
                                         FunctionAnalysisManager &AM) {
  LoopInfo *LI = &AM.getResult<LoopAnalysis>(F);
  DominatorTree *DT = &AM.getResult<DominatorTreeAnalysis>(F);
  ScalarEvolution *SE = &AM.getResult<ScalarEvolutionAnalysis>(F);
  AssumptionCache *AC = &AM.getResult<AssumptionAnalysis>(F);
  auto *MSSAAnalysis = AM.getCachedResult<MemorySSAAnalysis>(F);
  // dbgs() << "LI, DT, SE, AC, MSSAAnalysis: " << LI << ", " << DT << ", " <<
  // SE << ", " << AC << ", " << MSSAAnalysis << "\n";
  dbgs() << "========================================\n";
  dbgs() << "Function: " << F.getName() << "\n";

  // dbgs() << "panic insts count: " << PanicInsts.size() << "\n";
  // for (auto *I : PanicInsts) {
  //	dbgs() << "panic inst: " << *I << "\n";
  // }
  // dbgs() << "bdchk insts count: " << BdchkInsts.size() << "\n";
  // for (auto *I : BdchkInsts) {
  //  dbgs() << "bdchk inst: " << *I << "\n";
  // }

  auto BdchkInsts = getBdchkInsts(&F);

  for (auto *L : LI->getLoopsInPreorder()) {
    dbgs() << "----------------------------------------\n";
    dbgs() << "Loop: " << L->getHeader()->getName() << "\n";
    if (!L->isInnermost()) {
      // continue;
    }
    auto bdchks = findBdchkInstsInLoop(L, BdchkInsts);
    // TODO: Check if the loop contains memory access instructions.
    auto btc = SE->getBackedgeTakenCount(L);

    BasicBlock *Header = L->getHeader();
    if (PHINode *PN = dyn_cast<PHINode>(&Header->front())) {
      if (SE->isSCEVable(PN->getType())) {
        const SCEV *S = SE->getSCEV(PN);
        //if (const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(S)) {
          //if (AR->getLoop() == L && AR->isAffine()) {
            // PN is an induction variable.
            dbgs() << "SCEV: " << *S << "\n";
            dbgs() << "Backedge taken count: " << *btc << "\n";
            dbgs() << "Induction variable: " << *PN << "\n";
            SmallVector<BasicBlock *, 4> ExitingBlocks;
            L->getExitingBlocks(ExitingBlocks);
            dbgs() << "Exiting blocks count: " << ExitingBlocks.size() << "\n";
            for (auto *ExitingBlock : ExitingBlocks) {
              dbgs() << "Exiting block: " << ExitingBlock->getName() << "\n";
            }
            dbgs() << "bdchk insts count: " << bdchks.size() << "\n";
            for (auto *I : bdchks) {
              dbgs() << "bdchk inst: " << *I << "\n";
            }
          //}
        //}
      }
    }

    // if (IV != nullptr)
    //   dbgs() << "Canonical induction variable: " << *IV << "\n";
    // else
    //   dbgs() << "No canonical induction variable\n";
    // const SCEV *BackedgeTakenCount =
    // getAnalysis<ScalarEvolutionWrapperPass>().getSE()->getBackedgeTakenCount(L);

    // TODO: Get the loop's iteration count and the size of the accessed array.

    // Create a new basic block to hold the split loop.
    // BasicBlock *NewBB = BasicBlock::Create(F.getContext(), "split", &F);

    // Create a condition to check if the iteration count and array size are
    // less than 100. IRBuilder<> Builder(&F.getEntryBlock().front()); Value
    // *Cond = Builder.CreateAnd(
    //   Builder.CreateICmpSLT(IterationCount, Builder.getInt64(100)),
    //   Builder.CreateICmpSLT(ArraySize, Builder.getInt64(100))
    // );

    // Split the loop based on the condition.
    //   SplitBlockAndInsertIfThen(Cond, &F.getEntryBlock().front(), false,
    //   nullptr, nullptr, NewBB);

    // TODO: Clone the loop and modify the bounds to [0, 100) and [100, m).

    // TODO: Add the cloned loops to the new basic block.
  }

  dbgs() << "\n";
  return PreservedAnalyses::all();
}
