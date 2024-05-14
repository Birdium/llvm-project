#include "llvm/Transforms/Utils/LoopSplitting.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
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
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"

using namespace llvm;

void LoopSplittingPass::initialization(Function *F) {
  for (auto &BB : *F) {
    for (auto &I : BB) {
      // dbgs() << "Instruction: " << I << "\n";
      if (auto *LI = dyn_cast<CallInst>(&I)) {
        if (auto cf = LI->getCalledFunction()) {
          if (auto name = cf->getName(); name.contains("panic_bounds_check")) {
            // dbgs() << "panic BB: " << BB << "\n";
            panicBBs.insert(&BB);
          }
        }
      }
      if (auto *LI = dyn_cast<InvokeInst>(&I)) {
        if (auto cf = LI->getCalledFunction()) {
          if (auto name = cf->getName(); name.contains("panic_bounds_check")) {
            // dbgs() << "panic BB: " << BB << "\n";
            panicBBs.insert(&BB);
          }
        }
      }
    }
  }
  for (auto *BB : panicBBs) {
    // dbgs() << "panic BB: " << BB->getName() << "\n";
    for (auto *PredBB : predecessors(BB)) {
      if (auto *TI = PredBB->getTerminator()) {
        // PanicInsts.insert(TI);
        if (auto *BI = dyn_cast<BranchInst>(TI)) {
          if (BI->isConditional()) {
            auto CI = dyn_cast<CmpInst>(BI->getCondition());
            // if
            // (BI->getSuccessor(0)->getName().contains("panic_bounds_check")) {
            //   BI->swapSuccessors();
            //   CI->setPredicate(CI->getInversePredicate());
            // }
            // if (CI->getPredicate() == CmpInst::ICMP_SGT ||
            //     CI->getPredicate() == CmpInst::ICMP_UGT ||
            //     CI->getPredicate() == CmpInst::ICMP_SGE ||
            //     CI->getPredicate() == CmpInst::ICMP_UGE) {
            //   CI->swapOperands();
            // }

            panicBranchInsts.insert(BI);
            bdchkInsts.insert(CI);
            if (BI->getSuccessor(0)->getName().contains("panic_bounds_check")) {
              bdchkInstsInv.insert(CI);
            }
          }
        }
      }
    }
  }
}

static SmallPtrSet<BranchInst *, 16>
findPanicBranchInstsInLoop(Loop *L,
                           SmallPtrSet<BranchInst *, 16> &PanicBranchInsts) {
  SmallPtrSet<BranchInst *, 16> panics;
  for (auto *BB : L->getBlocks()) {
    for (auto &I : *BB) {
      if (auto *BI = dyn_cast<BranchInst>(&I)) {
        if (BI->isConditional()) {
          if (PanicBranchInsts.count(BI)) {
            panics.insert(BI);
          }
        }
      }
    }
  }
  return panics;
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

static SmallDenseMap<Value *, SmallPtrSet<CmpInst *, 16>>
getArrlen2CI(PHINode *PN, SmallPtrSet<Value *, 16> &bdchks, bool &doSplit) {
  SmallDenseMap<Value *, SmallPtrSet<CmpInst *, 16>> arrlen2CI;
  for (auto *I : bdchks) {
    if (auto *CI = dyn_cast<CmpInst>(I)) {
      if (CI->getOperand(0) == PN) {
        dbgs() << CI->getPredicate() << "\n";
        if (CI->getPredicate() != CmpInst::ICMP_NE) {
          auto *arrlen = CI->getOperand(1);
          arrlen2CI[arrlen].insert(CI);
        }
      } else if (CI->getOperand(1) == PN) {
        dbgs() << CI->getPredicate() << "\n";
        if (CI->getPredicate() != CmpInst::ICMP_NE) {
          auto *arrlen = CI->getOperand(0);
          arrlen2CI[arrlen].insert(CI);
        }
      } else {
        doSplit = false;
        break;
      }
    }
  }
  return arrlen2CI;
}

PreservedAnalyses LoopSplittingPass::run(Function &F,
                                         FunctionAnalysisManager &AM) {
  LoopInfo *LI = &AM.getResult<LoopAnalysis>(F);
  DominatorTree *DT = &AM.getResult<DominatorTreeAnalysis>(F);
  auto *LAIs = &AM.getResult<LoopAccessAnalysis>(F);
  ScalarEvolution *SE = &AM.getResult<ScalarEvolutionAnalysis>(F);
  // dbgs() << "LI, DT, SE, AC, MSSAAnalysis: " << LI << ", " << DT << ", " <<
  // SE << ", " << AC << ", " << MSSAAnalysis << "\n";
  dbgs() << "========================================\n";
  dbgs() << "Function: " << F.getName() << "\n";

  initialization(&F);

  // dbgs() << "panic insts count: " << PanicInsts.size() << "\n";
  // for (auto *I : PanicInsts) {
  //	dbgs() << "panic inst: " << *I << "\n";
  // }
  // dbgs() << "bdchk insts count: " << BdchkInsts.size() << "\n";
  // for (auto *I : BdchkInsts) {
  //  dbgs() << "bdchk inst: " << *I << "\n";
  // }
  bool changed = false;

  for (auto *L : LI->getLoopsInPreorder()) {
    dbgs() << "----------------------------------------\n";
    dbgs() << "Loop: " << L->getHeader()->getName() << "\n";
    if (!L->isInnermost()) {
      // continue;
    }
    auto bdchks = findBdchkInstsInLoop(L, bdchkInsts);
    auto panicbranches = findPanicBranchInstsInLoop(L, panicBranchInsts);
    // TODO: Check if the loop contains memory access instructions.
    auto btc = SE->getBackedgeTakenCount(L);

    BasicBlock *Header = L->getHeader();
    if (PHINode *PN = dyn_cast<PHINode>(&Header->front())) {
      if (SE->isSCEVable(PN->getType())) {
        const SCEV *S = SE->getSCEV(PN);
        // if (const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(S)) {
        // if (AR->getLoop() == L && AR->isAffine()) {
        // PN is an induction variable.
        dbgs() << "SCEV: " << *S << "\n";
        dbgs() << "Backedge taken count: " << *btc << "\n";
        dbgs() << "Backedge max taken count: "
               << *SE->getSymbolicMaxBackedgeTakenCount(L) << "\n";
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

        auto loopMaxTripCount = SE->getSymbolicMaxBackedgeTakenCount(L);

        if (auto *UMinExpr = dyn_cast<SCEVUMinExpr>(loopMaxTripCount)) {
          auto *LHS = UMinExpr->getOperand(0);
          auto *RHS = UMinExpr->getOperand(1);
          auto *LHSSimplified = SE->getSCEVAtScope(LHS, L);
          auto *RHSSimplified = SE->getSCEVAtScope(RHS, L);
          if (!SE->hasComputableLoopEvolution(LHSSimplified, L)) {
            // LHS does not contain a recursive subexpression, replace
            // UMinExpr with LHS
            loopMaxTripCount = LHSSimplified;
          } else if (!SE->hasComputableLoopEvolution(RHSSimplified, L)) {
            // RHS does not contain a recursive subexpression, replace
            // UMinExpr with RHS
            loopMaxTripCount = RHSSimplified;
          }
        }

        dbgs() << "Loop max trip count: " << *loopMaxTripCount << "\n";

        bool doSplit = bdchks.size() > 0;

        auto arrlen2CI = getArrlen2CI(PN, bdchks, doSplit);

        if (doSplit) {
          bool doEliminate = arrlen2CI.size() > 0;
          dbgs() << "Splitting: " << doSplit << "\n";
          dbgs() << "Array lengths count: " << arrlen2CI.size() << "\n";
          SmallPtrSet<CmpInst *, 16> mayOutCmps;
          for (auto &[arrlen, CIs] : arrlen2CI) {
            auto *arrlenSCEV = SE->getSCEV(arrlen);

            dbgs() << "Array length: " << *arrlenSCEV << "\n";
            for (auto CI : CIs) {
              auto index = CI->getOperand(0) == arrlen ? CI->getOperand(1)
                                                       : CI->getOperand(0);
              bool isCITrueWhenEQ = CI->isTrueWhenEqual();
              if (bdchkInstsInv.count(CI)) {
                isCITrueWhenEQ = !isCITrueWhenEQ;
              }
              auto *indexSCEV = SE->getSCEV(index);
              dbgs() << "Index: " << *indexSCEV << "\n";
              const SCEV *diff = SE->getMinusSCEV(arrlenSCEV, loopMaxTripCount);
              dbgs() << "Difference: " << *diff << "\n";
              bool isAlwaysInbound =
                  isCITrueWhenEQ ? isKnownNonNegativeInLoop(diff, L, *SE)
                                 : isKnownPositiveInLoop(diff, L, *SE);
              if (!isAlwaysInbound) {
                dbgs() << "Index may out of bound: " << *CI << "\n";
                doEliminate = false;
                mayOutCmps.insert(CI);
              } else {
                dbgs() << "Index always in bound: " << *CI << "\n";
                for (auto *I : panicbranches) {
                  if (auto *BI = dyn_cast<BranchInst>(I)) {
                    if (BI->getCondition() == CI) {
                      auto succ0 = BI->getSuccessor(0);
                      auto succ1 = BI->getSuccessor(1);
                      BasicBlock *target =
                          panicBBs.count(succ0) ? succ1 : succ0;
                      BranchInst *NewBI = BranchInst::Create(target);
                      NewBI->insertAfter(I);
                      I->eraseFromParent();
                      LI;
                      changed = true;
                    }
                  }
                }
              }
            }
          }
          if (!mayOutCmps.empty()) {
            if (L->isInnermost()) {
              dbgs() << "Do Promotion\n";
              ValueToValueMapTy VMap;
              SmallVector<llvm::BasicBlock *, 8> NewLoopBlocks;
              if (L->getLoopPreheader()) {
                auto preheader = L->getLoopPreheader();
                auto originPreheader =
                    SplitEdge(preheader, L->getHeader(), DT, LI);
                llvm::Loop *NewLoop = llvm::cloneLoopWithPreheader(
                    L->getLoopPreheader(), L->getLoopPreheader(), L, VMap,
                    ".clone", LI, DT, NewLoopBlocks);
                remapInstructionsInBlocks(NewLoopBlocks, VMap);
                auto clonePreheader = NewLoop->getLoopPreheader();
                SmallDenseMap<BranchInst *, BranchInst *> BranchReplacements;
                for (auto *BB : NewLoop->getBlocks()) {
                  for (auto &I : *BB) {
                    if (auto *BI = dyn_cast<BranchInst>(&I)) {
                      if (BI->getNumSuccessors() == 2) {
                        auto succ0 = BI->getSuccessor(0);
                        auto succ1 = BI->getSuccessor(1);
                        BasicBlock *target = nullptr;
                        if (panicBBs.count(succ0)) {
                          target = succ1;
                        } else if (panicBBs.count(succ1)) {
                          target = succ0;
                        }
                        if (target != nullptr) {
                          BranchInst *NewBI = BranchInst::Create(target);
                          BranchReplacements[BI] = NewBI;
                        }
                      }
                    }
                  }
                }
                for (auto &[BI, NewBI] : BranchReplacements) {
                  NewBI->insertAfter(BI);
                  BI->eraseFromParent();
                }
                dbgs() << "NewLoopBlocks count: " << NewLoopBlocks.size() << "\n";
                for (auto *BB : NewLoop->getBlocks()) {
                  dbgs() << "NewLoopBlock: " << *BB << "\n";
                }
                SmallVector<Value *, 16> cmpvalues;
                for (auto CI : mayOutCmps) {
                  auto op0 = CI->getOperand(0);
                  auto op1 = CI->getOperand(1);
                  auto scev0 = SE->getSCEV(op0);
                  auto scev1 = SE->getSCEV(op1);
                  dbgs() << "CI: " << *CI << "\n";
                  dbgs() << "op0: " << *op0 << "\n";
                  dbgs() << "op1: " << *op1 << "\n";
                  auto scev_idx = arrlen2CI.count(op0) ? scev1 : scev0;
                  auto scev_len = arrlen2CI.count(op0) ? scev0 : scev1;
                  auto scev_idx_max =
                      SE->getSCEVAtScope(scev_idx, L->getParentLoop());

                  dbgs() << "scev_idx: " << *scev_idx << "\n";
                  dbgs() << "scev_len: " << *scev_len << "\n";
                  dbgs() << "scev_idx_max: " << *scev_idx_max << "\n";

                  llvm::SCEVExpander Expander(
                      *SE, F.getParent()->getDataLayout(), "scevexpander");
                  auto val_idx = Expander.expandCodeFor(
                      scev_idx_max, nullptr, preheader->getTerminator());
                  auto val_len = Expander.expandCodeFor(
                      scev_len, nullptr, preheader->getTerminator());
                  auto bdchk = ICmpInst::Create(
                      Instruction::ICmp, ICmpInst::ICMP_ULT, val_idx, val_len);
                  bdchk->insertBefore(preheader->getTerminator());
                  cmpvalues.push_back(bdchk);
                }
                Value *branchvalue = nullptr;
                if (!cmpvalues.empty())
                  branchvalue = cmpvalues[0];
                for (int i = 1; i < cmpvalues.size(); i++) {
                  branchvalue =
                      BinaryOperator::CreateAnd(branchvalue, cmpvalues[i]);
                  auto branchinst = dyn_cast<BranchInst>(branchvalue);
                  branchinst->insertBefore(preheader->getTerminator());
                }
                auto *NewBI = BranchInst::Create(originPreheader,
                                                 clonePreheader, branchvalue);
                NewBI->insertBefore(preheader->getTerminator());
                preheader->getTerminator()->eraseFromParent();
              }
            }
          }
        }
      }
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

  dbgs() << "\n";
  if (changed) {
    dbgs() << "Changed\n";
    return PreservedAnalyses::none();
  } else {
    dbgs() << "No change\n";
    return PreservedAnalyses::all();
  }
}