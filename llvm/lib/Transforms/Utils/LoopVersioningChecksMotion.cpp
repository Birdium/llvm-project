#include "llvm/Transforms/Utils/LoopVersioningChecksMotion.h"
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

void LoopVersioningChecksMotionPass::initialization(Function *F) {
  panicBBs = {};
  panicBranchInsts = {};
  bdchkInsts = {};
  bdchkInstsInv = {};
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
getArrlen2CI(PHINode *PN, SmallPtrSet<Value *, 16> &bdchks, ScalarEvolution *SE,
             bool &doSplit) {
  SmallDenseMap<Value *, SmallPtrSet<CmpInst *, 16>> arrlen2CI;
  for (auto *I : bdchks) {
    if (auto *CI = dyn_cast<CmpInst>(I)) {
      if (CI->getOperand(0) == PN) {
        // dbgs() << CI->getPredicate() << "\n";
        if (CI->getPredicate() != CmpInst::ICMP_NE) {
          auto *arrlen = CI->getOperand(1);
          arrlen2CI[arrlen].insert(CI);
        }
      } else if (CI->getOperand(1) == PN) {
        // dbgs() << CI->getPredicate() << "\n";
        if (CI->getPredicate() != CmpInst::ICMP_NE) {
          auto *arrlen = CI->getOperand(0);
          arrlen2CI[arrlen].insert(CI);
        }
      } else {
        // doSplit = false;
        auto op0 = CI->getOperand(0);
        auto op1 = CI->getOperand(1);
        auto scev0 = SE->getSCEV(op0);
        auto scev1 = SE->getSCEV(op1);
        dbgs() << "CI: " << *CI << "\n";
        dbgs() << *scev0 << "   " << *scev1 << "\n";
        auto *arrlen = CI->getOperand(1);
        arrlen2CI[arrlen].insert(CI);

        // break;
      }
    }
  }
  return arrlen2CI;
}

PreservedAnalyses
LoopVersioningChecksMotionPass::run(Function &F, FunctionAnalysisManager &AM) {
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
        SmallVector<BasicBlock *, 4> ExitingBlocks;
        L->getExitingBlocks(ExitingBlocks);

        auto loopMaxTripCount = SE->getSymbolicMaxBackedgeTakenCount(L);

        dbgs() << "Loop max trip count: " << *loopMaxTripCount << "\n";

        if (dyn_cast<SCEVCouldNotCompute>(loopMaxTripCount)) {
          dbgs() << "Could not compute loop max trip count\n";
          continue;
        }

        bool doSplit = bdchks.size() > 0;

        auto arrlen2CI = getArrlen2CI(PN, bdchks, SE, doSplit);

        if (doSplit) {
          bool doEliminate = arrlen2CI.size() > 0;
          SmallPtrSet<CmpInst *, 16> mayOutCmps;
          for (auto &[arrlen, CIs] : arrlen2CI) {
            auto *arrlenSCEV = SE->getSCEV(arrlen);

            for (auto CI : CIs) {
              mayOutCmps.insert(CI);
            }
          }
          if (!mayOutCmps.empty()) {
            if (L->isInnermost()) {
              ValueToValueMapTy VMap;
              SmallVector<llvm::BasicBlock *, 8> NewLoopBlocks;
              if (L->getLoopPreheader()) {
                changed = true;
                dbgs() << "Do Promotion\n";

                // clone a new loop
                auto preheader = L->getLoopPreheader();

                dbgs() << "preheader: " << *preheader << "\n";
                dbgs() << "header: " << *L->getHeader() << "\n";

                auto originPreheader =
                    SplitEdge(preheader, L->getHeader(), DT, LI);

                llvm::Loop *NewLoop = llvm::cloneLoopWithPreheader(
                    L->getLoopPreheader(), L->getLoopPreheader(), L, VMap,
                    ".clone", LI, DT, NewLoopBlocks);
                remapInstructionsInBlocks(NewLoopBlocks, VMap);

                // for (auto [Old, New] : VMap) {
                //   dbgs() << "Old: " << *Old << "\n";
                //   dbgs() << "New: " << *New << "\n";
                // }

                auto clonePreheader = NewLoop->getLoopPreheader();

                // remove bdchks in newloop
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

                // add phi node to exit blocks
                SmallVector<BasicBlock *, 16> ExitBBs;
                NewLoop->getExitBlocks(ExitBBs);

                for (auto *ExitBB : ExitBBs) {
                  // Iterate over the instructions in the exit block.
                  for (auto &I : *ExitBB) {
                    // Check if the instruction is a phi instruction.
                    if (auto *Phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
                      // Modify the phi instruction.
                      // For example, you can replace an incoming value:
                      dbgs() << "Phi: " << *Phi << "\n";
                      for (int i = 0, e = Phi->getNumIncomingValues(); i != e;
                           ++i) {
                        llvm::Value *Incoming = Phi->getIncomingValue(i);
                        if (VMap.count(Incoming)) {
                          llvm::Value *IncomingBB = Phi->getIncomingBlock(i);
                          auto newVal = VMap[Incoming];
                          BasicBlock *newBB =
                              dyn_cast<BasicBlock>(VMap[IncomingBB]);
                          Phi->addIncoming(newVal, newBB);
                        } else {
                          llvm::Value *IncomingBB = Phi->getIncomingBlock(i);
                          if (VMap.count(IncomingBB)) {
                            BasicBlock *newBB =
                                dyn_cast<BasicBlock>(VMap[IncomingBB]);
                            Phi->addIncoming(Incoming, newBB);
                          }
                        }
                      }
                    }
                  }
                }

                // auto DefsUsedOutside = findDefsUsedOutsideOfLoop(L);

                // for (auto *I : DefsUsedOutside) {
                //   dbgs() << "DefUsedOutside: " << *I << "\n";
                // }
                dbgs() << "NewLoopBlocks count: " << NewLoopBlocks.size()
                       << "\n";
                for (auto *BB : NewLoop->getBlocks()) {
                  dbgs() << "NewLoopBlock: " << *BB << "\n";
                }

                // promote bounds check
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

                  LoopToScevMapT LoopToScevMap;
                  LoopToScevMap[L] = loopMaxTripCount;

                  SCEVLoopAddRecRewriter Rewriter(*SE, LoopToScevMap);

                  auto scev_idx_max = SCEVLoopAddRecRewriter::rewrite(
                      scev_idx, LoopToScevMap, *SE);
                  // SE->getSCEVAtScope(scev_idx, L->getParentLoop());

                  dbgs() << "scev_idx: " << *scev_idx << "\n";
                  dbgs() << "scev_len: " << *scev_len << "\n";
                  dbgs() << "scev_idx_max: " << *scev_idx_max << "\n";

                  llvm::SCEVExpander Expander(
                      *SE, F.getParent()->getDataLayout(), "scevexpander");
                  auto *val_idx = Expander.expandCodeFor(
                      scev_idx_max, nullptr, preheader->getTerminator());
                  auto *val_len = Expander.expandCodeFor(
                      scev_len, nullptr, preheader->getTerminator());
                  auto bdchk = ICmpInst::Create(
                      Instruction::ICmp, ICmpInst::ICMP_ULT, val_idx, val_len);
                  dbgs() << "preheader: " << *preheader << "\n";
                  dbgs() << "bdchk: " << *bdchk << "\n";
                  bdchk->insertBefore(preheader->getTerminator());
                  cmpvalues.push_back(bdchk);
                }
                Value *branchvalue = nullptr;
                if (!cmpvalues.empty()) {
                  branchvalue = cmpvalues[0];
                  for (int i = 1; i < cmpvalues.size(); i++) {
                    branchvalue =
                        BinaryOperator::CreateAnd(branchvalue, cmpvalues[i]);
                    auto branchinst = dyn_cast<Instruction>(branchvalue);

                    dbgs() << "branchinst: " << *branchinst << "\n";
                    branchinst->insertBefore(preheader->getTerminator());
                  }
                  // branchvalue = llvm::ConstantInt::get(
                  //     llvm::Type::getInt1Ty(F.getContext()), 1);
                  auto *NewBI = BranchInst::Create(
                      clonePreheader, originPreheader, branchvalue);
                  NewBI->insertBefore(preheader->getTerminator());
                  preheader->getTerminator()->eraseFromParent();
                }
              }
            }
          }
        }
      }
    }
  }

  dbgs() << "\n";
  if (changed) {
    dbgs() << "Changed\n";
    return PreservedAnalyses::none();
  } else {
    dbgs() << "No change\n";
    return PreservedAnalyses::all();
  }
}