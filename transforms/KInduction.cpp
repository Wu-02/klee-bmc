#include <map>

#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/SimpleLoopUnswitch.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"

using namespace llvm;

static cl::opt<unsigned> K("kind-k", cl::desc("Parameter k for k-induction."),
                           cl::value_desc("N"));

namespace {
// This pass transforms a loop in LCSSA form to its over-approximation based on
// k-induction. The loop will be replaced with two clones, one for paths with
// trip count less than k, and the other for paths with trip count at least k
// which is over-approximated. The branch taken is chosen non-deterministically
// at the preheader.
// Adapted from LoopUnswitch pass.
class KInductionPass : public LoopPass {
  DominatorTree *DT = nullptr;
  LoopInfo *LI;
  LPPassManager *LPM;
  // LoopBlocks contains all of the basic blocks of the loop to be cloned,
  // including the preheader of the loop, the body of the loop, and the exit
  // blocks of the loop, in that order.
  std::vector<BasicBlock *> LoopBlocks;
  // NewBlocks contained cloned copy of basic blocks from LoopBlocks.
  std::vector<BasicBlock *> NewBlocks;

 public:
  static char ID;

  KInductionPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *, LPPassManager &LPMRef) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequiredID(LoopSimplifyID);
    LoopPass::getAnalysisUsage(AU);
  }

 private:
  Value *emitNondetValue(Type *type, Instruction *I, StringRef name);

  Value *emitTripCount(Loop *L);

  void emitPreheaderBranchOnCondition(Value *LIC, Constant *Val,
                                      BasicBlock *TrueDest,
                                      BasicBlock *FalseDest,
                                      BranchInst *OldBranch);

  Loop *cloneLoopWithCondition(Loop *L, Value *Cond);

  void boundLoop(Loop *L);

  void abstractLoop(Loop *L);
};

static RegisterPass<KInductionPass> IS(
    "k-induction", "Instrument loops for k-induction over-approximation.");
char KInductionPass::ID = 0;

// Creates an intrinsic verifier call and inserts it before given instruction.
CallInst *emitVerifierCall(StringRef Name, Type *ReturnType,
                           ArrayRef<Value *> Args, Instruction *I) {
  Function *F = I->getParent()->getParent();
  Module *M = F->getParent();
  LLVMContext &Ctx = F->getContext();

  AttrBuilder B(Ctx);
  B.addAttribute(Attribute::NoUnwind);
  B.addAttribute(Attribute::NoRecurse);
  B.addAttribute(Attribute::OptimizeNone);
  B.addAttribute(Attribute::NoInline);
  AttributeList attrs =
      AttributeList::get(Ctx, AttributeList::FunctionIndex, B);
  SmallVector<Type *> argTypes = {};
  for (Value *arg : Args) {
    argTypes.push_back(arg->getType());
  }
  auto funcType = FunctionType::get(ReturnType, argTypes, false);
  auto callee = M->getOrInsertFunction(Name, funcType, attrs);

  IRBuilder<> IRB(Ctx);
  IRB.SetInsertPoint(I);
  return IRB.CreateCall(callee, Args);
}

// Emits trip count, i.e. how many times the backedge has been taken in a loop.
// The loop should be in simplified form. Returns trip count value.
//
// header: %Loop.trip = phi [0 %preheader] [%inc %latch]
//   ...
// latch:
//   ...
//   %inc = add %counter 1 br %Loop.trip
//   br ...
Value *KInductionPass::emitTripCount(Loop *L) {
  BasicBlock *Header = L->getHeader();
  BasicBlock *Preheader = L->getLoopPreheader();
  LLVMContext &Ctx = Header->getContext();
  IRBuilder<> B(Ctx);

  // Create a counter variable at header to track the backedge-taken count.
  B.SetInsertPoint(&Header->front());
  auto *counterType = Type::getInt32Ty(Ctx);
  PHINode *Counter = B.CreatePHI(counterType, 2, L->getName() + ".tripcount");
  Counter->addIncoming(ConstantInt::get(counterType, 0), Preheader);

  // Increment the counter by 1 at the end of latch.
  BasicBlock *Latch = L->getLoopLatch();
  B.SetInsertPoint(Latch->getTerminator());
  Value *incCounter = B.CreateAdd(Counter, ConstantInt::get(counterType, 1));
  Counter->addIncoming(incCounter, Latch);
  return Counter;
}

// Inserts a call to __VERIFIER_make_nondet before given instruction `I`,
// havocking the value `Val` passed to it. `Val` must be of pointer type and
// defined before `I`.
CallInst *createHavocCall(Value *Val, Instruction *I,
                          StringRef name = "unnamed") {
  Function *F = I->getParent()->getParent();
  Module *M = F->getParent();
  LLVMContext &Ctx = F->getContext();

  const DataLayout *DL = &M->getDataLayout();
  auto type = dyn_cast<PointerType>(Val->getType());
  assert(type && "Value must be of pointer type.");
  auto sz = DL->getTypeAllocSize(type->getElementType());
  auto *sizeType = Type::getInt32Ty(Ctx);

  // We cannot directly pass a ConstantDataArray, or klee will complain.
  Constant *strConst = ConstantDataArray::getString(Ctx, name);
  auto *strGlobal =
      new GlobalVariable(*M, strConst->getType(), true,
                         GlobalValue::PrivateLinkage, strConst, ".str");
  auto *strPtr =
      IRBuilder<>(I).CreateGEP(strGlobal->getValueType(), strGlobal,
                               {ConstantInt::get(Type::getInt64Ty(Ctx), 0),
                                ConstantInt::get(Type::getInt64Ty(Ctx), 0)});
  SmallVector<Value *> Args = {Val, ConstantInt::get(sizeType, sz), strPtr};
  return emitVerifierCall("__VERIFIER_make_nondet", Type::getVoidTy(Ctx), Args,
                          I);
}

// Allocates memory for a variable of given type on the stack, calls
// __VERIFIER_make_nondet to havoc its value, and loads it before I. Returns the
// load instuction.
Value *KInductionPass::emitNondetValue(Type *type, Instruction *I,
                                       StringRef name = "nondet") {
  Function *F = I->getParent()->getParent();
  LLVMContext &Ctx = F->getContext();
  IRBuilder<> IRB(Ctx);
  IRB.SetInsertPoint(I);
  AllocaInst *allocaInst = IRB.CreateAlloca(type, nullptr);
  createHavocCall(allocaInst, I, name);
  return IRB.CreateLoad(type, allocaInst, name);
}

bool isVerifierAssert(Function *call) {
  return call->getName() == "__VERIFIER_assert";
}

/// Split all of the edges from inside the loop to their exit blocks.
/// Update the appropriate Phi nodes as we do so.
void splitExitEdges(Loop *L, const SmallVectorImpl<BasicBlock *> &ExitBlocks,
                    DominatorTree *DT, LoopInfo *LI) {
  for (unsigned I = 0, E = ExitBlocks.size(); I != E; ++I) {
    BasicBlock *ExitBlock = ExitBlocks[I];
    SmallVector<BasicBlock *, 4> Preds(predecessors(ExitBlock));

    // Although SplitBlockPredecessors doesn't preserve loop-simplify in
    // general, if we call it on all predecessors of all exits then it does.
    BasicBlock *BB = SplitBlockPredecessors(ExitBlock, Preds, ".lcssa", DT, LI, nullptr,
                           /*PreserveLCSSA*/ true);
  }
}

/// Emit a conditional branch on two values if LIC == Val, branch to TrueDst,
/// otherwise branch to FalseDest. Insert the code immediately before OldBranch
/// and remove (but not erase!) it from the function.
void KInductionPass::emitPreheaderBranchOnCondition(Value *LIC, Constant *Val,
                                                    BasicBlock *TrueDest,
                                                    BasicBlock *FalseDest,
                                                    BranchInst *OldBranch) {
  assert(OldBranch->isUnconditional() && "Preheader is not split correctly");
  assert(TrueDest != FalseDest && "Branch targets should be different");

  // Insert a conditional branch on LIC to the two preheaders.
  Value *BranchVal = LIC;
  if (!isa<ConstantInt>(Val) ||
      Val->getType() != Type::getInt1Ty(LIC->getContext()))
    BranchVal = new ICmpInst(OldBranch, ICmpInst::ICMP_EQ, LIC, Val);

  // Old branch will be removed, so save its parent and successor to update the
  // DomTree.
  auto *OldBranchSucc = OldBranch->getSuccessor(0);
  auto *OldBranchParent = OldBranch->getParent();

  // Insert the new branch.
  // BranchInst *BI =
  IRBuilder<>(OldBranch).CreateCondBr(BranchVal, TrueDest, FalseDest);

  // Remove the old branch so there is only one branch at the end. This is
  // needed to perform DomTree's internal DFS walk on the function's CFG.
  OldBranch->removeFromParent();

  // Inform the DT about the new branch.
  if (DT) {
    // First, add both successors.
    SmallVector<DominatorTree::UpdateType, 3> Updates;
    if (TrueDest != OldBranchSucc)
      Updates.push_back({DominatorTree::Insert, OldBranchParent, TrueDest});
    if (FalseDest != OldBranchSucc)
      Updates.push_back({DominatorTree::Insert, OldBranchParent, FalseDest});
    // If both of the new successors are different from the old one, inform the
    // DT that the edge was deleted.
    if (OldBranchSucc != TrueDest && OldBranchSucc != FalseDest) {
      Updates.push_back(
          {DominatorTree::Delete, OldBranchParent, OldBranchSucc});
    }

    DT->applyUpdates(Updates);
  }

  // If either edge is critical, split it. This helps preserve LoopSimplify
  // form for enclosing loops.
  // auto Options = CriticalEdgeSplittingOptions(DT, LI).setPreserveLCSSA();
  // SplitCriticalEdge(BI, 0, Options);
  // SplitCriticalEdge(BI, 1, Options);
}

/// Clones the given loop and inserts a conditional branch
/// that selects between the original loop and the cloned copy. Returns a
/// pointer to the newly created cloned loop. The original loop and the clone
/// will both exist in the function, and a conditional branch will determine
/// which one is executed based on the given condition Cond: the new clone is
/// executed if Cond evaluates to true; otherwise, the original loop is
/// executed.
Loop *KInductionPass::cloneLoopWithCondition(Loop *L, Value *Cond) {
  auto *Header = L->getHeader();
  auto *Preheader = L->getLoopPreheader();
  Function *F = Header->getParent();
  LLVMContext &Ctx = F->getContext();
  LoopBlocks.clear();

  // Insert new preheader so that we can branch from the old one.
  BasicBlock *NewPreheader = SplitEdge(Preheader, Header, DT, LI);
  LoopBlocks.push_back(NewPreheader);

  // We want the loop to come after the preheader, but before the exit blocks.
  llvm::append_range(LoopBlocks, L->blocks());

  // Insert new exit blocks for the cloned loop.
  SmallVector<BasicBlock *, 8> ExitBlocks;
  L->getUniqueExitBlocks(ExitBlocks);
  splitExitEdges(L, ExitBlocks, DT, LI);

  // The exit blocks may have been changed due to edge splitting, recompute.
  ExitBlocks.clear();
  L->getUniqueExitBlocks(ExitBlocks);
  append_range(LoopBlocks, ExitBlocks);

  // Clone the loop.
  NewBlocks.clear();
  NewBlocks.reserve(LoopBlocks.size());
  ValueToValueMapTy VMap;  // Keep the BB mapping from original to clone.
  for (unsigned I = 0, E = LoopBlocks.size(); I != E; ++I) {
    BasicBlock *NewBB = CloneBasicBlock(LoopBlocks[I], VMap, ".kind-clone", F);

    NewBlocks.push_back(NewBB);
    VMap[LoopBlocks[I]] = NewBB;
  }

  // Splice the newly inserted blocks into the function right before the
  // original preheader.
  F->getBasicBlockList().splice(NewPreheader->getIterator(),
                                F->getBasicBlockList(),
                                NewBlocks[0]->getIterator(), F->end());

  // Create a new Loop object for the clone.
  Loop *NewLoop = cloneLoop(L, L->getParentLoop(), VMap, LI, LPM);

  Loop *ParentLoop = L->getParentLoop();
  if (ParentLoop) {
    // Make sure to add the cloned preheader and exit blocks to the parent loop
    // as well.
    ParentLoop->addBasicBlockToLoop(NewBlocks[0], *LI);
  }

  for (unsigned EBI = 0, EBE = ExitBlocks.size(); EBI != EBE; ++EBI) {
    BasicBlock *NewExit = cast<BasicBlock>(VMap[ExitBlocks[EBI]]);
    // The new exit block should be in the same loop as the old one.
    if (Loop *ExitBBLoop = LI->getLoopFor(ExitBlocks[EBI]))
      ExitBBLoop->addBasicBlockToLoop(NewExit, *LI);

    assert(NewExit->getTerminator()->getNumSuccessors() == 1 &&
           "Exit block should have been split to have one successor!");
    BasicBlock *ExitSucc = NewExit->getTerminator()->getSuccessor(0);

    // If the successor of the exit block had PHI nodes, add an entry for
    // NewExit.
    for (PHINode &PN : ExitSucc->phis()) {
      Value *V = PN.getIncomingValueForBlock(ExitBlocks[EBI]);
      ValueToValueMapTy::iterator It = VMap.find(V);
      if (It != VMap.end()) V = It->second;
      PN.addIncoming(V, NewExit);
    }

    if (LandingPadInst *LPad = NewExit->getLandingPadInst()) {
      PHINode *PN = PHINode::Create(LPad->getType(), 0, "",
                                    &*ExitSucc->getFirstInsertionPt());

      for (BasicBlock *BB : predecessors(ExitSucc)) {
        LandingPadInst *LPI = BB->getLandingPadInst();
        LPI->replaceAllUsesWith(PN);
        PN->addIncoming(LPI, BB);
      }
    }
  }

  // Rewrite the code to refer to itself.
  for (unsigned NBI = 0, NBE = NewBlocks.size(); NBI != NBE; ++NBI) {
    for (Instruction &I : *NewBlocks[NBI]) {
      RemapInstruction(&I, VMap,
                       RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
    }
  }

  // Rewrite the original preheader to select between the original loop (false) and the clone (true).
  BranchInst *OldBR = cast<BranchInst>(Preheader->getTerminator());
  assert(OldBR->isUnconditional() && OldBR->getSuccessor(0) == LoopBlocks[0] &&
         "Preheader splitting did not work correctly!");
  emitPreheaderBranchOnCondition(Cond, ConstantInt::getTrue(Ctx), NewBlocks[0],
                                 LoopBlocks[0], OldBR);

  // The OldBr was replaced by a new one and removed (but not erased) by
  // emitPreheaderBranchOnCondition. It is no longer needed, so delete it.
  delete OldBR;

  return NewLoop;
}

// Bounds loop by record loop trip count and force quit before the k-th
// iteration.
void KInductionPass::boundLoop(Loop *L) {
  assert(L->isLoopSimplifyForm() && "Loop is not in simplified form!");
  auto *Counter = dyn_cast<PHINode>(emitTripCount(L));

  BasicBlock *Header = L->getHeader();
  LLVMContext &Ctx = Header->getContext();
  IRBuilder<> B(Ctx);

  // Check whether counter >= K - 1. If this is true, we need to abort
  // immediately after loop header. Caution: this may change Latch if Header ==
  // Latch.
  B.SetInsertPoint(Header->getTerminator());
  Value *CmpInst =
      B.CreateICmpEQ(Counter, ConstantInt::get(Type::getInt32Ty(Ctx), K - 1));

  // Create a new unreachable exit basic block. After executing loop header k
  // times, control flow will be directed to that block.
  Instruction *UnreachableInst = SplitBlockAndInsertIfThen(
      CmpInst, Header->getTerminator(), true, nullptr, DT, LI);

  // Add __VERIFIER_assume(0) before the unreachable instruction to make it
  // truly unreachable.
  emitVerifierCall("__VERIFIER_assume", Type::getVoidTy(Ctx),
                   {ConstantInt::get(Type::getInt1Ty(Ctx), 0)},
                   UnreachableInst);
}

/// Transforms the given loop into an over-approximating abstraction of all
/// paths with trip count >= K.
void KInductionPass::abstractLoop(Loop *L) {
  assert(L->isLoopSimplifyForm() && "Loop is not in simplified form!");

  auto *Header = L->getHeader();
  auto *Preheader = L->getLoopPreheader();
  auto *Latch = L->getLoopLatch();
  LLVMContext &Ctx = Header->getContext();
  IRBuilder<> B(Ctx);

  // If a phi node in header have both incoming edge from Latch(update) and
  // Preheader (init), havoc the init value.
  Instruction *preheaderTermInst = Preheader->getTerminator();
  for (auto &phiNode : Header->phis()) {
    if (phiNode.getBasicBlockIndex(Preheader) != -1 &&
        phiNode.getBasicBlockIndex(Latch) != -1) {
      Value *havocInst = emitNondetValue(phiNode.getType(), preheaderTermInst,
                                         phiNode.getName().str() + ".havoc");
      phiNode.setIncomingValueForBlock(Preheader, havocInst);
    }
  }

  // We also havoc all memory objects that may be modified in the loop.
  // FIXME: For now we only deal with store instructions of which the operand
  // is defined in a basic block that dominates the preheader (so we can havoc
  // it there).
  std::set<Value *> ptrs;
  for (auto BB : L->getBlocks()) {
    for (auto &I : *BB) {
      if (auto *storeInst = dyn_cast<StoreInst>(&I)) {
        Value *ptr = storeInst->getPointerOperand();
        ptrs.insert(ptr);
      }
    }
  }
  for (auto ptr : ptrs) {
    if (auto *inst = dyn_cast<Instruction>(ptr)) {
      BasicBlock *defBB = inst->getParent();
      if (DT->dominates(defBB, Preheader)) {
        createHavocCall(ptr, preheaderTermInst, ptr->getName().str() + ".kind");
      }
    } else if (auto *arg = dyn_cast<Argument>(ptr)) {
      createHavocCall(ptr, preheaderTermInst, ptr->getName().str() + ".kind");
    } else if (auto *global = dyn_cast<GlobalVariable>(ptr)) {
      createHavocCall(ptr, preheaderTermInst, ptr->getName().str() + ".kind");
    } else {
      dbgs() << "Unable to handle store to pointer " << ptr->getName()
             << ", result may be unsound!\n";
    }
  }

  //FIXME: We also need to handle function calls.

  // Done havocking. Add trip counter now.
  auto *Counter = dyn_cast<PHINode>(emitTripCount(L));

  // We replace all calls __VERIFIER_assert(cond) with
  // __VERIFIER_assert_or_assume(cond, flag), where flag is true iff trip count
  // == K - 1.
  B.SetInsertPoint(Header->getFirstNonPHI());
  Value *Flag = B.CreateICmpEQ(
      Counter, ConstantInt::get(Type::getInt32Ty(Ctx), K - 1), L->getName() + ".flag");
  SmallVector<CallInst *> callInsts;
  for (auto BB : L->getBlocks()) {
    for (auto &I : *BB) {
      if (CallInst *CI = dyn_cast<CallInst>(&I)) {
        Function *calledFunc = CI->getCalledFunction();
        if (calledFunc && isVerifierAssert(calledFunc)) {
          // Replace the call to oldFunc with a call to newFunc
          callInsts.push_back(CI);
        }
      }
    }
  }
  for (CallInst *CI : callInsts) {
    SmallVector<Value *> Args = {CI->getArgOperand(0), Flag};
    auto *newCI = emitVerifierCall("__VERIFIER_assert_or_assume",
                                   Type::getVoidTy(Ctx), Args, CI);
    CI->replaceAllUsesWith(newCI);
    CI->eraseFromParent();
  }

  // To assume the loop exits exactly after K iterations, we add
  // __VERIFIER_assume(flag) calls to all exit blocks, and we abort after
  // passing the backedge for the K-th time. Caution: this may change Latch if
  // Header == Latch.
  // SmallVector<BasicBlock *> ExitBlocks;
  // L->getUniqueExitBlocks(ExitBlocks);
  // for (auto BB : ExitBlocks) {
  //   emitVerifierCall("__VERIFIER_assume", Type::getVoidTy(Ctx), {Flag},
  //                    BB->getFirstNonPHI());
  // }

  B.SetInsertPoint(Header->getTerminator());
  Value *SGTBoundInst =
      B.CreateICmpEQ(Counter, ConstantInt::get(Type::getInt32Ty(Ctx), K));

  Instruction *UnreachableInst = SplitBlockAndInsertIfThen(
      SGTBoundInst, Header->getTerminator(), true, nullptr, DT, LI);
  emitVerifierCall("__VERIFIER_assume", Type::getVoidTy(Ctx),
                   {ConstantInt::get(Type::getInt1Ty(Ctx), 0)},
                   UnreachableInst);
}

bool KInductionPass::runOnLoop(Loop *L, LPPassManager &LPMRef) {
  if (K == 0) return false;

  // Avoid cloning the same loop multiple times.
  if (L->getName().contains(".kind-clone")) return false;

  LPM = &LPMRef;
  DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  formLCSSA(*L, *DT, LI, nullptr);
  assert(L->isLoopSimplifyForm() && "Loop not simplified!");
  if (!L->isSafeToClone()) {
    dbgs() << "Loop " << L->getName() << " is unsafe to clone. Skip.\n";
    return false;
  }

  // Insert branch condition.
  auto *Preheader = L->getLoopPreheader();
  auto &Ctx = Preheader->getContext();
  Value *NondetCond =
      emitNondetValue(Type::getInt1Ty(Ctx), Preheader->getTerminator(),
                      L->getName().str() + ".kind");

  // Clone the loop
  Loop *NewLoop = cloneLoopWithCondition(L, NondetCond);

  // Transform the loops
  boundLoop(L);
  abstractLoop(NewLoop);

  return true;
}
}  // namespace
