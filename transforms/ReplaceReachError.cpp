//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.

#include <cassert>
#include <set>
#include <vector>

#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#if LLVM_VERSION_MAJOR >= 4 || \
    (LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR >= 5)
#include "llvm/IR/InstIterator.h"
#else
#include "llvm/Support/InstIterator.h"
#endif
#include <llvm/IR/DebugInfoMetadata.h>

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

llvm::cl::opt<std::string> assert_fn(
    "replace-asserts-fn",
    llvm::cl::desc("Insert a function that marks the header of the loop"),
    llvm::cl::init("__assert_fail"));

bool CloneMetadata(const llvm::Instruction *i1, llvm::Instruction *i2);

namespace {

class ReplaceAsserts : public FunctionPass {
 public:
  static char ID;

  ReplaceAsserts() : FunctionPass(ID) {}

  virtual bool runOnFunction(Function &F);
};

bool ReplaceAsserts::runOnFunction(Function &F) {
  bool modified = false;
  Module *M = F.getParent();
  Function *ver_err = nullptr;

  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E;) {
    Instruction *ins = &*I;
    ++I;
    if (CallInst *CI = dyn_cast<CallInst>(ins)) {
      if (CI->isInlineAsm()) continue;

#if LLVM_VERSION_MAJOR >= 8
      const Value *val = CI->getCalledOperand()->stripPointerCasts();
#else
      const Value *val = CI->getCalledValue()->stripPointerCasts();
#endif
      const Function *callee = dyn_cast<Function>(val);
      if (!callee || callee->isIntrinsic()) continue;

      assert(callee->hasName());
      StringRef name = callee->getName();
      if (!name.equals("reach_error")) continue;

      if (!ver_err) {
        LLVMContext &Ctx = M->getContext();
        AttrBuilder B(Ctx);
        // Not supported in llvm-14
        // B.addAttribute(Attribute::Leaf);
        // B.addAttribute(Attribute::NoThrow);
        B.addAttribute(Attribute::NoReturn);
        AttributeList as =
            AttributeList::get(Ctx, AttributeList::FunctionIndex, B);
        auto C = M->getOrInsertFunction(
            "__assert_fail", as, Type::getVoidTy(Ctx), Type::getInt8PtrTy(Ctx),
            Type::getInt8PtrTy(Ctx), Type::getInt32Ty(Ctx),
            Type::getInt8PtrTy(Ctx)
#if LLVM_VERSION_MAJOR < 5
                ,
            nullptr
#endif
        );
#if LLVM_VERSION_MAJOR >= 9
        ver_err = cast<Function>(C.getCallee()->stripPointerCasts());
#else
        ver_err = cast<Function>(C);
#endif
      }

      // Just pass null pointers since the program is going to abort anyway
      auto CI2 = CallInst::Create(
          ver_err, {ConstantPointerNull::get(Type::getInt8PtrTy(M->getContext())),
                    ConstantPointerNull::get(Type::getInt8PtrTy(M->getContext())),
                    ConstantInt::get(Type::getInt32Ty(M->getContext()), 0),
                    ConstantPointerNull::get(Type::getInt8PtrTy(M->getContext()))});
      CloneMetadata(CI, CI2);

      CI2->insertAfter(CI);
      CI->eraseFromParent();

      modified = true;
    }
  }
  return modified;
}

static RegisterPass<ReplaceAsserts> RASS(
    "replace-reach-error",
    "Replace reach_error calls with calls to __assert_fail (sv-comp hack)");
char ReplaceAsserts::ID;
}  // namespace
