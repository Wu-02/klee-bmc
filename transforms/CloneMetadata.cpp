//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.

#include <cassert>
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/DebugInfoMetadata.h>

using namespace llvm;

/** Clone metadata from one instruction to another.
 *
 * @param i1 the first instruction
 * @param i2 the second instruction without any metadata
 */
bool CloneMetadata(const llvm::Instruction *i1, llvm::Instruction *i2)
{
    if (i1->hasMetadata()) {
        i2->setDebugLoc(i1->getDebugLoc());
        return true;
    }

    return false;
}

