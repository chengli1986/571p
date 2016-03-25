//===-- BranchInstCount.cpp - Collects the count of branch instructions ---===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass collects the count of branch instructions and reports them
//
//===----------------------------------------------------------------------===//


/*
 * opt -debug -load ~/Documents/EECE571P/llvm-local/build/lib/libAssign1.so -branchinstcount-assn1 -stats schedule2.ll
 */

#include "llvm/Analysis/Passes.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/IR/Instructions.h"

using namespace llvm;

#define DEBUG_TYPE "BranchInstCount"

STATISTIC(NumCondBranch, "Number of conditional branches in the program");
STATISTIC(NumUncondBranch, "Number of unconditional branches in the program");
STATISTIC(NumEqBranch, "Number of conditional branches whose comparison type "
                       "is equal test");
STATISTIC(NumGTBranch, "Number of conditional branches whose comparison type "
                        "is greater than test");
STATISTIC(NumLTBranch, "Number of conditional branches whose comparison type "
                        "is less than test");

/* the following is for DEBUG purpose ONLY */
STATISTIC(NumNEqBranch, "Number of conditional branches whose comparison type "
                       "is not equal test");
STATISTIC(NumGEBranch, "Number of conditional branches whose comparison type "
                        "is greater than and equal test");
STATISTIC(NumLEBranch, "Number of conditional branches whose comparison type "
                        "is less than and equal test");

                        
namespace {
  class BranchInstCount : public FunctionPass {
  
  public:
    static char ID;
    BranchInstCount() : FunctionPass(ID) {  }

    virtual bool runOnFunction(Function &F);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
    }
  };
}

char BranchInstCount::ID = 0;
static RegisterPass<BranchInstCount> X ("branchinstcount-assn1",
                "Counts the various types of branch instructions", false, true);

// This is the main Analysis entry point for a function.
bool BranchInstCount::runOnFunction(Function &F) {
   // Add your analysis here
   // You are free to add new methods to the class

   Value *brInstCC;
   Value *phiNodeCC;
   
   /* iterator over each function */
   for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      /* iterator over each basic block */
      for (BasicBlock::iterator i = b->begin(), ie = b->end(); i != ie; ++i) {
         /* check for instance of branch instruction */
         if (BranchInst* branchInst = dyn_cast<BranchInst> (&*i)) {
            /* conditional branch case */
            if (branchInst->isConditional()) {
               /* increment conditional branch instruction within this basic block */
               NumCondBranch++;
               //check the condition used for the conditional branch
               brInstCC = branchInst->getCondition();
               DEBUG(brInstCC->dump());
               //brInstCC->dump();
               /* dynamically cast branch condition Value to comparison instruction */
               if (CmpInst* cmpInst = dyn_cast<CmpInst> (brInstCC)) {
                  DEBUG(errs() << "cmpInstCC Code: " << cmpInst->getPredicate() << "\n");
                  /* fcmp types are missing 2!!! */
                  switch (cmpInst->getPredicate()) {
                     case CmpInst::ICMP_EQ:  // 32
                     case CmpInst::FCMP_OEQ: // 1
                     case CmpInst::FCMP_UEQ: // 9
                        NumEqBranch++;
                        break;
                     case CmpInst::ICMP_SGT: // 38
                     case CmpInst::ICMP_UGT: // 34
                     case CmpInst::FCMP_OGT: // 2
                     case CmpInst::FCMP_UGT: // 10
                        NumGTBranch++;
                        break;
                     case CmpInst::ICMP_SLT: // 40
                     case CmpInst::ICMP_ULT: // 36
                     case CmpInst::FCMP_OLT: // 4
                     case CmpInst::FCMP_ULT: // 12
                        NumLTBranch++;
                        break;
                     /* For DEBUG purpose ONLY */
                     case CmpInst::ICMP_NE:  // 33
                     case CmpInst::FCMP_ONE: // 6
                     case CmpInst::FCMP_UNE: // 14
                        NumNEqBranch++;
                        break;
                     case CmpInst::ICMP_UGE: // 35
                     case CmpInst::ICMP_SGE: // 39
                     case CmpInst::FCMP_OGE: // 3
                     case CmpInst::FCMP_UGE: // 11
                        NumGEBranch++;
                        break;
                     case CmpInst::ICMP_ULE: // 37
                     case CmpInst::ICMP_SLE: // 41
                     case CmpInst::FCMP_OLE: // 5
                     case CmpInst::FCMP_ULE: // 13
                        NumLEBranch++;
                        break;
                    default:
                        break;
                  }
               /* Phi node determines the branch cc */
               } else if (PHINode* phiNode = dyn_cast<PHINode> (brInstCC)) {
                  //DEBUG(errs() << "Phi node incoming value edges: " << phiNode->getNumIncomingValues() << "\n");
                  for (unsigned int i = 0; i < phiNode->getNumIncomingValues(); i++) {
                     phiNodeCC = phiNode->getIncomingValue(i);
                     //DEBUG(phiNodeCC->dump());
                     if (CmpInst* phiNodeCmpInst = dyn_cast<CmpInst> (phiNodeCC)) {
                        DEBUG(errs() << "phiNodeCC Code: " << phiNodeCmpInst->getPredicate() << "\n");
                        //DEBUG(errs() << "Phi node selects: " << *phiNodeCmpInst << "\n");
                        /* Phi node takes value #1 if label#1 is taken; otherwise the alternative; 
                           no GT or LT need to be considered */
                        if (phiNodeCmpInst->getPredicate() == CmpInst::ICMP_EQ) {
                           NumEqBranch++; 
                        } else if (phiNodeCmpInst->getPredicate() == CmpInst::ICMP_NE) {
                           NumNEqBranch++;
                        }
                     }
                  }
// well, the following is NOT working properly, but this is the main issue
// where the xor command is seriously missing...
               } else if (BinaryOperator* biOp = dyn_cast<BinaryOperator> (brInstCC)) {
                  DEBUG(errs() << "\n\n ISSUE: xor instruction is used to be the flag for next branch, this is the missing count when it comes up with 37/38...\n\n");
                  DEBUG(biOp->getOpcode());
#if 0
                  if (biOp->getOpcode == ) {
                     NumNEqBranch++;
                  } else {
                     NumEqBranch++;
                  }
#endif
               } // end of conditional branch if
            } else if (branchInst->isUnconditional()) {
               // the following IS WRONG... no condition can be get for unconditional branch, hahaha
               //branchInst->getCondition()->dump(); 
               NumUncondBranch++;
            } else {
               errs() << *branchInst << "Leftover branch instructions" << "\n";
               branchInst->dump();
            }
         }
      }
   }
   return false;
}
