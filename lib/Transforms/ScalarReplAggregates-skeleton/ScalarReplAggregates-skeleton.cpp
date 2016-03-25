//===- ScalarReplAggregates.cpp - Scalar Replacement of Aggregates --------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This transformation implements the well known scalar replacement of
// aggregates transformation.  This xform breaks up alloca instructions of
// structure type into individual alloca instructions for
// each member, when legal.  Then, if legal, it transforms the individual
// alloca instructions into nice clean scalar SSA form.
//
// This combines a simple SRoA algorithm with Mem2Reg because they
// often interact, especially for C++ programs.  As such, iterating between
// SRoA and Mem2Reg until we run out of things to promote works well.
//
//===----------------------------------------------------------------------===//
/*
#include "llvm/Transforms/Scalar.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Pass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
//#include "llvm/Target/TargetData.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
*/

#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/Loads.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"

using namespace llvm;
#define DEBUG_TYPE "ScalarReplAggregates"
#define WL_SIZE 64

STATISTIC(NumExpanded,  "Number of aggregate allocas broken up");
STATISTIC(NumPromoted,  "Number of scalar allocas promoted to register");

namespace {
  //--------------------------------------------------------------------------//
  // class SROA: Scalar Replacement of Aggregates function pass.
  // 
  // The main entry point is runOnFunction.
  // The pass is registered using the declaration of a static global
  // variable (X) below.
  //--------------------------------------------------------------------------//
  
  struct SROA : public FunctionPass {
    static char ID;             // Pass identification
    
    SROA() : FunctionPass(ID) { }

    // Entry point for the overall scalar-replacement pass
    bool runOnFunction(Function &F);

    // Promotes allocas to registers, which can enable more scalar replacement
    bool performPromotion(Function &F);

    // Entry point for the scalar-replacement transformation itself
    bool performScalarRepl(Function &F);

    // getAnalysisUsage - This pass does not require any passes, but we know it
    // will not alter the CFG, so say so.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<AssumptionCacheTracker>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.setPreservesCFG();
    }

  private:
    // Add fields and helper functions for this pass here.
    bool checkGEPU1Format(AllocaInst *Alloca);
  };
}

//--------------------------------------------------------------------------//
// Register the pass so it is accessible from the command line,
// via the pass manager.
//--------------------------------------------------------------------------//
char SROA::ID = 0;
static RegisterPass<SROA> X("scalarrepl-assn2",
			    "EECE571P Scalar Replacement of Aggregates", false, false);

//----------------------------------------------------------------------------//
// 
// Function runOnFunction:
// Entry point for the overall ScalarReplAggregates function pass.
// This function is provided to you.
// 
//----------------------------------------------------------------------------//

bool SROA::runOnFunction(Function &F) {

  DEBUG(errs() << "\nINFO   " << __func__ << "(): *** Check function: "<< F.getName() << " ***\n\n");
  /* do mem2reg pass first for each function */
  bool Changed = performPromotion(F);

  while (1) {
    bool LocalChange = performScalarRepl(F);
    if (!LocalChange) break;   // No need to repromote if no scalarrepl
    Changed = true;
    LocalChange = performPromotion(F);
    if (!LocalChange) break;   // No need to re-scalarrepl if no promotion
  }

  return Changed;
}


//----------------------------------------------------------------------------//
// Function performPromotion:
// Promote allocas to registers, which can enable more scalar replacement.
//----------------------------------------------------------------------------//
bool SROA::performPromotion(Function &F) {
  std::vector<AllocaInst*> Allocas;
  /* doesn't seem to be used anywhere */
  //const DataLayout &DL = F.getParent()->getDataLayout();
  /*
  // clean up the code a bit
  DominatorTree *DT = nullptr;
    DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  */
  DominatorTree &DT =
      getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  AssumptionCache &AC =
      getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

  BasicBlock &BB = F.getEntryBlock();  // Get the entry node for the function
  DIBuilder DIB(*F.getParent(), /*AllowUnresolved*/ false);
  bool Changed = false;
  //SmallVector<Instruction*, 64> Insts;
  while (1) {
    //DEBUG(errs() << "\n");
    Allocas.clear();

    // Find allocas that are safe to promote, by looking at all instructions in
    // the entry node;

    /*
     * mem2reg is alloca-driven: it looks for allocas and if it can handle them, it promotes them.
     * It does not apply to global variables or heap allocations.
     *
     * mem2reg only looks for alloca instructions in the entry block of the function.
     * Being in the entry block guarantees that the alloca is only executed once,
     * which makes analysis simpler.
     *
     * mem2reg only promotes allocas whose uses are direct loads and stores. If the address
     * of the stack object is passed to a function, or if any funny pointer arithmetic is
     * involved, the alloca will not be promoted.
     *
     * mem2reg only works on allocas of first class values (such as pointers, scalars and
     * vectors), and only if the array size of the allocation is 1 (or missing in the .ll
     * file). mem2reg is not capable of promoting structs or arrays to registers. Note that
     * the “scalarrepl” pass is more powerful and can promote structs, “unions”, and arrays in many cases.
     *
     */
    for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I) {
      if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {       // Is it an alloca?
        DEBUG(errs() << "INFO   " << __func__ << "(): Alloca found: "<< *AI << " ");
        if (isAllocaPromotable(AI)) {
          DEBUG(errs() << "Promotable [YES]\n");
          Allocas.push_back(AI);
        } else {
          DEBUG(errs() << "Promotable [NO]\n");
        }
      }
    }

    if (Allocas.empty()) break;

    //PromoteMemToReg(Allocas, *DT, nullptr, &AC);
    PromoteMemToReg(Allocas, DT, nullptr, &AC);
    NumPromoted += Allocas.size();
    DEBUG(errs() << "INFO   " << __func__ << "(): mem2reg NumPromoted: " << NumPromoted << "\n");
    Changed = true;
  }

  return Changed;
}

//----------------------------------------------------------------------------//
// Function performScalarRepl:
// Entry point for a single pass of the scalar-replacement transformation itself.
//----------------------------------------------------------------------------//

bool SROA::performScalarRepl(Function &F) {

  bool changed = false;
  /* define a small set of working list */
  //SmallSetVector<AllocaInst *, WL_SIZE> workList;
  //SmallSetVector<Value *, WL_SIZE> oldInst;
  std::vector<AllocaInst*> workList;
  std::vector<Value*> oldInst;


  /* get the entry node of the function */
  BasicBlock &BB = F.getEntryBlock();
  //DEBUG(errs() << "\n");
  /* loop through each basic block; identify each Alloca; save to work list */
  for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I) {
    if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
      DEBUG(errs() << "INFO   "<< __func__ << "() Alloca found: " << *AI << "\n");
      workList.push_back(AI);
    }
  }

  //DEBUG(errs() << "\nWorkList size: " << WorkList.size() << "\n");

  /* loop through work list */
  while (!workList.empty()) {

    AllocaInst *AI = workList.back();
    workList.pop_back();

    /* only cares about structure Alloca */
    if (!isa<StructType>(AI->getAllocatedType())) {
      DEBUG(errs() << "INFO   " << __func__ << "(): Non structure Alloca found: " << *AI <<" [SKIP]\n");
      continue;
    }

    if (!checkGEPU1Format(AI)) {
      /* bypass the transformation if GEP format is illegal */
      continue;
    }

    DEBUG(errs() << "\nINFO   " << __func__ << "(): Promotable Alloca found: " << *AI <<"\n");

    std::vector<AllocaInst*> newAllocas;

    /* make sure the alloca instr is allocated with structure type; although checked already */
    if (StructType *structT = dyn_cast<StructType>(AI->getAllocatedType())) {
      newAllocas.reserve(structT->getNumContainedTypes());
      //newAllocas.reserve(structT->getNumElements());
      DEBUG(errs() << "DEBUG  " << __func__ << "(): Number of contained types: " \
          << structT->getNumContainedTypes() <<"\n");
      /* nested structure is one of contained type, so can't simply use getElements() */

      /* loop through each structure element then create new Alloca with its corresponding type*/
      for (int I = 0, E = structT->getNumContainedTypes(); I != E ; I++) {
        /* create the element Alloca for this type */
        AllocaInst *newAI = new AllocaInst(structT->getContainedType(I), nullptr,
                                            AI->getAlignment(),
                                            AI->getName() + ".SROA." + Twine(I), AI);
        DEBUG(errs() << "DEBUG  " << __func__ << "(): Create new Alloca: " << *newAI << "\n");
        /* push to work list */
        newAllocas.push_back(newAI);
        /* handle nested structure */
        workList.push_back(newAI);
      }
    } else {
      DEBUG(errs() << "ERROR  " << __func__ << "(): Not a structure type!\n");
    }

    /* loop through each GEP instr and perform replacement */
    for (Value::user_iterator I = AI->user_begin(), E = AI->user_end(); I != E; ++I) {
      if (GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(*I)) {
        /* find the corresponding index in the work list; checking bounds*/
        uint64_t index = cast<ConstantInt>(gepInst->getOperand(2))->getLimitedValue();

        if (index >= newAllocas.size()) {
          assert(0 && "Alloca instruction list size exceeds...");
        }

        AllocaInst *newAI = newAllocas[index];
        Value *newValue = newAI;

        DEBUG(errs() << "INFO   Replace GEP instr (U1): " << *gepInst \
                     << "\n\t   with scalar Alloca: " << *newAI << "\n");

        /* replace all uses of this instruction with new Alloca */
        gepInst->replaceAllUsesWith(newValue);

        //DEBUG(errs() << "\nDEBUG  " << __func__ << "(): Old Alloca to be cleaned up: " << *gepInst <<"\n");

        /* store obsoleted instr */
        oldInst.push_back(gepInst);
      } else {
          DEBUG(errs() << "ERROR  " << __func__ << "(): Not a GEP instruction!\n");
      }
    }

    /* erase obsoleted GEP inst */
    while(!oldInst.empty()) {
      Instruction *Inst = cast<Instruction>(oldInst.back());
      DEBUG(errs() << "DEBUG  " << __func__ << "(): Erase " << *Inst <<"\n");
      oldInst.pop_back();
      Inst->eraseFromParent();
    }

    /* erase obsoleted struct Alloca from BB as well */
    DEBUG(errs() << "DEBUG  " << __func__ << "(): Erase " << *AI <<"\n");
    AI->eraseFromParent();

    NumExpanded++;
    changed = true;
  }
  
  return changed;
}

/*
 * A alloca instruction can be eliminated if the resulting pointer ptr is used only in the following way:
 * (U1) In a getelementptr instruction that satisfies both these conditions:
 *      It is of the form: getelementptr ptr, 0, constant
 *      The result of the getelementptr is only used in instructions of type U1, or as the pointer argument
 *      of a load or store instruction, i.e., the pointer stored into (not the value being stored).
*/
bool SROA::checkGEPU1Format(AllocaInst *Alloca)
{
  //DEBUG(errs() << "\n");
  //int count = 0;
  /* go through the user-list of each Alloca instruction to find related GEP instr */
  for (Value::user_iterator I = Alloca->user_begin(), E = Alloca->user_end(); I != E; ++I) {
    //DEBUG(errs() << "count = " << count << "\n");
    //DEBUG(errs() << "\nDEBUG " << __func__ << "(): >>> dump: " << Alloca->getOperandList() << "\n");
    if (GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(*I)) {
      DEBUG(errs() <<"INFO   " << __func__ << "(): found GEP used by Alloca: " << *gepInst <<"\n");

      if (gepInst->getNumIndices() != 2) {
        DEBUG(errs() << "ERROR  " << __func__ << "(): condition mismatched, only 2 indices allowed [ " << gepInst << " ]\n");
        return false;
      }
      if (!isa<PointerType>(gepInst->getPointerOperandType())) {
        DEBUG(errs() << "ERROR  " << __func__ << "(): condition mismatched, first operand must be a pointer [ " << gepInst << " ]\n");
        return false;
      }
      if (!(cast<Constant>(gepInst->getOperand(1)))->isZeroValue() ){
        DEBUG(errs() << "ERROR  " << __func__ << "(): condition mismatched, first index must be zero [ " << gepInst << " ]\n");
        return false;
      }
      if (!isa<Constant>(gepInst->getOperand(2))) {
        DEBUG(errs() << "ERROR  " << __func__ << "(): condition mismatched, second index must be a constant [ " << gepInst << " ]\n");
        return false;
      }

    } else {
      /* A very important case to catch! */
      DEBUG(errs() << "INFO   " << __func__ << "(): unfortunately, the user of this alloca is not ONLY a GEP\n");
      return false;
    }
    //count++;
  }

  return true;
}
