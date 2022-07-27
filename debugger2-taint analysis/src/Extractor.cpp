#include "Extractor.h"

#include "llvm/IR/Instruction.h"

void Extractor::addDef(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (InstMap.find(X) == InstMap.end())
    return;
  DefFile << toString(X) << "\t" << toString(L) << "\n";
}

void Extractor::addUse(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  UseFile << toString(X) << "\t" << toString(L) << "\n";
}

void Extractor::addDiv(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  DivFile << toString(X) << "\t" << toString(L) << "\n";
}

void Extractor::addTaint(const InstMapTy &InstMap, Instruction *L) {
  TaintFile << toString(L) << "\n";
}

void Extractor::addSanitizer(const InstMapTy &InstMap, Instruction *L) {
  SanitizerFile << toString(L) << "\n";
}

void Extractor::addNext(const InstMapTy &InstMap, Instruction *X,
                        Instruction *Y) {
  NextFile << toString(X) << "\t" << toString(Y) << "\n";
};

/**
 * @brief Collects Datalog facts for each instruction to corresponding facts
 * file.
 */
void Extractor::extractConstraints(const InstMapTy &InstMap, Instruction *I) {
  /**
   * For each predecessor P of instruction I,
   *       add a new fact in the `next` relation.
   */
  auto predecessors = getPredecessors(I);
  for(auto p: predecessors){
    addNext(InstMap, p, I);
  }
  
  /**
   *   For each of the instruction add appropriate facts:
   *     Add `def` and `use` relations.
   *   For `BinaryOperator` instructions involving division:
   *     Add a fact for the `div` relation.
   *   For `CallInst` instructions:
   *     Add a `def` relation only if it returns a non-void value.
   *     If its a call to tainted input,
   *       Add appropriate fact to `taint` relation.
   *     If its a call to sanitize,
   *       Add appropriate fact to `sanitizer` relation.
   *
   * NOTE: Many Values may be used in a single instruction,
   *       but at most one Value can be defined in one instruction.
   * NOTE: use `isTaintedInput()` and `isSanitizer()` function
   *       to check if a particular CallInst is a tainted input
   *       or sanitize respectively.
   */

  if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
    // do nothing, alloca is just a declaration.
  } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    //Extract facts from StoreInst
      addUse(InstMap, SI->getValueOperand(), SI);
      addDef(InstMap, SI->getPointerOperand(), SI);

  } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    // Extract facts from LoadInst
    addUse(InstMap, LI->getPointerOperand(), LI);
    addDef(InstMap, LI, LI);
  } 
  else if (BinaryOperator *BI = dyn_cast<BinaryOperator>(I)) {
    // Extract facts from BinaryOperation
    if((BI->getOpcode() == Instruction::SDiv) || (BI->getOpcode() == Instruction::UDiv)){
      addDiv(InstMap, BI->getOperand(1), BI);
    }
    addDef(InstMap, BI, BI);
    addUse(InstMap, BI->getOperand(0), BI);
    addUse(InstMap, BI->getOperand(1), BI);

  } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
    // Extract facts from CallInst
    if(CI->getType()->isIntegerTy()){
      addDef(InstMap, CI, CI);
    if(isTaintedInput(CI)){
      addTaint(InstMap, CI);
    }
    if(isSanitizer(CI)){
      addSanitizer(InstMap, CI);
    }
     //CHECK  if all the args are ints
    //iterate through args
    auto argLst = CI->args();
    for(auto arg = argLst.begin(); arg != argLst.end(); ++arg){
      addUse(InstMap, arg->get(), CI);
    }
  }
  } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
    // Extract facts from CastInst
    addDef(InstMap, CI, CI);
    addUse(InstMap, CI->getOperand(0), CI);
  } else if (CmpInst *CI = dyn_cast<CmpInst>(I)) {
    // Extract facts from CmpInst
    addDef(InstMap, CI, CI);
    addUse(InstMap, CI->getOperand(0), CI);
    addUse(InstMap, CI->getOperand(1), CI);
  }
}
