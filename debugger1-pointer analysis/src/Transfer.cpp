#include "DivZeroAnalysis.h"
#include "Utils.h"

namespace dataflow {

/**
 * @brief Is the given instruction a user input?
 *
 * @param Inst The instruction to check.
 * @return true If it is a user input, false otherwise.
 */
bool isInput(Instruction *Inst) {
  if (auto Call = dyn_cast<CallInst>(Inst)) {
    if (auto Fun = Call->getCalledFunction()) {
      return (Fun->getName().equals("getchar") ||
              Fun->getName().equals("fgetc"));
    }
  }
  return false;
}

/**
 * Evaluate a PHINode to get its Domain.
 *
 * @param Phi PHINode to evaluate
 * @param InMem InMemory of Phi
 * @return Domain of Phi
 */
Domain *eval(PHINode *Phi, const Memory *InMem) {
  if (auto ConstantVal = Phi->hasConstantValue()) {
    return new Domain(extractFromValue(ConstantVal));
  }

  Domain *Joined = new Domain(Domain::Uninit);

  for (unsigned int i = 0; i < Phi->getNumIncomingValues(); i++) {
    auto Dom = getOrExtract(InMem, Phi->getIncomingValue(i));
    Joined = Domain::join(Joined, Dom);
  }
  return Joined;
}

/**
 * @brief Evaluate the +, -, * and / BinaryOperator instructions
 * using the Domain of its operands and return the Domain of the result.
 *
 * @param BinOp BinaryOperator to evaluate
 * @param InMem InMemory of BinOp
 * @return Domain of BinOp
 */
Domain *eval(BinaryOperator *BinOp, const Memory *InMem) {
  /**
   * evaluate +, -, * and /
   * based on the Domains of the operands.
   */
  Domain *op0 = getOrExtract(InMem, BinOp->getOperand(0));
  Domain *op1 = getOrExtract(InMem, BinOp->getOperand(1));
  switch (BinOp->getOpcode()){
    case Instruction::Add:
      return Domain::add(op0, op1);
    case Instruction::Sub:
      return Domain::sub(op0, op1);
    case Instruction::Mul:
      return Domain::mul(op0, op1);
    case Instruction::UDiv:
    case Instruction::SDiv:
      return Domain::div(op0, op1);
  }
  errs() << "Shouldn't be handled " << *BinOp << "\n";
   return new Domain(Domain::Uninit);
}

/**
 * @brief Evaluate Cast instructions.
 *
 * @param Cast Cast instruction to evaluate
 * @param InMem InMemory of Instruction
 * @return Domain of Cast
 */
Domain *eval(CastInst *Cast, const Memory *InMem) {
  
  return getOrExtract(InMem, Cast->getOperand(0));
}

/**
 * @brief Evaluate the ==, !=, <, <=, >=, and > Comparision operators using
 * the Domain of its operands to compute the Domain of the result.
 *
 * @param Cmp Comparision instruction to evaluate
 * @param InMem InMemory of Cmp
 * @return Domain of Cmp
 */
Domain *eval(CmpInst *Cmp, const Memory *InMem) {
  /** evaluate:
   * ==, !=, <, <=, >=, and > based on the Domains of the operands.
   *
   * NOTE: There is a lot of scope for refining this, but this is done by returning
   * MaybeZero for comparisons other than equality.
   */
   Domain *E1 = getOrExtract(InMem, Cmp->getOperand(0));
  Domain *E2 = getOrExtract(InMem, Cmp->getOperand(1));
  if (E1->Value == Domain::Uninit || E2->Value == Domain::Uninit){
    return new Domain(Domain::Uninit);
  }

  if(Cmp->getPredicate() == ICmpInst::ICMP_EQ){
  if (E1->Value == Domain::Zero && E2->Value == Domain::Zero){
    return new Domain(Domain::NonZero);
  }
  else{
    return new Domain(Domain::MaybeZero);
  }
  }

  if(Cmp->getPredicate() == ICmpInst::ICMP_NE){
    if((E1->Value == Domain::NonZero && E2->Value == Domain::Zero) || (E1->Value == Domain::Zero && E2->Value == Domain::NonZero)){
      return new Domain(Domain::NonZero);
    }
  else if (E1->Value == Domain::Zero && E2->Value == Domain::Zero){
    return new Domain(Domain::Zero);
  }
  else{
    return new Domain(Domain::MaybeZero);
  }
  }

  return new Domain(Domain::MaybeZero);
}

void DivZeroAnalysis::transfer(Instruction *Inst, const Memory *In,
                               Memory &NOut, PointerAnalysis *PA,
                               SetVector<Value *> PointerSet) {
  if (isInput(Inst)) {
    // The instruction is a user controlled input, it can have any value.
    NOut[variable(Inst)] = new Domain(Domain::MaybeZero);
  } else if (auto Phi = dyn_cast<PHINode>(Inst)) {
    // Evaluate PHI node
    NOut[variable(Phi)] = eval(Phi, In);
  } else if (auto BinOp = dyn_cast<BinaryOperator>(Inst)) {
    // Evaluate BinaryOperator
    NOut[variable(BinOp)] = eval(BinOp, In);
  } else if (auto Cast = dyn_cast<CastInst>(Inst)) {
    // Evaluate Cast instruction
    NOut[variable(Cast)] = eval(Cast, In);
  } else if (auto Cmp = dyn_cast<CmpInst>(Inst)) {
    // Evaluate Comparision instruction
    NOut[variable(Cmp)] = eval(Cmp, In);
  } else if (auto Alloca = dyn_cast<AllocaInst>(Inst)) {
    // Do nothing here.
  } else if (auto Store = dyn_cast<StoreInst>(Inst)) {
    /**
     * Store instruction can either add new variables or overwrite existing variables into memory maps.
     * To update the memory map, we rely on the points-to graph constructed in PointerAnalysis.
     *
     * To build the abstract memory map, you need to ensure all pointer references are in-sync, and
     * will converge upon a precise abstract value. To achieve this, implement the following workflow:
     *
     * Iterate through the provided PointerSet:
     *   - If there is a may-alias (i.e., `alias()` returns true) between two variables:
     *     + Get the abstract values of each variable.
     *     + Join the abstract values using Domain::join().
     *     + Update the memory map for the current assignment with the joined abstract value.
     *     + Update the memory map for all may-alias assignments with the joined abstract value.
     *
     * Hint: You may find getOperand(), getValueOperand(), and getPointerOperand() useful.
     */
    if(Store->getValueOperand()->getType()->isIntegerTy()){
      auto ptr1 = variable(Store->getPointerOperand());
      for(auto p: PointerSet){
      auto ptr2 = variable(p);
      if(ptr1 == ptr2){
        NOut[ptr1] = getOrExtract(In, Store->getValueOperand());
        NOut[ptr2] = getOrExtract(In, Store->getValueOperand());
      }else
      if(PA->alias(ptr1, ptr2)){
        Domain *Joined = Domain::join(getOrExtract(In, Store->getValueOperand()), getOrExtract(In, p));
        NOut[ptr1] = Joined;
        NOut[ptr2] = Joined;
      }
    }
    }
  } else if (auto Load = dyn_cast<LoadInst>(Inst)) {
    /**
     * Rely on the existing variables defined within the `In` memory to
     * know what abstract domain should be for the new variable
     * introduced by a load instruction.
     *
     * If the memory map already contains the variable, propagate the existing
     * abstract value to NOut.
     * Otherwise, initialize the memory map for it.
     *
     * Hint: You may use getPointerOperand().
     */
     auto type = Load->getType();
    if(type->isIntegerTy()){
      auto value = Load->getPointerOperand();
      if((*In).find(variable(value)) != (*In).end()){
        NOut[variable(Load)] = In->at(variable(value));
      }else{
        NOut[variable(Load)] = getOrExtract(In, value);
      }
    }
  } else if (auto Branch = dyn_cast<BranchInst>(Inst)) {
    // Analysis is flow-insensitive, so do nothing here.
  } else if (auto Call = dyn_cast<CallInst>(Inst)) {
    /**
     * Populate the NOut with an appropriate abstract domain.
     *
     * You only need to consider calls with int return type.
     */
    if(Call->getType()->isIntegerTy()){
      NOut[variable(Call)] = new Domain(Domain::MaybeZero);
    }
  } else if (auto Return = dyn_cast<ReturnInst>(Inst)) {
    // Analysis is intra-procedural, so do nothing here.
  } else {
    errs() << "Unhandled instruction: " << *Inst << "\n";
  }
}

} // namespace dataflow