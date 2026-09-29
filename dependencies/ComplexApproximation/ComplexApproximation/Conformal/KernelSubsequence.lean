module

public import ComplexApproximation.Conformal.InverseLimits
public import FunctionTheory.Conformal.KernelSubsequence

@[expose] public section

/-! # Compatibility imports for FunctionTheory

The proofs now belong to the sibling FunctionTheory project. These aliases
preserve the existing declarations and their mathematical statements.
-/

namespace ComplexApproximation

alias exists_biholomorphic_kernel_subsequence := FunctionTheory.exists_biholomorphic_kernel_subsequence

end ComplexApproximation
