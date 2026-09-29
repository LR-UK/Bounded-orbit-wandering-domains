module

public import ComplexApproximation.Conformal.RiemannInverseBounds
public import ComplexApproximation.Conformal.KernelSubsequence
public import FunctionTheory.Conformal.BoundedKernel

@[expose] public section

/-! # Compatibility imports for FunctionTheory

The proofs now belong to the sibling FunctionTheory project. These aliases
preserve the existing declarations and their mathematical statements.
-/

namespace ComplexApproximation

alias exists_normalized_riemann_kernel_subsequence := FunctionTheory.exists_normalized_riemann_kernel_subsequence

end ComplexApproximation
