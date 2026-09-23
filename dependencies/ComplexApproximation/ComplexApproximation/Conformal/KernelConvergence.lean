import ComplexApproximation.Conformal.BoundedKernel
import FunctionTheory.Conformal.KernelConvergence

/-! # Compatibility imports for FunctionTheory

The proofs now belong to the sibling FunctionTheory project. These aliases
preserve the existing declarations and their mathematical statements.
-/

namespace ComplexApproximation

alias locallyUniformOn_of_subsequence_limits := FunctionTheory.locallyUniformOn_of_subsequence_limits
alias normalized_riemannMaps_tendsto_on_bounded_kernel := FunctionTheory.normalized_riemannMaps_tendsto_on_bounded_kernel
alias exists_normalized_riemannMap_of_bounded_kernel := FunctionTheory.exists_normalized_riemannMap_of_bounded_kernel

end ComplexApproximation
