module

public import ComplexApproximation.Conformal.RiemannMapping
public import FunctionTheory.Conformal.RiemannInverseBounds

@[expose] public section

/-! # Compatibility imports for FunctionTheory

The proofs now belong to the sibling FunctionTheory project. These aliases
preserve the existing declarations and their mathematical statements.
-/

namespace ComplexApproximation

alias normalized_inverse_derivative_lower_bound := FunctionTheory.normalized_inverse_derivative_lower_bound

end ComplexApproximation
