module

public import Runge.LocalDomain
public import FunctionTheory.Conformal.RiemannMapping

@[expose] public section

/-! # Compatibility imports for FunctionTheory

The proofs now belong to the sibling FunctionTheory project. These aliases
preserve the existing declarations and their mathematical statements.
-/

namespace ComplexApproximation

alias exists_riemannMap_on_domain := FunctionTheory.exists_riemannMap_on_domain

end ComplexApproximation
