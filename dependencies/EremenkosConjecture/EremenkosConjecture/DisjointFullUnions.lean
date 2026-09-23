import ComplexApproximation.Topology.Nonseparation

/-!
# Unions of disjoint full compact sets

This compatibility interface now follows from the general disjoint closed-set
nonseparation theorem in ComplexApproximation. The continuous-logarithm proof
formerly in this file has been moved and generalised there.
-/

open Set Metric Function

namespace EremenkosConjecture

/-- Disjoint full compacta have full union (the disjoint case of Janiszewski). -/
theorem isConnected_compl_union_disjoint (A B : Set ℂ) (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsConnected Aᶜ) (hBc : IsConnected Bᶜ) (hAB : Disjoint A B) :
    IsConnected (A ∪ B)ᶜ := by
  obtain ⟨R, hR, hbound⟩ := (hA.union hB).isBounded.exists_pos_norm_le
  refine ⟨?_, ComplexApproximation.isPreconnected_compl_union_disjoint A B
    hA.isClosed hB.isClosed hAB hAc.isPreconnected hBc.isPreconnected⟩
  refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
  intro hz
  have H := hbound _ hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at H
  linarith

end EremenkosConjecture
