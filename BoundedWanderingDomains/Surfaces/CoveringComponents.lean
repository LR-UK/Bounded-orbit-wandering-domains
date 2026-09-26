/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import Mathlib.Topology.Homotopy.Lifting

/-! # Connected components of covering spaces -/

open Set Function Topology unitInterval

/-- Every connected component of the source of a covering maps onto a
path-connected target. -/
theorem IsCoveringMap.surjective_connectedComponent
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) (e : E) :
    Surjective (fun z : connectedComponent e => p z) := by
  intro x
  let γ : Path (p e) x := PathConnectedSpace.somePath (p e) x
  let Γ := hp.liftPath γ e γ.source
  have hΓ0 : Γ 0 = e := hp.liftPath_zero γ e γ.source
  have hΓ1 : p (Γ 1) = x := by
    have h := congrFun (hp.liftPath_lifts γ e γ.source) 1
    exact h.trans γ.target
  have hmem : Γ 1 ∈ connectedComponent e := by
    apply pathComponent_subset_component e
    refine ⟨⟨Γ, hΓ0, rfl⟩⟩
  exact ⟨⟨Γ 1, hmem⟩, hΓ1⟩

#print axioms IsCoveringMap.surjective_connectedComponent
