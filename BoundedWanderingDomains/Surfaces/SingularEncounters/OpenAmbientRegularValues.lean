module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LocalDynamics

@[expose] public section

/-! # Regular values are preserved when the target is read in an open subsurface -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

theorem regularValues_into_open_ambient_of_source_homeomorph
    {X : Type*} [TopologicalSpace X] (O : TopologicalSpace.Opens X)
    (f : LocalMap X) (g : LocalMap O) (e : g.source ≃ₜ f.source)
    (hcomm : ∀ u, (g.map u : X) = f.map (e u)) :
    Subtype.val ⁻¹' f.regularValues ⊆ g.regularValues := by
  let p : g.source → X := fun u => (g.map u : X)
  have hpeq : p = f.map ∘ e := funext hcomm
  let eAll : g.source ≃ₜ p ⁻¹' (O : Set X) :=
    { toFun := fun u => ⟨u, (g.map u).2⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  intro y hy
  obtain ⟨W, hW, hyW, hWr, hWc⟩ := hy
  let B : Set O := Subtype.val ⁻¹' W
  have hp : IsCoveringMapOn p W := by
    rw [hpeq]
    exact hWc.comp_homeomorph e
  refine ⟨B, hW.preimage continuous_subtype_val, hyW, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha⟩ := hWr hb
    refine ⟨e.symm a, Subtype.ext ?_⟩
    exact (hcomm (e.symm a)).trans ((congrArg f.map (e.apply_symm_apply a)).trans ha)
  · intro b hb
    have hh := ((hp b hb).restrictPreimage (O : Set X) b.2).comp_homeomorph eAll
    change IsEvenlyCovered g.map b _ at hh
    exact hh.to_isEvenlyCovered_preimage

end SurfaceDynamics.LocalMap
