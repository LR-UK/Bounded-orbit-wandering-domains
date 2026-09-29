module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
public import BoundedWanderingDomains.Surfaces.LocalMapTotalization

@[expose] public section

/-! # Compact subsets follow the common covering-disc itinerary -/

open Set Function Filter Topology
open scoped Manifold

namespace AreaDeficit.Surfaces.DiscCover

theorem compact_subset_covering_radius
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (U : TopologicalSpace.Opens X) (p : DiscCover U)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℝ, r < 1 ∧
      K ⊆ (fun w => (p.projection w : X)) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ r} := by
  let L : Set U := Subtype.val ⁻¹' K
  have hLeq : (Subtype.val : U → X) '' L = K :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
  have hL : IsCompact L := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, hLeq]
    exact hK
  obtain ⟨B, hB, hLB⟩ := p.compact_lift_set hL
  have hbound : ∃ r : ℝ, r < 1 ∧ ∀ w ∈ B, ‖(w : ℂ)‖ ≤ r := by
    by_cases hne : B.Nonempty
    · obtain ⟨w, hwB, hw⟩ := hB.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
      refine ⟨‖(w : ℂ)‖, ?_, hw⟩
      exact mem_ball_zero_iff.mp w.2
    · refine ⟨0, zero_lt_one, ?_⟩
      intro w hw
      exact False.elim (hne ⟨w, hw⟩)
  obtain ⟨r, hr, hBr⟩ := hbound
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨w, hwB, hwx⟩ := hLB (show (⟨x, hKU hx⟩ : U) ∈ L from hx)
  exact ⟨w, hBr w hwB, congrArg Subtype.val hwx⟩

end AreaDeficit.Surfaces.DiscCover

namespace SurfaceDynamics.LocalMap

theorem eventually_capture_compact_of_covering_radii
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (U : TopologicalSpace.Opens X) (p : AreaDeficit.Surfaces.DiscCover U)
    (F : ℕ → AreaDeficit.Surfaces.unitDisc → X)
    (hF0 : F 0 = fun w => (p.projection w : X))
    (hforward : ∀ r : ℝ, r < 1 → ∀ n,
      MapsTo f.totalize (F n '' {w | ‖(w : ℂ)‖ ≤ r})
        (F (n + 1) '' {w | ‖(w : ℂ)‖ ≤ r}))
    (φ : ℕ → ℕ) (V : ℕ → Set X)
    (hV : ∀ r : ℝ, r < 1 → ∀ᶠ n in atTop,
      F (φ n) '' {w | ‖(w : ℂ)‖ ≤ r} ⊆ V n) :
    ∀ K : Set X, IsCompact K → K ⊆ U →
      ∀ᶠ n in atTop, MapsTo (f.totalize^[φ n]) K (V n) := by
  intro K hK hKU
  obtain ⟨r, hr, hKr⟩ := p.compact_subset_covering_radius U hK hKU
  have hiter : ∀ m, MapsTo (f.totalize^[m]) K (F m '' {w | ‖(w : ℂ)‖ ≤ r}) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      change y ∈ F 0 '' {w | ‖(w : ℂ)‖ ≤ r}
      rw [hF0]
      exact hKr hy
    | succ m ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      exact hforward r hr m (ih hy)
  filter_upwards [hV r hr] with n hn
  exact (hiter (φ n)).mono_right hn

end SurfaceDynamics.LocalMap
