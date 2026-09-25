/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.KernelLift

/-! # Pulling dense finite punctures back to the fixed ambient disc -/

open Set Function Metric Filter
open scoped Topology Manifold
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The lifted finite punctures are dense in the preimage of their closed
limit. Openness of the ambient covering map supplies the reverse closure
inclusion, so planar Hurwitz can be used upstairs. -/
theorem preimage_dense_finite_punctures (p : DiscCover M)
    (P : ℕ → Finset M) {A : Set M}
    (hA : closure (⋃ n, (↑(P n) : Set M)) = A) :
    closure (⋃ n, p.projection ⁻¹' (↑(P n) : Set M)) =
      p.projection ⁻¹' A := by
  rw [← preimage_iUnion]
  rw [← p.isOpenMap.preimage_closure_eq_closure_preimage p.continuous]
  exact congrArg (p.projection ⁻¹' ·) hA

end AreaDeficit.Surfaces.DiscCover



open Metric
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Express the lifted puncture closure in ordinary complex coordinates,
the exact input expected by the planar Hurwitz omission theorem. -/
theorem mem_closure_lifted_punctures_iff (p : DiscCover M)
    (P : ℕ → Finset M) {A : Set M}
    (hA : closure (⋃ n, (↑(P n) : Set M)) = A)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    z ∈ closure ((Subtype.val : unitDisc → ℂ) ''
      (⋃ n, p.projection ⁻¹' (↑(P n) : Set M))) ↔
      p.projection (⟨z,hz⟩ : unitDisc) ∈ A := by
  have hs := (closure_subtype (x := (⟨z,hz⟩ : unitDisc))
    (s := ⋃ n, p.projection ⁻¹' (↑(P n) : Set M)))
  rw [p.preimage_dense_finite_punctures P hA] at hs
  exact hs.symm

end AreaDeficit.Surfaces.DiscCover

open Filter
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Planar Hurwitz on the fixed ambient covering disc prevents a
nonconstant normal limit from meeting the closed omitted set downstairs. -/
theorem ambient_hurwitz_avoidance (p : DiscCover M)
    (P : ℕ → Finset M) (hP : Monotone P) {A : Set M}
    (hA : closure (⋃ n, (↑(P n) : Set M)) = A)
    (h : ℕ → unitDisc → unitDisc)
    (hh : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h n))
    (havoid : ∀ n (v : unitDisc), p.projection (h n v) ∉ (↑(P n) : Set M))
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {g : ℂ → ℂ}
    (hl : TendstoLocallyUniformlyOn
      (fun n => planeExtension (fun v => (h (φ n) v : ℂ))) g atTop (ball 0 r))
    (hn : ¬∃ c, ∀ z ∈ ball (0 : ℂ) r, g z = c)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    (hgz : g z ∈ ball (0 : ℂ) 1) :
    p.projection (⟨g z,hgz⟩ : unitDisc) ∉ A := by
  let S : Set ℂ := (Subtype.val : unitDisc → ℂ) ''
    (⋃ n, p.projection ⁻¹' (↑(P n) : Set M))
  have hd : ∀ n, DifferentiableOn ℂ
      (planeExtension (fun v => (h (φ n) v : ℂ))) (ball 0 r) := by
    intro n
    exact (planeExtension_differentiableOn
      ((mdifferentiable_subtype_val unitDisc).comp (hh (φ n)))).mono
        (ball_subset_ball hr1.le)
  have homit : ∀ a ∈ S, ∀ᶠ n in atTop,
      ∀ z ∈ ball (0 : ℂ) r,
        planeExtension (fun v => (h (φ n) v : ℂ)) z ≠ a := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := ha
    obtain ⟨k,hvk⟩ := Set.mem_iUnion.mp hv
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k)] with n hn z hz
    have hz1 : z ∈ ball (0 : ℂ) 1 := (ball_subset_ball hr1.le) hz
    intro he
    have hval : planeExtension (fun v => (h (φ n) v : ℂ)) z =
        (h (φ n) ⟨z,hz1⟩ : ℂ) :=
      planeExtension_coe _ ⟨z,hz1⟩
    rw [hval] at he
    have he' : h (φ n) ⟨z,hz1⟩ = v := Subtype.ext he
    have hvP : p.projection v ∈ (↑(P (φ n)) : Set M) := hP hn hvk
    exact havoid (φ n) ⟨z,hz1⟩ (he' ▸ hvP)
  have hlim := AreaDeficit.nonconstant_limit_avoids_closure
    isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected hd hl homit hn
  have hnot : g z ∉ closure S :=
    disjoint_left.mp hlim (mem_image_of_mem g hz)
  intro ha
  exact hnot ((p.mem_closure_lifted_punctures_iff P hA hgz).mpr ha)

end AreaDeficit.Surfaces.DiscCover
