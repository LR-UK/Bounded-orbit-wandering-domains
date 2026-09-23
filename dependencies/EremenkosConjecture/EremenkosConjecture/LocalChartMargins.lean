import EremenkosConjecture.ComponentBarriers
import EremenkosConjecture.UniformConformalStability
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Function

namespace EremenkosConjecture

/-- A uniform source margin becomes a uniform image margin when the inverse
chart is uniformly continuous on the closed inset. -/
theorem exists_uniform_image_tube_of_uniform_inverse
    (e : OpenPartialHomeomorph ℂ ℂ) {S A : Set ℂ}
    (hS : S ⊆ e.source) (himage : IsClosed (e '' S))
    (hinv : UniformContinuousOn e.symm (e '' S)) {r : ℝ} (hr : 0 < r)
    (htube : ∀ z ∈ A, ball z r ⊆ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ e '' A, ball w δ ⊆ interior (e '' S) := by
  have hA : A ⊆ S := fun z hz => htube z hz (mem_ball_self hr)
  have hint : e '' interior S ⊆ interior (e '' S) :=
    interior_maximal (image_mono interior_subset)
      (e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hS))
  obtain ⟨δ, hδ, hδr⟩ := Metric.uniformContinuousOn_iff.mp hinv r hr
  refine ⟨δ, hδ, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  have hzint : e z ∈ interior (e '' S) := by
    apply hint
    exact ⟨z, interior_maximal (htube z hz) isOpen_ball (mem_ball_self hr), rfl⟩
  have hdisj : Disjoint (ball (e z) δ) (frontier (e '' S)) := by
    apply disjoint_left.mpr
    intro v hv hvfront
    have hvS : v ∈ e '' S := himage.closure_eq ▸ hvfront.1
    obtain ⟨x, hx, rfl⟩ := hvS
    have hd := hδr (e x) (mem_image_of_mem e hx)
      (e z) (mem_image_of_mem e (hA hz)) hv
    rw [e.left_inv (hS hx), e.left_inv (hS (hA hz))] at hd
    have hxint : x ∈ interior S := interior_maximal (htube z hz) isOpen_ball hd
    exact hvfront.2 (hint (mem_image_of_mem e hxint))
  have hsub := connectedComponentIn_subset_interior_of_frontier_disjoint himage hdisj
    (mem_ball_self hδ) hzint
  rwa [(convex_ball (e z) δ).isPreconnected.connectedComponentIn (mem_ball_self hδ)] at hsub

/-- Uniform continuity on an image neighbourhood, together with a positive
image margin, gives the control needed by finite-iterate approximation. -/
theorem uniformControlOn_of_uniformContinuousOn
    {f : ℂ → ℂ} {S A : Set ℂ} (hf : UniformContinuousOn f S)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ S) :
    UniformControlOn f S A := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hf ε hε
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro z hz w hw
  have hwS := htube z hz (hw.trans_le (min_le_left _ _))
  exact ⟨hwS, hclose w hwS z (htube z hz (mem_ball_self hr))
    (hw.trans_le (min_le_right _ _))⟩

/-- Consecutive iterates give uniform control on an intermediate image using
local charts and their uniformly continuous inverses. -/
theorem uniformControlOn_iterate_image_of_local_chart
    {f : ℂ → ℂ} {S A E : Set ℂ} {k : ℕ}
    (e : OpenPartialHomeomorph ℂ ℂ) (hS : S ⊆ e.source)
    (he : EqOn (f^[k]) e S) (hclosed : IsClosed (e '' S))
    (hinv : UniformContinuousOn e.symm (e '' S))
    (hnext : UniformContinuousOn (f^[k + 1]) S)
    {r : ℝ} (hr : 0 < r) (htube : ∀ z ∈ A, ball z r ⊆ S)
    (himage : e '' S ⊆ E) : UniformControlOn f E ((f^[k]) '' A) := by
  have hA : A ⊆ S := fun z hz => htube z hz (mem_ball_self hr)
  have hmap : MapsTo e.symm (e '' S) S := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hS hz)] using hz
  have heq : EqOn ((f^[k + 1]) ∘ e.symm) f (e '' S) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [comp_apply, e.left_inv (hS hz), iterate_succ_apply', he hz]
  have huc : UniformContinuousOn f (e '' S) := (hnext.comp hinv hmap).congr heq
  obtain ⟨δ, hδ, hδtube⟩ := exists_uniform_image_tube_of_uniform_inverse
    e hS hclosed hinv hr htube
  have hc := uniformControlOn_of_uniformContinuousOn huc hδ
    (fun z hz => (hδtube z hz).trans interior_subset)
  have hEq : (f^[k]) '' A = e '' A := image_congr (he.mono hA)
  rw [hEq]
  intro ε hε
  obtain ⟨d, hd, hcontrol⟩ := hc ε hε
  exact ⟨d, hd, fun z hz w hw => ⟨himage (hcontrol z hz w hw).1,
    (hcontrol z hz w hw).2⟩⟩

end EremenkosConjecture
