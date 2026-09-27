/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereCombinedRemoval
import BoundedWanderingDomains.FinitePunctureSphereArea

/-! # Uniform singular-obstacle cost for finite dynamical models -/

open Set Function OnePoint MeasureTheory Filter
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

/-- A closed planar obstacle lying in a fixed compact spherical set plus
finitely many exceptional values has uniformly bounded area cost on the
separated compact set, independently of the finite model. -/
theorem uniform_singular_gain_finite_models
    {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) (E : Finset ℂ)
    {S : Set ℂ} (hS : IsClosed S)
    (hSE : ∀ z ∈ S, (z : OnePoint ℂ) ∈ K ∨ z ∈ E) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (P : Finset ℂ) {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P)
        (W : Set ℂ) (_hW : MeasurableSet W)
        (_hWL : ∀ z ∈ W, (z : OnePoint ℂ) ∈ L)
        (_hWP : Disjoint W (↑P : Set ℂ)) (_hWE : Disjoint W (↑E : Set ℂ)),
        (∫⁻ z in W,
          hyperbolicAreaWeight ((↑P : Set ℂ) ∪ S) (P.finite_toSet.isClosed.union hS)
            hab (Or.inl ha) (Or.inl hb) z -
          hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := uniform_compact_finite_gain_sphere hK hL hKL E
  refine ⟨C, hC, ?_⟩
  intro P a b hab ha hb W hW hWL hWP hWE
  let A := finiteSphereObstacle P
  let D := finiteSphereMetricData P hab ha hb
  let B := (A ∪ K) ∪ sphereFiniteSet E
  have hB : IsClosed B := ((isClosed_finiteSphereObstacle P).union hK.isClosed).union
    (E.finite_toSet.image (fun z : ℂ => (z : OnePoint ℂ))).isClosed
  let Q : Set ℂ := (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' B
  have hQ : IsClosed Q := closed_sphere_set_in_pole_chart hB _
  have hPQ : (↑P : Set ℂ) ⊆ Q := by
    intro z hz
    exact Or.inl (Or.inl ((coe_mem_finiteSphereObstacle P z).mpr hz))
  have hSQ : (↑P : Set ℂ) ∪ S ⊆ Q := by
    rintro z (hzP | hzS)
    · exact hPQ hzP
    · rcases hSE z hzS with hzK | hzE
      · exact Or.inl (Or.inr hzK)
      · exact Or.inr ⟨z, hzE, rfl⟩
  have hWQ : W ⊆ Qᶜ := by
    intro z hz
    rintro ((hzP | hzK) | ⟨w, hwE, hwz⟩)
    · exact disjoint_left.mp hWP hz ((coe_mem_finiteSphereObstacle P z).mp hzP)
    · exact disjoint_left.mp hKL hzK (hWL z hz)
    · have hw : w = z := OnePoint.coe_injective hwz
      exact disjoint_left.mp hWE hz (hw ▸ hwE)
  have hbnd := hbound A (isClosed_finiteSphereObstacle P) D rfl
  have hplane : (∫⁻ z in (spherePoleChart (∞ : OnePoint ℂ)) ⁻¹' (L ∩ Bᶜ),
      hyperbolicAreaWeight Q hQ hab (hPQ ha) (hPQ hb) z -
      hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C := by
    unfold sphereHyperbolicAreaGain at hbnd
    simpa only [D, finiteSphereMetricData, A,
      infty_chart_preimage_finiteSphereObstacle] using hbnd
  apply le_trans _ hplane
  calc
    _ ≤ ∫⁻ z in W,
        hyperbolicAreaWeight Q hQ hab (hPQ ha) (hPQ hb) z -
        hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hW] with z hz
      exact tsub_le_tsub_right
        (hyperbolicAreaWeight_mono_any _ _ (P.finite_toSet.isClosed.union hS) hQ hSQ
          hab hab (Or.inl ha) (Or.inl hb) (hPQ ha) (hPQ hb) (hWQ hz)) _
    _ ≤ _ := by
      apply lintegral_mono_set
      intro z hz
      exact ⟨hWL z hz, hWQ hz⟩

end AreaDeficit
