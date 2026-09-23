import EremenkosConjecture.RayCounterexample
import ComplexDynamics.Conjugacy

/-! # Theorem 7.1, with the endpoint at the origin -/

open Set Function ComplexDynamics

namespace EremenkosConjecture

theorem theorem7_1 : ∃ f : ℂ → ℂ,
    IsTranscendentalEntire f ∧ horizontalRay 0 ⊆ juliaSet f ∧ (0 : ℂ) ∈ escapingSet f ∧
    horizontalRay 0 \ {0} ⊆ bungeeSet f ∧
    connectedComponentIn (juliaSet f ∪ escapingSet f ∪ bungeeSet f) 0 = horizontalRay 0 ∧
    connectedComponentIn (escapingSet f) 0 = {0} := by
  obtain ⟨f, hf, hJ, hI, hB, hcomponent, hsingleton⟩ := theorem7_1_translated
  let H : ℂ ≃ₜ ℂ := (translation rayBase).symm
  let g := conjugate H f
  have hH (z : ℂ) : H z = z - rayBase := rfl
  have hzero : H rayBase = 0 := sub_self rayBase
  have hg (z : ℂ) : g z = f (z + rayBase) - rayBase := rfl
  have hg_entire : IsEntire g :=
    (hf.1.comp (differentiable_id.add_const rayBase)).sub_const rayBase
  have hg_trans : IsTranscendentalEntire g := by
    refine ⟨hg_entire, ?_⟩
    rintro ⟨p, hp⟩
    apply hf.2
    refine ⟨p.comp (Polynomial.X - Polynomial.C rayBase) + Polynomial.C rayBase, fun z => ?_⟩
    have he := hp (z - rayBase)
    rw [hg, sub_add_cancel] at he
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact sub_eq_iff_eq_add.mp he
  have hray : H '' horizontalRay rayBase = horizontalRay 0 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨sub_nonneg.mpr hw.1, sub_eq_zero.mpr hw.2⟩
    · intro hz
      refine ⟨z + rayBase, ⟨?_, ?_⟩, ?_⟩
      · change rayBase.re ≤ z.re + rayBase.re
        have hr : 0 ≤ z.re := hz.1
        linarith
      · change z.im + rayBase.im = rayBase.im
        have hi : z.im = 0 := hz.2
        simp only [hi, zero_add]
      · exact add_sub_cancel_right z rayBase
  have hJ' : horizontalRay 0 ⊆ juliaSet g := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hray.symm ▸ hz
    exact (mem_juliaSet_conjugate_iff H f w).mpr (hJ hw)
  have hI' : (0 : ℂ) ∈ escapingSet g := by
    simpa only [hzero] using (mem_escapingSet_conjugate_iff H f rayBase).mpr hI
  refine ⟨g, hg_trans, hJ', hI', ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, he⟩ := hray.symm ▸ hz.1
    have hne : w ≠ rayBase := by
      intro h
      apply hz.2
      rw [← he, h, hzero]
      exact mem_singleton 0
    rw [← he]
    exact (mem_bungeeSet_conjugate_iff H f w).mpr (hB ⟨hw, hne⟩)
  · have he := H.image_connectedComponentIn
      (show rayBase ∈ juliaSet f ∪ escapingSet f ∪ bungeeSet f from Or.inl (Or.inr hI))
    rw [hcomponent, image_union, image_union, image_juliaSet_conjugate,
      image_escapingSet_conjugate, image_bungeeSet_conjugate, hzero, hray] at he
    exact he.symm
  · have he := H.image_connectedComponentIn hI
    rw [hsingleton, image_singleton, hzero, image_escapingSet_conjugate] at he
    exact he.symm

/-- Eremenko's conjecture fails: some escaping point belongs to no connected
subset of the escaping set other than its singleton. -/
theorem eremenko_conjecture_false : ∃ (f : ℂ → ℂ) (z : ℂ),
    IsTranscendentalEntire f ∧ z ∈ escapingSet f ∧
      ∀ A : Set ℂ, IsConnected A → A ⊆ escapingSet f → z ∈ A → A = {z} := by
  obtain ⟨f, z, hf, hz, hcomponent⟩ := eremenko_counterexample
  refine ⟨f, z, hf, hz, ?_⟩
  intro A hA hAI hzA
  have hsub := hA.isPreconnected.subset_connectedComponentIn hzA hAI
  rw [hcomponent] at hsub
  exact hsub.antisymm (singleton_subset_iff.mpr hzA)

end EremenkosConjecture
