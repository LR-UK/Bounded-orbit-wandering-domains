import EremenkosConjecture.SineChainPaths
import EremenkosConjecture.AmbientExtension

open Set Metric Filter Topology Real

namespace EremenkosConjecture.SineContinuum

theorem zero_mem_complexChain : (0 : ℂ) ∈ complexChain := by
  rw [mem_complexChain_iff]
  simpa only [Complex.zero_re, Complex.zero_im, Prod.zero_eq_mk] using zero_mem_chain

theorem pathComponentIn_complexChain_zero : pathComponentIn complexChain 0 = {0} := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨γ, hγ⟩ := hq
    have H := no_curve_from_zero (Complex.equivRealProdCLM.continuous.comp γ.continuous_extend)
      (by simp only [Function.comp_apply, γ.extend_zero, map_zero]) (fun t ht => by
        apply (mem_complexChain_iff _).mp
        simpa only [γ.extend_extends' ⟨t, ht⟩] using hγ ⟨t, ht⟩)
    apply Complex.equivRealProdCLM.injective
    simpa only [Function.comp_apply, γ.extend_one, map_zero] using H
  · rintro q rfl
    exact mem_pathComponentIn_self zero_mem_complexChain

theorem zero_mem_frontier_complexChain : (0 : ℂ) ∈ frontier complexChain := by
  rw [frontier_eq_closure_inter_closure, isCompact_complexChain.isClosed.closure_eq]
  refine ⟨zero_mem_complexChain, ?_⟩
  have hlim : Tendsto (fun n => (-(radius n : ℂ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Complex.ofReal_zero, neg_zero] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp radius_tendsto).neg
  apply isClosed_closure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  apply subset_closure
  intro hn
  have hpair := (mem_complexChain_iff _).mp hn
  have hne : ((-(radius n : ℂ)).re, (-(radius n : ℂ)).im) ≠ (0 : ℝ × ℝ) := by
    intro H
    have H' := congrArg Prod.fst H
    simp only [Complex.neg_re, Complex.ofReal_re, Prod.fst_zero] at H'
    linarith [radius_pos n]
  have H := chain_fst_pos hpair hne
  simp only [Complex.neg_re, Complex.ofReal_re] at H
  linarith [radius_pos n]

theorem complexChain_nontrivial : complexChain.Nontrivial := by
  let p := copyMap 0 (1, sin 1)
  have hp : p ∈ chain := mem_chain_iff.mpr (Or.inr ⟨0, ⟨_, right_mem_base, rfl⟩⟩)
  refine ⟨0, zero_mem_complexChain, Complex.equivRealProdCLM.symm p, ⟨p, hp, rfl⟩, ?_⟩
  intro H
  have H' := congrArg (fun z : ℂ => (Complex.equivRealProdCLM z).1) H
  simp only [map_zero, Prod.fst_zero, ContinuousLinearEquiv.apply_symm_apply] at H'
  norm_num [p, copyMap, radius] at H'

end EremenkosConjecture.SineContinuum

namespace EremenkosConjecture

/-- A full continuum with a prescribed singleton path component, as in Figure 5. -/
theorem exists_full_continuum_singleton_pathComponent (a : ℂ) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧ IsConnected Kᶜ ∧ K.Nontrivial ∧
      a ∈ frontier K ∧ pathComponentIn K a = {a} := by
  let H := Homeomorph.addRight a
  let K := H '' SineContinuum.complexChain
  have ha : a ∈ K := ⟨0, SineContinuum.zero_mem_complexChain, by simp [H]⟩
  refine ⟨K, SineContinuum.isCompact_complexChain.image H.continuous,
    SineContinuum.isConnected_complexChain.image H H.continuous.continuousOn,
    isConnected_compl_image_homeomorph H SineContinuum.isConnected_compl_complexChain,
    SineContinuum.complexChain_nontrivial.image H.injective, ?_, ?_⟩
  · rw [show K = H '' SineContinuum.complexChain from rfl, ← H.image_frontier]
    exact ⟨0, SineContinuum.zero_mem_frontier_complexChain, by simp [H]⟩
  · apply Subset.antisymm
    · intro q hq
      have hm := hq.map H.symm.continuous.continuousOn
      have heq : H.symm '' K = SineContinuum.complexChain := by
        dsimp [K]
        rw [← image_comp, show H.symm ∘ H = id from funext H.symm_apply_apply, image_id]
      have ha0 : H.symm a = 0 := by
        apply H.injective
        rw [H.apply_symm_apply]
        simp [H]
      rw [heq, ha0] at hm
      have hzero : H.symm q = 0 := by
        change H.symm q ∈ pathComponentIn SineContinuum.complexChain 0 at hm
        rw [SineContinuum.pathComponentIn_complexChain_zero] at hm
        exact hm
      have Hq := congrArg H hzero
      simpa [H] using Hq
    · rintro q rfl
      exact mem_pathComponentIn_self ha

end EremenkosConjecture
