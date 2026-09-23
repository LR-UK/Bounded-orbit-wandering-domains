import EremenkosConjecture.SineChainFibers
import Mathlib.Topology.Order.Compact

open Set Metric Filter Topology Real

namespace EremenkosConjecture.SineContinuum

private theorem exists_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {s t x : ℝ} (hst : s ≤ t) (hx : x ∈ Icc (f s) (f t)) :
    ∃ u ∈ Icc s t, f u = x :=
  (isPreconnected_Icc.image f hf.continuousOn).Icc_subset
    ⟨s, ⟨le_rfl, hst⟩, rfl⟩ ⟨t, ⟨hst, le_rfl⟩, rfl⟩ hx

/-- The limit point of the shrinking sine chain cannot be joined to any other point. -/
theorem no_curve_from_zero {g : ℝ → ℝ × ℝ} (hg : Continuous g)
    (hstart : g 0 = 0) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ chain) : g 1 = 0 := by
  by_contra hend
  have hxend : 0 < (g 1).1 := chain_fst_pos (hmem 1 ⟨zero_le_one, le_rfl⟩) hend
  obtain ⟨n, hn⟩ := (radius_tendsto.eventually_lt_const hxend).exists
  let a := radius (n + 1)
  have ha : 0 < a := radius_pos _
  have hstep : radius n = 2 * a := by dsimp [a]; rw [radius_step]; ring
  have hfst : Continuous (fun t => (g t).1) := continuous_fst.comp hg
  let A : Set ℝ := Icc 0 1 ∩ {t | (g t).1 = a}
  have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_eq hfst continuous_const)
  have hAne : A.Nonempty := by
    obtain ⟨t, ht, heq⟩ := exists_level_between hfst zero_le_one
      (show a ∈ Icc (g 0).1 (g 1).1 from ⟨by simpa [hstart] using ha.le, by linarith⟩)
    exact ⟨t, ht, heq⟩
  let t₀ := sSup A
  have ht₀ : t₀ ∈ A := hA.sSup_mem hAne
  have ht₀₁ : t₀ < 1 := lt_of_le_of_ne ht₀.1.2 (by
    intro H
    have heq := ht₀.2
    change (g t₀).1 = a at heq
    rw [H] at heq
    linarith)
  obtain ⟨δ, hδ, hclose⟩ : ∃ δ > 0, ∀ t, dist t t₀ < δ → dist (g t) (g t₀) < a :=
    Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hg.continuousAt a ha)
  let t₁ := t₀ + min δ (1 - t₀) / 2
  have hmin : 0 < min δ (1 - t₀) := lt_min hδ (sub_pos.mpr ht₀₁)
  have ht₀₁' : t₀ < t₁ := by dsimp [t₁]; linarith
  have ht₁ : t₁ ∈ Icc (0 : ℝ) 1 := by
    have hm := min_le_right δ (1 - t₀)
    dsimp [t₁]
    constructor <;> linarith [ht₀.1.1]
  have hdist : dist t₁ t₀ < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht₀₁')]
    have hm := min_le_left δ (1 - t₀)
    dsimp [t₁]
    linarith
  have hx₁ : a < (g t₁).1 := by
    by_contra! H
    obtain ⟨t, ht, heq⟩ := exists_level_between hfst ht₁.2
      (show a ∈ Icc (g t₁).1 (g 1).1 from ⟨H, by linarith⟩)
    have htA : t ∈ A := ⟨⟨ht₁.1.trans ht.1, ht.2⟩, heq⟩
    have H := le_csSup hA.bddAbove htA
    linarith [ht.1]
  have hx₁upper : (g t₁).1 < radius n := by
    have H : dist (g t₁).1 (g t₀).1 ≤ dist (g t₁) (g t₀) := le_max_left _ _
    have H' := H.trans_lt (hclose t₁ hdist)
    rw [Real.dist_eq, ht₀.2, abs_of_pos (sub_pos.mpr hx₁)] at H'
    linarith
  have hosc (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
      ∃ t, dist (g t) (g t₀) < a ∧ (g t).2 = radius n * y := by
    obtain ⟨u, hu, hsin⟩ := TopologistsSineCurve.exists_mem_Ioc_of_y hy
      (show 0 < ((g t₁).1 - a) / a from div_pos (sub_pos.mpr hx₁) ha)
    let x := a + a * u
    have hax : a < x := by dsimp [x]; nlinarith [hu.1]
    have hxu : x ≤ (g t₁).1 := by
      have H := (le_div_iff₀ ha).mp hu.2
      dsimp [x]
      nlinarith
    obtain ⟨t, ht, heq⟩ := exists_level_between hfst ht₀₁'.le
      (show x ∈ Icc (g t₀).1 (g t₁).1 from ⟨ht₀.2.symm ▸ hax.le, hxu⟩)
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1.1.trans ht.1, ht.2.trans ht₁.2⟩
    have htclose : dist (g t) (g t₀) < a := by
      apply hclose
      exact (dist_right_le_of_mem_uIcc (Icc_subset_uIcc' ht)).trans_lt hdist
    have htcopy := mem_copy_of_strip (hmem t htI) (by rwa [heq]) (by rw [heq]; exact hxu.trans_lt hx₁upper)
    obtain ⟨p, hp, hp_eq⟩ := htcopy
    have hp₁ : a * (1 + p.1) = x := (congrArg Prod.fst hp_eq).trans heq
    have hpu : p.1 = u := by dsimp [x] at hp₁; nlinarith
    have hp₂ := base_snd_of_pos hp (hpu.symm ▸ hu.1)
    refine ⟨t, htclose, ?_⟩
    have H : radius n * p.2 = (g t).2 := congrArg Prod.snd hp_eq
    rw [hp₂, hpu, hsin] at H
    exact H.symm
  obtain ⟨tPlus, htPlus, hyPlus⟩ := hosc 1 (by norm_num)
  obtain ⟨tMinus, htMinus, hyMinus⟩ := hosc (-1) (by norm_num)
  have hd : dist (g tPlus) (g tMinus) < 2 * a :=
    (dist_triangle_right _ _ (g t₀)).trans_lt (by linarith)
  have H : dist (g tPlus).2 (g tMinus).2 ≤ dist (g tPlus) (g tMinus) := le_max_right _ _
  rw [Real.dist_eq, hyPlus, hyMinus, mul_one, mul_neg_one,
    sub_neg_eq_add, abs_of_pos (by linarith [radius_pos n])] at H
  linarith

theorem pathComponentIn_chain_zero : pathComponentIn chain 0 = {0} := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨γ, hγ⟩ := hq
    have H := no_curve_from_zero γ.continuous_extend γ.extend_zero (fun t ht => by
      simpa only [γ.extend_extends' ⟨t, ht⟩] using hγ ⟨t, ht⟩)
    simpa only [γ.extend_one, mem_singleton_iff] using H
  · intro q hq
    rcases hq with rfl
    exact mem_pathComponentIn_self zero_mem_chain

end EremenkosConjecture.SineContinuum
