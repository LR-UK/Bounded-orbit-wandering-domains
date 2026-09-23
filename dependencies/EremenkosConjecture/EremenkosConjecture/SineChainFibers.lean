import EremenkosConjecture.SineChain
import EremenkosConjecture.VerticalFibers

open Set Metric Filter Topology Real

namespace EremenkosConjecture.SineContinuum

theorem base_vertical_fibers (x : ℝ) : OrdConnected {y : ℝ | (x, y) ∈ base} := by
  constructor
  intro u hu v hv y hy
  have hx := (base_coordinates hu).1.1
  change 0 ≤ x at hx
  rcases hx.eq_or_lt with hx | hx
  · subst x
    exact vertical_mem_base ⟨(base_coordinates hu).2.1.trans hy.1,
      hy.2.trans (base_coordinates hv).2.2⟩
  · have hu' := base_snd_of_pos hu hx
    have hv' := base_snd_of_pos hv hx
    dsimp at hu' hv'
    have hyu : y = u := by linarith [hy.1, hy.2]
    simpa only [hyu] using hu

theorem copy_vertical_fibers (n : ℕ) (x : ℝ) : OrdConnected {y : ℝ | (x, y) ∈ copy n} := by
  constructor
  intro u hu v hv y hy
  obtain ⟨p, hp, heqp⟩ := hu
  obtain ⟨q, hq, heqq⟩ := hv
  have hp₁ : radius (n + 1) * (1 + p.1) = x := congrArg Prod.fst heqp
  have hq₁ : radius (n + 1) * (1 + q.1) = x := congrArg Prod.fst heqq
  have hp₂ : radius n * p.2 = u := congrArg Prod.snd heqp
  have hq₂ : radius n * q.2 = v := congrArg Prod.snd heqq
  have hpq : p.1 = q.1 := by nlinarith [radius_pos (n + 1)]
  have hq' : (p.1, q.2) ∈ base := by simpa only [hpq] using hq
  have hr : 0 < radius n := radius_pos n
  have hy' : y / radius n ∈ Icc p.2 q.2 := by
    constructor
    · apply (le_div_iff₀ hr).mpr
      nlinarith [hy.1]
    · apply (div_le_iff₀ hr).mpr
      nlinarith [hy.2]
  refine ⟨(p.1, y / radius n), (base_vertical_fibers p.1).out hp hq' hy', ?_⟩
  apply Prod.ext
  · exact hp₁
  · dsimp [copyMap]
    field_simp [ne_of_gt hr]

theorem mem_copy_of_same_fst {m n : ℕ} (hmn : m ≤ n) {p q : ℝ × ℝ}
    (hp : p ∈ copy m) (hq : q ∈ copy n) (heq : p.1 = q.1) : q ∈ copy m := by
  rcases hmn.eq_or_lt with rfl | hmn
  · exact hq
  have hx : q.1 = radius (m + 1) := by
    apply le_antisymm
    · exact (copy_bounds hq).1.2.trans (radius_antitone (Nat.succ_le_of_lt hmn))
    · rw [← heq]
      exact (copy_bounds hp).1.1
  have hy : |q.2| ≤ radius m :=
    (copy_bounds hq).2.trans (radius_antitone hmn.le)
  refine ⟨(0, q.2 / radius m), vertical_mem_base ?_, ?_⟩
  · change -1 ≤ q.2 / radius m ∧ q.2 / radius m ≤ 1
    rw [← abs_le, abs_div, abs_of_pos (radius_pos m)]
    exact (div_le_one (radius_pos m)).mpr hy
  · apply Prod.ext
    · simpa only [copyMap, add_zero, mul_one] using hx.symm
    · dsimp [copyMap]
      field_simp [ne_of_gt (radius_pos m)]

theorem chain_vertical_fibers (x : ℝ) : OrdConnected {y : ℝ | (x, y) ∈ chain} := by
  constructor
  intro u hu v hv y hy
  by_cases hx : x = 0
  · have hz (w : ℝ) (hw : (x, w) ∈ chain) : w = 0 := by
      rcases mem_chain_iff.mp hw with H | ⟨n, hn⟩
      · exact congrArg Prod.snd H
      · have H := (radius_pos (n + 1)).trans_le (copy_bounds hn).1.1
        simpa only [hx, lt_self_iff_false] using H
    have hu0 := hz u hu
    have hv0 := hz v hv
    have hy0 : y = 0 := by linarith [hy.1, hy.2]
    change (x, y) ∈ chain
    simpa only [hx, hy0, Prod.zero_eq_mk] using zero_mem_chain
  · obtain hu0 | ⟨m, hm⟩ := mem_chain_iff.mp hu
    · exact (hx (congrArg Prod.fst hu0)).elim
    obtain hv0 | ⟨n, hn⟩ := mem_chain_iff.mp hv
    · exact (hx (congrArg Prod.fst hv0)).elim
    rcases le_total m n with hmn | hnm
    · have hn' := mem_copy_of_same_fst hmn hm hn rfl
      exact mem_chain_iff.mpr (Or.inr ⟨m, (copy_vertical_fibers m x).out hm hn' hy⟩)
    · have hm' := mem_copy_of_same_fst hnm hn hm rfl
      exact mem_chain_iff.mpr (Or.inr ⟨n, (copy_vertical_fibers n x).out hm' hn hy⟩)

noncomputable def complexChain : Set ℂ := Complex.equivRealProdCLM.symm '' chain

theorem isCompact_complexChain : IsCompact complexChain :=
  isCompact_chain.image Complex.equivRealProdCLM.symm.continuous

theorem isConnected_complexChain : IsConnected complexChain :=
  isConnected_chain.image _ Complex.equivRealProdCLM.symm.continuous.continuousOn

theorem mem_complexChain_iff (z : ℂ) : z ∈ complexChain ↔ (z.re, z.im) ∈ chain := by
  change z ∈ Complex.equivRealProdCLM.symm '' chain ↔ Complex.equivRealProdCLM z ∈ chain
  exact (Equiv.image_symm_eq_preimage _ _ ▸ Iff.rfl)

theorem isConnected_compl_complexChain : IsConnected complexChainᶜ := by
  apply isConnected_compl_of_vertical_fibers isCompact_complexChain.isBounded
  intro x
  have heq : {y : ℝ | (⟨x, y⟩ : ℂ) ∈ complexChain} = {y : ℝ | (x, y) ∈ chain} := by
    ext y
    exact mem_complexChain_iff _
  rw [heq]
  exact chain_vertical_fibers x

end EremenkosConjecture.SineContinuum
