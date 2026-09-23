import EremenkosConjecture.BoundaryGates
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Compact

/-! # Alternating openings prohibit paths across nested boundaries -/

open Set Metric Filter Function
open scoped Topology

namespace EremenkosConjecture

private theorem last_parameter_mem_frontier {g : ℝ → ℂ} (hg : Continuous g)
    {L : Set ℂ} (hL : IsClosed L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hmem : g t ∈ L) (hend : g 1 ∉ L)
    (hlast : ∀ s ∈ Icc (0 : ℝ) 1, g s ∈ L → s ≤ t) :
    g t ∈ frontier L := by
  refine ⟨hL.closure_eq.symm ▸ hmem, ?_⟩
  intro hi
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (fun h => hend (h ▸ hmem))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_interior.preimage hg) t hi
  let s := t + min δ (1 - t) / 2
  have hm : 0 < min δ (1 - t) := lt_min hδ (sub_pos.mpr ht1)
  have hsI : s ∈ Icc (0 : ℝ) 1 := by
    have hle := min_le_right δ (1 - t)
    dsimp [s]
    constructor <;> linarith [ht.1]
  have hst : t < s := by dsimp [s]; linarith
  have hsball : s ∈ ball t δ := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hst)]
    have hle := min_le_left δ (1 - t)
    dsimp [s]
    linarith
  exact (not_lt_of_ge (hlast s hsI (interior_subset (hball hsball)))) hst

/-- A curve cannot cross nested compact boundaries if its only available
openings shrink alternately towards two distinct points. -/
theorem no_curve_through_alternating_openings
    (K : Set ℂ) (L P : ℕ → Set ℂ) (hclosed : ∀ n, IsClosed (L n))
    (hanti : Antitone L) (hKL : ∀ n, K ⊆ L n) (hcap : (⋂ n, L n) = K)
    (a b : ℂ) (hab : a ≠ b) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hgate₀ : ∀ n z, z ∈ frontier (L (2 * n)) → z ∉ P (2 * n) → dist z a ≤ ε (2 * n))
    (hgate₁ : ∀ n z, z ∈ frontier (L (2 * n + 1)) → z ∉ P (2 * n + 1) → dist z b ≤ ε (2 * n + 1))
    {g : ℝ → ℂ} (hg : Continuous g) (hstart : g 0 ∈ K) (hend : g 1 ∉ K)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, g t ∉ P n) : False := by
  let T : ℕ → Set ℝ := fun n => Icc 0 1 ∩ g ⁻¹' L n
  have hTcompact (n : ℕ) : IsCompact (T n) :=
    isCompact_Icc.inter_right ((hclosed n).preimage hg)
  have hTne (n : ℕ) : (T n).Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, hKL n hstart⟩
  let t : ℕ → ℝ := fun n => sSup (T n)
  have ht (n : ℕ) : t n ∈ T n := (hTcompact n).sSup_mem (hTne n)
  have htanti : Antitone t := by
    intro n m hnm
    exact csSup_le_csSup (hTcompact n).bddAbove (hTne m)
      (inter_subset_inter_right _ (preimage_mono (hanti hnm)))
  have htlim : Tendsto t atTop (𝓝 (⨅ n, t n)) :=
    tendsto_atTop_ciInf htanti ⟨0, by rintro _ ⟨n, rfl⟩; exact (ht n).1.1⟩
  have hglim : Tendsto (fun n => g (t n)) atTop (𝓝 (g (⨅ n, t n))) := hg.continuousAt.tendsto.comp htlim
  have hex : ∃ N, g 1 ∉ L N := by
    by_contra! H
    exact hend (hcap ▸ mem_iInter.mpr H)
  obtain ⟨N, hN⟩ := hex
  have hfront : ∀ᶠ n in atTop, g (t n) ∈ frontier (L n) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply last_parameter_mem_frontier hg (hclosed n) (ht n).1 (ht n).2
      (fun h => hN (hanti hn h))
    intro s hs hmem
    exact le_csSup (hTcompact n).bddAbove ⟨hs, hmem⟩
  have h0 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    (show StrictMono (fun n : ℕ => 2 * n) by intro i j hij; dsimp; omega).tendsto_atTop
  have h1 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    (show StrictMono (fun n : ℕ => 2 * n + 1) by intro i j hij; dsimp; omega).tendsto_atTop
  have heqa : g (⨅ n, t n) = a := by
    apply dist_le_zero.mp
    apply le_of_tendsto_of_tendsto ((hglim.comp h0).dist tendsto_const_nhds) (hε.comp h0)
    filter_upwards [h0.eventually hfront] with n hn
    exact hgate₀ n _ hn (havoid _ (ht (2 * n)).1 _)
  have heqb : g (⨅ n, t n) = b := by
    apply dist_le_zero.mp
    apply le_of_tendsto_of_tendsto ((hglim.comp h1).dist tendsto_const_nhds) (hε.comp h1)
    filter_upwards [h1.eventually hfront] with n hn
    exact hgate₁ n _ hn (havoid _ (ht (2 * n + 1)).1 _)
  exact hab (heqa.symm.trans heqb)

end EremenkosConjecture
