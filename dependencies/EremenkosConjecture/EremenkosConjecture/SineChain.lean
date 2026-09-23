import EremenkosConjecture.TruncatedSineCurve
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Filter Topology Real

namespace EremenkosConjecture.SineContinuum

noncomputable def radius (n : ℕ) : ℝ := (1 / 2) ^ n

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

theorem radius_step (n : ℕ) : radius (n + 1) = radius n / 2 := by
  simp only [radius, pow_succ]
  ring

theorem radius_antitone : Antitone radius := by
  apply antitone_nat_of_succ_le
  intro n
  rw [radius_step]
  linarith [radius_pos n]

theorem radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

noncomputable def copyMap (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (radius (n + 1) * (1 + p.1), radius n * p.2)

noncomputable def copy (n : ℕ) : Set (ℝ × ℝ) := copyMap n '' base

theorem continuous_copyMap (n : ℕ) : Continuous (copyMap n) := by
  unfold copyMap
  fun_prop

theorem isCompact_copy (n : ℕ) : IsCompact (copy n) :=
  isCompact_base.image (continuous_copyMap n)

theorem isConnected_copy (n : ℕ) : IsConnected (copy n) :=
  isConnected_base.image (copyMap n) (continuous_copyMap n).continuousOn

theorem copy_bounds {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ copy n) :
    p.1 ∈ Icc (radius (n + 1)) (radius n) ∧ |p.2| ≤ radius n := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hx, hy⟩ := base_coordinates hq
  dsimp [copyMap]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [radius_pos (n + 1), hx.1]
  · rw [radius_step]
    nlinarith [radius_pos n, hx.2]
  · rw [abs_mul, abs_of_pos (radius_pos n)]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr hy) (radius_pos n).le).trans_eq (mul_one _)

theorem copy_norm_le {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ copy n) : ‖p‖ ≤ radius n := by
  obtain ⟨hx, hy⟩ := copy_bounds hp
  rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg ((radius_pos _).le.trans hx.1)]
  exact ⟨hx.2, hy⟩

theorem copies_meet (n : ℕ) : (copy n ∩ copy (n + 1)).Nonempty := by
  refine ⟨(radius (n + 1), radius (n + 1) * sin 1), ?_, ?_⟩
  · refine ⟨(0, sin 1 / 2), vertical_mem_base ?_, ?_⟩
    · constructor <;> nlinarith [neg_one_le_sin (1 : ℝ), sin_le_one (1 : ℝ)]
    · ext <;> simp only [copyMap, add_zero, mul_one, radius_step] <;> ring
  · refine ⟨(1, sin 1), right_mem_base, ?_⟩
    ext <;> simp only [copyMap, radius_step] <;> ring

noncomputable def chain : Set (ℝ × ℝ) := closure (⋃ n, copy n)

theorem isCompact_chain : IsCompact chain := by
  apply (isCompact_closedBall (0 : ℝ × ℝ) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  rintro p ⟨_, ⟨n, rfl⟩, hp⟩
  rw [mem_closedBall, dist_zero_right]
  exact (copy_norm_le hp).trans (radius_antitone (Nat.zero_le n))

theorem isConnected_chain : IsConnected chain :=
  (IsConnected.iUnion_of_chain isConnected_copy copies_meet).closure

theorem zero_mem_chain : (0 : ℝ × ℝ) ∈ chain := by
  have hlim : Tendsto (fun n => copyMap n (1, sin 1)) atTop (𝓝 (0 : ℝ × ℝ)) := by
    have hlim₁ := radius_tendsto.comp (tendsto_add_atTop_nat 1)
    simpa only [copyMap, zero_mul, Prod.zero_eq_mk, Function.comp_apply] using
      (hlim₁.mul_const (1 + (1 : ℝ))).prodMk_nhds (radius_tendsto.mul_const (sin 1))
  apply isClosed_closure.mem_of_tendsto hlim
  exact .of_forall fun n => subset_closure (mem_iUnion.mpr ⟨n, ⟨_, right_mem_base, rfl⟩⟩)

theorem mem_chain_iff {p : ℝ × ℝ} : p ∈ chain ↔ p = 0 ∨ ∃ n, p ∈ copy n := by
  constructor
  · intro hp
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      obtain ⟨N, hN⟩ := eventually_atTop.mp (radius_tendsto.eventually_lt_const
        (half_pos (norm_pos_iff.mpr hp0)))
      let A : Set (ℝ × ℝ) := ⋃ n ∈ Finset.range N, copy n
      have hA : IsCompact A := (Finset.range N).isCompact_biUnion (fun n _ => isCompact_copy n)
      have hsub : (⋃ n, copy n) ⊆ A ∪ closedBall 0 (‖p‖ / 2) := by
        intro q hq
        obtain ⟨n, hn⟩ := mem_iUnion.mp hq
        by_cases hnN : n < N
        · exact Or.inl (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr hnN, hn⟩⟩)
        · right
          rw [mem_closedBall, dist_zero_right]
          exact (copy_norm_le hn).trans (hN n (Nat.le_of_not_gt hnN)).le
      have H := closure_minimal hsub (hA.isClosed.union isClosed_closedBall) hp
      rcases H with H | H
      · obtain ⟨n, hn⟩ := mem_iUnion.mp H
        obtain ⟨_, hmem⟩ := mem_iUnion.mp hn
        exact ⟨n, hmem⟩
      · rw [mem_closedBall, dist_zero_right] at H
        exact (not_le_of_gt (half_lt_self (norm_pos_iff.mpr hp0)) H).elim
  · rintro (rfl | ⟨n, hn⟩)
    · exact zero_mem_chain
    · exact subset_closure (mem_iUnion.mpr ⟨n, hn⟩)

theorem chain_fst_pos {p : ℝ × ℝ} (hp : p ∈ chain) (hp0 : p ≠ 0) : 0 < p.1 := by
  obtain h | ⟨n, hn⟩ := mem_chain_iff.mp hp
  · exact (hp0 h).elim
  · exact (radius_pos _).trans_le (copy_bounds hn).1.1

/-- In the interior of its horizontal strip, only the corresponding sine copy occurs. -/
theorem mem_copy_of_strip {p : ℝ × ℝ} {n : ℕ} (hp : p ∈ chain)
    (hl : radius (n + 1) < p.1) (hr : p.1 < radius n) : p ∈ copy n := by
  obtain h | ⟨m, hm⟩ := mem_chain_iff.mp hp
  · subst p
    exact (not_lt_of_ge (radius_pos _).le hl).elim
  · obtain hmn | rfl | hnm := lt_trichotomy m n
    · have H := radius_antitone (Nat.succ_le_of_lt hmn)
      exact (not_lt_of_ge (H.trans (copy_bounds hm).1.1) hr).elim
    · exact hm
    · have H := radius_antitone (Nat.succ_le_of_lt hnm)
      exact (not_lt_of_ge ((copy_bounds hm).1.2.trans H) hl).elim

end EremenkosConjecture.SineContinuum
