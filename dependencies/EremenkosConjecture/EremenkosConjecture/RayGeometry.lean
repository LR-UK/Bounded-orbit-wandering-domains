import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # Horizontal rays and their closed half-strip neighbourhoods -/

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

def horizontalRay (ζ : ℂ) : Set ℂ := {z | ζ.re ≤ z.re ∧ z.im = ζ.im}

def closedHalfStrip (ζ : ℂ) (a b : ℝ) : Set ℂ :=
  {z | ζ.re - a ≤ z.re ∧ |z.im - ζ.im| ≤ b}

theorem mem_horizontalRay (ζ : ℂ) : ζ ∈ horizontalRay ζ := ⟨le_rfl, rfl⟩

theorem isClosed_horizontalRay (ζ : ℂ) : IsClosed (horizontalRay ζ) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem isConnected_horizontalRay (ζ : ℂ) : IsConnected (horizontalRay ζ) := by
  have he : horizontalRay ζ = (fun t : ℝ => (t : ℂ) + (ζ.im : ℂ) * I) '' Ici ζ.re := by
    ext z
    constructor
    · intro hz
      exact ⟨z.re, hz.1, by apply Complex.ext <;> simp [hz.2]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simpa using ht, by simp⟩
  rw [he]
  exact isConnected_Ici.image _ (Complex.continuous_ofReal.add continuous_const).continuousOn

theorem frontier_horizontalRay (ζ : ℂ) : frontier (horizontalRay ζ) = horizontalRay ζ := by
  apply Subset.antisymm (frontier_subset_iff_isClosed.mpr (isClosed_horizontalRay ζ))
  intro z hz
  refine ⟨(isClosed_horizontalRay ζ).closure_eq.symm ▸ hz, ?_⟩
  intro hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hw : z + (r / 2 : ℝ) * I ∈ horizontalRay ζ := by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have him := hw.2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] at him
  linarith [hz.2]

theorem isClosed_closedHalfStrip (ζ : ℂ) (a b : ℝ) : IsClosed (closedHalfStrip ζ a b) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le (Complex.continuous_im.sub continuous_const).abs continuous_const)

theorem horizontalRay_subset_interior_halfStrip {ζ : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : horizontalRay ζ ⊆ interior (closedHalfStrip ζ a b) := by
  let U : Set ℂ := {z | ζ.re - a < z.re ∧ |z.im - ζ.im| < b}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const)
  have hsub : U ⊆ closedHalfStrip ζ a b := fun _ h => ⟨h.1.le, h.2.le⟩
  intro z hz
  have hzU : z ∈ U := ⟨by linarith [hz.1], by simpa [hz.2] using hb⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hzU) hsub)

theorem mem_frontier_halfStrip_top {ζ z : ℂ} {a b : ℝ}
    (hb : 0 ≤ b) (hre : ζ.re - a ≤ z.re) (him : z.im = ζ.im + b) :
    z ∈ frontier (closedHalfStrip ζ a b) := by
  have hz : z ∈ closedHalfStrip ζ a b := ⟨hre, by simp [him, abs_of_nonneg hb]⟩
  refine ⟨(isClosed_closedHalfStrip ζ a b).closure_eq.symm ▸ hz, ?_⟩
  intro hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hw : z + (r / 2 : ℝ) * I ∈ closedHalfStrip ζ a b := by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hwi := (abs_le.mp hw.2).2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] at hwi
  linarith

theorem exists_unbounded_frontier_sequence {ζ : ℂ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (closedHalfStrip ζ a b)) ∧
      Tendsto (fun n => ‖u n‖) atTop atTop := by
  let u : ℕ → ℂ := fun n => ζ + (n : ℂ) + (b : ℂ) * I
  refine ⟨u, ?_, ?_⟩
  · intro n
    apply mem_frontier_halfStrip_top hb
    · dsimp [u]
      simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · simp [u]
  · have hRe : Tendsto (fun n => (u n).re) atTop atTop := by
      simpa [u] using (tendsto_const_nhds (x := ζ.re)).add_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ))
    exact tendsto_atTop_mono (fun n => Complex.re_le_norm (u n)) hRe

end EremenkosConjecture

namespace EremenkosConjecture

theorem iInter_closedHalfStrip_eq_ray {ζ : ℂ} {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (ha0 : Tendsto a atTop (𝓝 0)) (hb0 : Tendsto b atTop (𝓝 0)) :
    (⋂ n, closedHalfStrip ζ (a n) (b n)) = horizontalRay ζ := by
  ext z
  constructor
  · intro hz
    have hza : ζ.re - z.re ≤ 0 := ge_of_tendsto ha0
      (Filter.Eventually.of_forall fun n => by have := (mem_iInter.mp hz n).1; linarith)
    have hzb : |z.im - ζ.im| ≤ 0 := ge_of_tendsto hb0
      (Filter.Eventually.of_forall fun n => (mem_iInter.mp hz n).2)
    exact ⟨by linarith, sub_eq_zero.mp (abs_nonpos_iff.mp hzb)⟩
  · intro hz
    exact mem_iInter.mpr fun n => ⟨by have := ha n; linarith [hz.1], by simpa [hz.2] using hb n⟩

end EremenkosConjecture
