import FunctionTheory.Smooth.SequenceLimit
import FunctionTheory.Smooth.ComplexSeriesDerivative
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Smooth conjugacy limits retain the Cauchy--Riemann equations on a closed
model set, even when the holomorphic neighbourhoods shrink with the stage.
The small total derivative error also supplies a smooth global inverse. -/
theorem exists_smooth_complex_diffeomorphism_limit_of_close_sequence
    (F : ℕ → ℂ → ℂ) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hF0 : ∀ z, F 0 z = z) (m : ℕ) (hm : 1 ≤ m)
    (v : ℕ → ℝ) (hv : Summable v)
    (hbound : ∀ k i, k ≤ max m (i + 1) → ∀ z,
      ‖iteratedFDeriv ℝ k (fun w => F (i + 1) w - F i w) z‖ ≤ v i)
    (hsmall : (∑' i, v i) < 1) (K : Set ℂ)
    (hcomplex : ∀ i, ∀ a ∈ K, DifferentiableAt ℂ (F i) a) :
    ∃ e : ℂ ≃ₜ ℂ,
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      TendstoUniformly F (e : ℂ → ℂ) atTop ∧
      (∀ k ≤ m, ∀ z,
        ‖iteratedFDeriv ℝ k (fun w => e w - w) z‖ ≤ ∑' i, v i) ∧
      (∀ A : Set ℂ, (∀ i, EqOn (F i) id A) → EqOn (e : ℂ → ℂ) id A) ∧
      ∀ a ∈ K, DifferentiableAt ℂ (e : ℂ → ℂ) a := by
  obtain ⟨e, he, hei, hconv, hnorm, hfix⟩ :=
    exists_smooth_diffeomorphism_limit_of_close_sequence F hF hF0 m hm v hv hbound hsmall
  let u : ℕ → ℂ → ℂ := fun i z => F (i + 1) z - F i z
  have hu : ∀ i, ContDiff ℝ ∞ (u i) := fun i => (hF (i + 1)).sub (hF i)
  have H0 : ∀ i z, ‖u i z‖ ≤ v i := by
    intro i z
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 i (Nat.zero_le _) z
  have H1 : ∀ i z, ‖fderiv ℝ (u i) z‖ ≤ v i := by
    intro i z
    simpa only [norm_iteratedFDeriv_one] using
      hbound 1 i (hm.trans (le_max_left m (i + 1))) z
  have Hsum : ∀ z, Summable (fun i => u i z) :=
    fun z => Summable.of_norm_bounded hv (fun i => H0 i z)
  have Htel : ∀ N z, (∑ i ∈ Finset.range N, u i z) = F N z - z := by
    intro N
    induction N with
    | zero => intro z; simp [hF0]
    | succ N ih =>
      intro z
      rw [Finset.sum_range_succ, ih z]
      dsimp [u]
      abel
  have Heq : (e : ℂ → ℂ) = (fun z => z + ∑' i, u i z) := by
    funext z
    have H : Tendsto (fun N => z + ∑ i ∈ Finset.range N, u i z) atTop
        (𝓝 (z + ∑' i, u i z)) :=
      tendsto_const_nhds.add (Hsum z).hasSum.tendsto_sum_nat
    have Hfun : (fun N => z + ∑ i ∈ Finset.range N, u i z) = (fun N => F N z) := by
      funext N
      rw [Htel N z]
      abel
    rw [Hfun] at H
    exact tendsto_nhds_unique (hconv.tendsto_at z) H
  refine ⟨e, he, hei, hconv, hnorm, hfix, ?_⟩
  intro a ha
  rw [Heq]
  apply differentiableAt_id.add
  exact (hasFDerivAt_complex_tsum_of_real_control u
    (fun i => (hu i).differentiable (by simp)) v hv H1 (Hsum 0)
    (fun i => (hcomplex (i + 1) a ha).sub (hcomplex i a ha))).differentiableAt

end FunctionTheory
