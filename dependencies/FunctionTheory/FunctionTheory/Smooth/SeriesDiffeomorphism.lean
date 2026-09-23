import FunctionTheory.Smooth.NearIdentitySmooth
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff NNReal

namespace FunctionTheory

set_option autoImplicit false

/-- A normally convergent series of smooth displacements gives a global
smooth diffeomorphism if the sum of the first-derivative bounds is below one.
The result controls every derivative of the limiting displacement and proves
uniform convergence of the derivative sums. -/
theorem exists_smooth_diffeomorphism_of_summable_displacements
    (u : ℕ → ℂ → ℂ) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (v : ℕ → ℕ → ℝ) (hv : ∀ k, Summable (v k))
    (hbound : ∀ k i z, ‖iteratedFDeriv ℝ k (u i) z‖ ≤ v k i)
    (hsmall : (∑' i, v 1 i) < 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = z + ∑' i, u i z) ∧
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      (∀ k z, ‖iteratedFDeriv ℝ k (fun w => e w - w) z‖ ≤ ∑' i, v k i) ∧
      ∀ k, TendstoUniformly
        (fun N z => ∑ i ∈ Finset.range N, iteratedFDeriv ℝ k (u i) z)
        (fun z => iteratedFDeriv ℝ k (fun w => e w - w) z) atTop := by
  let g : ℂ → ℂ := fun z => ∑' i, u i z
  have hg : ContDiff ℝ ∞ g :=
    contDiff_tsum (N := ⊤) hu (fun k _ => hv k) (fun k i z _ => hbound k i z)
  have Hder : ∀ k z, iteratedFDeriv ℝ k g z =
      ∑' i, iteratedFDeriv ℝ k (u i) z := by
    intro k z
    exact iteratedFDeriv_tsum_apply (N := ⊤) hu (fun j _ => hv j)
      (fun j i w _ => hbound j i w) (by simp) z
  have Hnorm : ∀ k z, ‖iteratedFDeriv ℝ k g z‖ ≤ ∑' i, v k i := by
    intro k z
    rw [Hder k z]
    exact tsum_of_norm_bounded (hv k).hasSum (fun i => hbound k i z)
  have hv0 : ∀ i, 0 ≤ v 1 i := fun i =>
    (norm_nonneg (iteratedFDeriv ℝ 1 (u i) 0)).trans (hbound 1 i 0)
  let k : ℝ≥0 := NNReal.mk (∑' i, v 1 i) (tsum_nonneg hv0)
  have hk : k < 1 := by exact_mod_cast hsmall
  have Hfirst : ∀ z, ‖fderiv ℝ g z‖ ≤ (k : ℝ) := by
    intro z
    simpa only [norm_iteratedFDeriv_one, k, NNReal.coe_mk] using Hnorm 1 z
  obtain ⟨e, he, hes, hei⟩ :=
    exists_smooth_homeomorph_eq_add_of_derivative_bound hg hk Hfirst
  have heDiff : (fun w => e w - w) = g := by
    funext w
    rw [he w]
    abel
  refine ⟨e, he, hes, hei, ?_, ?_⟩
  · simpa only [heDiff] using Hnorm
  · intro j
    have H := tendstoUniformly_tsum_nat (hv j) (fun i z => hbound j i z)
    simpa only [heDiff, Hder] using H

/-- The smooth limit criterion used in successive corrections: the number
of controlled derivatives may increase with the stage. The fixed orders
through m retain a uniform bound, while every higher order is controlled
eventually. The small first-derivative total guarantees a smooth inverse. -/
theorem exists_smooth_diffeomorphism_of_increasing_derivative_control
    (u : ℕ → ℂ → ℂ) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (m : ℕ) (hm : 1 ≤ m) (v : ℕ → ℝ) (hv : Summable v)
    (hbound : ∀ k i, k ≤ max m (i + 1) →
      ∀ z, ‖iteratedFDeriv ℝ k (u i) z‖ ≤ v i)
    (hsmall : (∑' i, v i) < 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = z + ∑' i, u i z) ∧
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      (∀ k ≤ m, ∀ z,
        ‖iteratedFDeriv ℝ k (fun w => e w - w) z‖ ≤ ∑' i, v i) ∧
      ∀ k ≤ m, TendstoUniformly
        (fun N z => ∑ i ∈ Finset.range N, iteratedFDeriv ℝ k (u i) z)
        (fun z => iteratedFDeriv ℝ k (fun w => e w - w) z) atTop := by
  let g : ℂ → ℂ := fun z => ∑' i, u i z
  have Hev : ∀ k : ℕ, ∀ᶠ i in (cofinite : Filter ℕ),
      ∀ z, ‖iteratedFDeriv ℝ k (u i) z‖ ≤ v i := by
    intro k
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop k] with i hi
    exact hbound k i ((Nat.le_succ_of_le hi).trans (le_max_right m (i + 1)))
  have hg : ContDiff ℝ ∞ g :=
    contDiff_tsum_of_eventually (N := ⊤) hu (fun _ _ => hv) (fun k _ => Hev k)
  have huM : ∀ i, ContDiff ℝ m (u i) := fun i => (hu i).of_le (by simp)
  have HM : ∀ k i z, k ≤ m → ‖iteratedFDeriv ℝ k (u i) z‖ ≤ v i :=
    fun k i z hk => hbound k i (hk.trans (le_max_left m (i + 1))) z
  have Hder : ∀ k ≤ m, ∀ z, iteratedFDeriv ℝ k g z =
      ∑' i, iteratedFDeriv ℝ k (u i) z := by
    intro k hk z
    exact iteratedFDeriv_tsum_apply (N := m) huM (fun _ _ => hv)
      (fun j i w hj => HM j i w (by exact_mod_cast hj)) (by exact_mod_cast hk) z
  have Hnorm : ∀ k ≤ m, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ ∑' i, v i := by
    intro k hk z
    rw [Hder k hk z]
    exact tsum_of_norm_bounded hv.hasSum (fun i => HM k i z hk)
  have hv0 : ∀ i, 0 ≤ v i := fun i =>
    (norm_nonneg (iteratedFDeriv ℝ 1 (u i) 0)).trans (HM 1 i 0 hm)
  let k : ℝ≥0 := NNReal.mk (∑' i, v i) (tsum_nonneg hv0)
  have hk : k < 1 := by exact_mod_cast hsmall
  have Hfirst : ∀ z, ‖fderiv ℝ g z‖ ≤ (k : ℝ) := by
    intro z
    simpa only [norm_iteratedFDeriv_one, k, NNReal.coe_mk] using Hnorm 1 hm z
  obtain ⟨e, he, hes, hei⟩ :=
    exists_smooth_homeomorph_eq_add_of_derivative_bound hg hk Hfirst
  have heDiff : (fun w => e w - w) = g := by
    funext w
    rw [he w]
    abel
  refine ⟨e, he, hes, hei, ?_, ?_⟩
  · simpa only [heDiff] using Hnorm
  · intro j hj
    have H := tendstoUniformly_tsum_nat hv (fun i z => HM j i z hj)
    simpa only [heDiff, Hder j hj] using H

end FunctionTheory

