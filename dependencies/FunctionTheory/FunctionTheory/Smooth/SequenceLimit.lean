import FunctionTheory.Smooth.SeriesDiffeomorphism
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Quantitative smooth convergence of successive corrections starting at
the identity. Increasing derivative control gives smoothness of the limit;
the small total first-derivative error gives global invertibility. -/
theorem exists_smooth_diffeomorphism_limit_of_close_sequence
    (F : ℕ → ℂ → ℂ) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hF0 : ∀ z, F 0 z = z) (m : ℕ) (hm : 1 ≤ m)
    (v : ℕ → ℝ) (hv : Summable v)
    (hbound : ∀ k i, k ≤ max m (i + 1) → ∀ z,
      ‖iteratedFDeriv ℝ k (fun w => F (i + 1) w - F i w) z‖ ≤ v i)
    (hsmall : (∑' i, v i) < 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      TendstoUniformly F (e : ℂ → ℂ) atTop ∧
      (∀ k ≤ m, ∀ z,
        ‖iteratedFDeriv ℝ k (fun w => e w - w) z‖ ≤ ∑' i, v i) ∧
      ∀ A : Set ℂ, (∀ i, EqOn (F i) id A) → EqOn (e : ℂ → ℂ) id A := by
  let u : ℕ → ℂ → ℂ := fun i z => F (i + 1) z - F i z
  have hu : ∀ i, ContDiff ℝ ∞ (u i) := fun i => (hF (i + 1)).sub (hF i)
  obtain ⟨e, he, hes, hei, heBound, _⟩ :=
    exists_smooth_diffeomorphism_of_increasing_derivative_control
      u hu m hm v hv hbound hsmall
  have Hsum : ∀ N z, (∑ i ∈ Finset.range N, u i z) = F N z - z := by
    intro N
    induction N with
    | zero => intro z; simp [hF0]
    | succ N ih =>
      intro z
      rw [Finset.sum_range_succ, ih z]
      dsimp [u]
      abel
  have H0 : ∀ i z, ‖u i z‖ ≤ v i := by
    intro i z
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 i (Nat.zero_le _) z
  have HU := tendstoUniformly_tsum_nat hv H0
  have He : TendstoUniformly F (e : ℂ → ℂ) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp HU ε hε] with N hN
    intro z
    have H := hN z
    rw [Hsum N z] at H
    calc
      dist (e z) (F N z) = dist (∑' i, u i z) (F N z - z) := by
        rw [he z, dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      _ < ε := H
  refine ⟨e, hes, hei, He, heBound, ?_⟩
  intro A HA z hz
  have Hlim := He.tendsto_at z
  have Hconst : (fun i => F i z) = (fun _ : ℕ => z) := by
    funext i
    exact HA i hz
  rw [Hconst] at Hlim
  exact tendsto_nhds_unique Hlim tendsto_const_nhds

end FunctionTheory
