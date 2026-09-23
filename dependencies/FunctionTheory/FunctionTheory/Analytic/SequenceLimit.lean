import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Summably close holomorphic maps on one fixed open domain have a uniform
holomorphic limit, without a boundedness assumption on the domain or maps. -/
theorem exists_analytic_uniform_limit_of_summable_increments
    {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (v : ℕ → ℝ) (hv : Summable v)
    (hbound : ∀ i z, z ∈ U → ‖F (i + 1) z - F i z‖ ≤ v i) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ TendstoUniformlyOn F f atTop U := by
  let u : ℕ → ℂ → ℂ := fun i z => F (i + 1) z - F i z
  let f : ℂ → ℂ := fun z => F 0 z + ∑' i, u i z
  have Htel : ∀ N z, (∑ i ∈ Finset.range N, u i z) = F N z - F 0 z := by
    intro N
    induction N with
    | zero => intro z; simp
    | succ N ih =>
      intro z
      rw [Finset.sum_range_succ, ih z]
      dsimp [u]
      abel
  have HU := tendstoUniformlyOn_tsum_nat (f := u) hv hbound
  have Hconv : TendstoUniformlyOn F f atTop U := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp HU ε hε] with N hN
    intro z hz
    have H := hN z hz
    rw [Htel N z] at H
    calc
      dist (f z) (F N z) = dist (∑' i, u i z) (F N z - F 0 z) := by
        dsimp [f]
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      _ < ε := H
  refine ⟨f, ?_, Hconv⟩
  exact (Hconv.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (fun i => (hF i).differentiableOn)) hU).analyticOnNhd hU

/-- Uniform convergence on a neighbourhood permits evaluation at moving
points. This is the limit passage in the finite conjugacy identities. -/
theorem tendsto_uniformlyOn_at_moving_points
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f atTop U)
    {x : ℕ → ℂ} {a : ℂ} (hx : Tendsto x atTop (𝓝 a))
    (ha : a ∈ U) (hf : ContinuousAt f a) :
    Tendsto (fun i => F i (x i)) atTop (𝓝 (f a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 2 := half_pos hε
  have H1 := Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) he
  have H2 := Metric.tendsto_nhds.mp (hf.tendsto.comp hx) (ε / 2) he
  filter_upwards [H1, H2, hx.eventually (hU.mem_nhds ha)] with i hi hi' hiU
  have hdist : dist (F i (x i)) (f (x i)) < ε / 2 := by
    simpa only [dist_comm] using hi (x i) hiU
  calc
    dist (F i (x i)) (f a) ≤ dist (F i (x i)) (f (x i)) + dist (f (x i)) (f a) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdist hi'
    _ = ε := add_halves ε

end FunctionTheory
