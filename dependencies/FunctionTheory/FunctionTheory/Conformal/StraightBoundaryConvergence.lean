import FunctionTheory.Conformal.UniformStraightBoundary
import FunctionTheory.Conformal.StraightBoundaryContinuous

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

theorem dist_boundary_limit_le_of_boundary_cap
    {U : Set ℂ} {f : ℂ → ℂ} {ξ a : ℂ} {r δ : ℝ}
    (hcl : (0 : ℂ) ∈ closure (U ∩ {z : ℂ | 0 < z.re})) (hr : 0 < r)
    (hlim : Tendsto f (𝓝[U ∩ {z : ℂ | 0 < z.re}] 0) (𝓝 ξ))
    (hcap : ∀ z ∈ U ∩ ball (0 : ℂ) r, 0 < z.re → f z ∈ closedBall a δ) :
    ∀ z ∈ U ∩ ball (0 : ℂ) r, 0 < z.re → dist (f z) ξ ≤ 2 * δ := by
  let S := U ∩ {z : ℂ | 0 < z.re}
  have : (𝓝[S] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hevent : ∀ᶠ z in 𝓝[S] (0 : ℂ), f z ∈ closedBall a δ := by
    have hb : ∀ᶠ z in 𝓝[S] (0 : ℂ), z ∈ ball (0 : ℂ) r :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [self_mem_nhdsWithin, hb] with z hz hzb
    exact hcap z ⟨hz.1, hzb⟩ hz.2
  have hξ : ξ ∈ closedBall a δ := isClosed_closedBall.mem_of_tendsto hlim hevent
  intro z hz hp
  have h1 := mem_closedBall.mp (hcap z hz hp)
  have h2 := mem_closedBall.mp hξ
  have h3 := dist_triangle (f z) a ξ
  rw [dist_comm a ξ] at h3
  linarith

/-- At a common straight boundary, fixed-basepoint disk maps inherit
convergence of boundary values from ordinary interior convergence. Uniform
crosscut caps provide the needed control; global boundary continuity and
local connectedness elsewhere are unnecessary. -/
theorem boundary_limits_tendsto_of_common_straight_side
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {ξ : ℕ → ℂ} {ξ₀ z₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hz₀ne : z₀ ≠ 0)
    (hU : ∀ n, IsOpen (U n)) (hF : ∀ n, DifferentiableOn ℂ (F n) (U n))
    (hFb : ∀ n, BijOn (F n) (U n) (ball 0 1))
    (hz₀U : ∀ n, z₀ ∈ U n) (hF0 : ∀ n, F n z₀ = 0)
    (hhalf : ∀ n, ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ U n)
    (hline : ∀ n, ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ∉ U n)
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hfb : BijOn f V (ball 0 1))
    (hz₀V : z₀ ∈ V) (hf0 : f z₀ = 0)
    (hvhalf : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ V)
    (hvline : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → z ∉ V)
    (hξ : ∀ n, Tendsto (F n) (𝓝[U n ∩ {z : ℂ | 0 < z.re}] 0) (𝓝 (ξ n)))
    (hξ₀ : Tendsto f (𝓝[V ∩ {z : ℂ | 0 < z.re}] 0) (𝓝 ξ₀))
    (hconv : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → Tendsto (fun n => F n z) atTop (𝓝 (f z))) :
    Tendsto ξ atTop (𝓝 ξ₀) := by
  have hcl {W : Set ℂ}
      (hh : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → z ∈ W) :
      (0 : ℂ) ∈ closure (W ∩ {z : ℂ | 0 < z.re}) := by
    apply closure_mono (show ball (0 : ℂ) R ∩ {z : ℂ | 0 < z.re} ⊆
        W ∩ {z : ℂ | 0 < z.re} from fun z hz => ⟨hh z hz.1 hz.2, hz.2⟩)
    exact mem_closure_right_half_ball (by simpa using hR) (by simp)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (ε / 16) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨r, hr, hcap⟩ := exists_uniform_boundary_cap_at_straight_side hz₀ne hR hδ hδ1
  let t := min r R / 2
  have ht : 0 < t := half_pos (lt_min hr hR)
  have htr : t < r := (half_lt_self (lt_min hr hR)).trans_le (min_le_left _ _)
  have htR : t < R := (half_lt_self (lt_min hr hR)).trans_le (min_le_right _ _)
  have hub : (t : ℂ) ∈ ball (0 : ℂ) R := by simpa [abs_of_pos ht] using htR
  have hur : (t : ℂ) ∈ ball (0 : ℂ) r := by simpa [abs_of_pos ht] using htr
  have hupos : 0 < (t : ℂ).re := by simpa using ht
  have hdist (n : ℕ) : dist (F n (t : ℂ)) (ξ n) ≤ 2 * δ := by
    obtain ⟨a, _, ha⟩ := hcap (U n) (F n) (hU n) (hF n) (hFb n) (hz₀U n)
      (hF0 n) (hhalf n) (hline n)
    exact dist_boundary_limit_le_of_boundary_cap (hcl (hhalf n)) hr (hξ n) ha
      (t : ℂ) ⟨hhalf n _ hub hupos, hur⟩ hupos
  obtain ⟨a, _, ha⟩ := hcap V f hV hf hfb hz₀V hf0 hvhalf hvline
  have hdistf := dist_boundary_limit_le_of_boundary_cap (hcl hvhalf) hr hξ₀ ha
    (t : ℂ) ⟨hvhalf _ hub hupos, hur⟩ hupos
  filter_upwards [Metric.tendsto_nhds.mp (hconv _ hub hupos) (ε / 2) (half_pos hε)] with n hn
  have hnξ := hdist n
  have htri1 := dist_triangle (ξ n) (F n (t : ℂ)) ξ₀
  have htri2 := dist_triangle (F n (t : ℂ)) (f (t : ℂ)) ξ₀
  rw [dist_comm (ξ n) (F n (t : ℂ))] at htri1
  have hδε : δ ≤ ε / 16 := min_le_left _ _
  linarith

end FunctionTheory
