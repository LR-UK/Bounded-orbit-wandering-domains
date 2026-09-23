/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.PointOrbitBridge
import BoundedWanderingDomains.LocalDiscInjectivity
import BoundedWanderingDomains.EventualCompactDiscs

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- The conditional entire-function theorem with only one bounded point
orbit. Trapped components replace the potentially unbounded Fatou components;
local inverse branches supply eventual intrinsic-disc injectivity. -/
theorem no_wandering_fatou_orbit_of_bounded_point (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∀ x, ¬EventuallyConst f (𝓝 x))
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hbounded : ∃ R : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ R) :
    ¬ Pairwise (fun n m : ℕ => Disjoint (U n) (U m)) := by
  classical
  intro hdis
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    obtain ⟨a, _, ha⟩ := hU n
    rw [ha]
    exact (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  obtain ⟨R, hR, hzR⟩ := bounded_point_mem_trapped_interior hf (hUo 0) hz hforward hdis hbounded
  let V : Set ℂ := ball 0 (R + 2)
  let K : Set ℂ := closedBall 0 (R + 1)
  let T : Set ℂ := interior (trappedSet f V)
  let W : ℕ → Set ℂ := fun n => connectedComponentIn T ((f^[n]) z)
  have hfa : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hop : IsOpenMap f := fun S hS => analytic_locally_open hfa (fun x _ => hn x) S (subset_univ _) hS
  have hTF : MapsTo f T T := trapped_interior_forward (fun S _ hS => hop S hS)
  have hzT : z ∈ T := by
    apply interior_mono (s := trappedSet f (ball 0 R)) (t := trappedSet f V) _ hzR
    exact fun x hx n => ball_subset_ball (by linarith : R ≤ R + 2) (hx n)
  have hznT : ∀ n, (f^[n]) z ∈ T := fun n => hTF.iterate n hzT
  have hznW : ∀ n, (f^[n]) z ∈ W n := fun n => mem_connectedComponentIn (hznT n)
  have hWT : ∀ n, W n ⊆ T := fun n => connectedComponentIn_subset _ _
  have hWV : ∀ n, W n ⊆ V := fun n => (hWT n).trans (interior_subset.trans (trappedSet_subset f V))
  have hWo : ∀ n, IsOpen (W n) := fun _ => isOpen_interior.connectedComponentIn
  have hznU : ∀ n, (f^[n]) z ∈ U n := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih => simpa only [iterate_succ_apply'] using hforward n ih
  have hWU : ∀ n, W n ⊆ U n := by
    intro n
    obtain ⟨a, ha, he⟩ := hU n
    have he' : U n = connectedComponentIn (ComplexDynamics.fatouSet f) ((f^[n]) z) :=
      he.trans (connectedComponentIn_eq (he ▸ hznU n))
    rw [he']
    exact connectedComponentIn_mono _ (trapped_interior_subset_fatou hf hn isBounded_ball)
  have hWd : Pairwise (fun n m => Disjoint (W n) (W m)) :=
    fun n m hnm => (hdis hnm).mono (hWU n) (hWU m)
  have hWsc : ∀ n, IsSimplyConnected (W n) := by
    intro n
    dsimp [W, T, V]
    rw [trapped_ball_interior_eq_closed hop (by linarith : R + 2 ≠ 0)]
    apply trapped_closed_disc_component_simplyConnected hf
    rw [← trapped_ball_interior_eq_closed hop (by linarith : R + 2 ≠ 0)]
    exact hznT n
  have hWb : ∀ n x, x ∈ W n → ‖x‖ ≤ R + 2 :=
    fun n x hx => (mem_ball_zero_iff.mp (hWV n hx)).le
  have hznR : ∀ n, ‖(f^[n]) z‖ ≤ R := fun n => (mem_ball_zero_iff.mp (interior_subset hzR n)).le
  have hznK : ∀ n, (f^[n]) z ∈ K := fun n => mem_closedBall_zero_iff.mpr (by linarith [hznR n])
  have hWmap : ∀ n, MapsTo f (W n) (W (n + 1)) := by
    intro n
    change MapsTo f (connectedComponentIn T ((f^[n]) z))
      (connectedComponentIn T ((f^[n + 1]) z))
    rw [iterate_succ_apply']
    exact ((hf.continuous.continuousOn (s := T)).mapsTo_connectedComponentIn
      (hznT n)).mono_right (connectedComponentIn_mono _ hTF.image_subset)
  have hchart : ∀ n, ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (W n) ∧
      BijOn u (W n) (ball 0 1) ∧ u ((f^[n]) z) = 0 := by
    intro n
    apply Complex.exists_bijOn_unitBall_map_eq_zero (hWo n) (hWsc n) _ (hznW n)
    intro he
    exact (isCompact_closedBall (0 : ℂ) (R + 2)).ne_univ
      (univ_subset_iff.mp (by simpa [he] using (hWV n).trans ball_subset_closedBall))
  choose u hu hub hu0 using hchart
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, chartDisc (u n) (W n) r ⊆ K := by
    intro r hr hr1
    exact eventually_atTop.mp (chart_discs_eventually_in_fixed_closedBall
      hWo hu hub hznW hu0 hWb hWd hznR (by linarith : R < R + 1) hr.le hr1)
  have hinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn f (chartDisc (u n) (W n) r) := by
    intro r hr hr1
    exact eventually_atTop.mp (eventually_injOn_shrinking_chart_discs
      (isCompact_closedBall _ _) (hfa.mono (subset_univ K)) (fun x _ => hn x)
      hWo hWsc hu hub hznW hznK hu0 hWb hWd hWmap
      (fun _ => hf.continuous.continuousOn) hr.le hr1)
  have hVc : IsCompact (closure V) := by
    dsimp [V]
    rw [closure_ball (0 : ℂ) (by linarith : R + 2 ≠ 0)]
    exact isCompact_closedBall _ _
  let a : ℂ := ((R + 3 : ℝ) : ℂ)
  let b : ℂ := ((R + 4 : ℝ) : ℂ)
  have ha : a ∉ V := by
    intro hx
    have H := mem_ball_zero_iff.mp hx
    dsimp [a] at H
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at H
    linarith
  have hb : b ∉ V := by
    intro hx
    have H := mem_ball_zero_iff.mp hx
    dsimp [b] at H
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at H
    linarith
  have hab : a ≠ b := by
    intro he
    have H := Complex.ofReal_injective he
    linarith
  apply G.no_wandering_chart_orbit_with_eventual_compact_discs isOpen_ball hVc
    (hfa.mono (subset_univ _)) (fun x _ => hn x) (isCompact_closedBall _ _)
    (closedBall_subset_ball (by linarith : R + 1 < R + 2)) hab
    ha hb
    hznT (fun _ => rfl) (fun n => by simp [iterate_succ_apply']) hWd hu hub hu0 hcompact hinj

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_fatou_orbit_of_bounded_point
