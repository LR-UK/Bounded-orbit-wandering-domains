import FunctionTheory.Conformal.UnivalentBoundaryConvergence
import FunctionTheory.Conformal.CircleCollar
import FunctionTheory.Conformal.KernelSeparation

/-! # Boundary convergence on eventually preserved circle arcs

Injective disk maps converging to the identity on the open disk converge locally
uniformly up to every unit-circle point with an eventually preserved boundary
arc. The symmetric collar is constructed. Thus convergence extends to the
closed disk away from any exceptional set where that boundary condition fails.
-/

open Set Metric Filter
open scoped Topology

namespace FunctionTheory

theorem exists_boundary_neighbourhood_convergence_of_shared_arc
    {F : ℕ → ℂ → ℂ} {a : ℂ} (ha : a ∈ sphere (0 : ℂ) 1)
    (hFc : ∀ n, ContinuousOn (F n) (closedBall (0 : ℂ) 1))
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball (0 : ℂ) 1))
    (hi : ∀ n, InjOn (F n) (ball (0 : ℂ) 1))
    (hmap : ∀ n, MapsTo (F n) (closedBall (0 : ℂ) 1) (closedBall 0 1))
    (hconv : TendstoLocallyUniformlyOn F (fun z => z) atTop (ball 0 1))
    (harc : ∃ ε > 0, ∀ᶠ n in atTop,
      MapsTo (F n) (ball a ε ∩ sphere (0 : ℂ) 1) (sphere 0 1)) :
    ∃ Ω ∈ 𝓝 a, TendstoLocallyUniformlyOn F (fun z => z) atTop
      (Ω ∩ closedBall (0 : ℂ) 1) := by
  obtain ⟨ε, hε, hE⟩ := harc
  obtain ⟨Ω, hΩo, hΩc, haΩ, hsymm, haway, hinner, hΩarc⟩ :=
    exists_symmetric_circle_collar ha (lt_min hε (by norm_num : (0 : ℝ) < 1 / 4))
      (min_le_right ε (1 / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  have hclosed := univalent_boundary_convergence_on_symmetric_collar
    (F := fun n => F (n + N)) hΩo hΩc.isPreconnected
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    haway hsymm hinner (fun n => hFc (n + N)) (fun n => hFd (n + N))
    (fun n => hi (n + N)) (fun n => hmap (n + N))
    (fun n z hz => hN (n + N) (by omega)
      ⟨ball_subset_ball (min_le_left ε (1 / 4)) (hΩarc hz), hz.2⟩)
    (locallyUniformOn_reindex hconv (tendsto_add_atTop_nat N))
  exact ⟨Ω, hΩo.mem_nhds haΩ, locallyUniformOn_of_nat_tail N hclosed⟩

theorem univalent_convergence_on_closedDisk_away_from_exceptional_set
    {F : ℕ → ℂ → ℂ} {B : Set ℂ}
    (hFc : ∀ n, ContinuousOn (F n) (closedBall (0 : ℂ) 1))
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball (0 : ℂ) 1))
    (hi : ∀ n, InjOn (F n) (ball (0 : ℂ) 1))
    (hmap : ∀ n, MapsTo (F n) (closedBall (0 : ℂ) 1) (closedBall 0 1))
    (hconv : TendstoLocallyUniformlyOn F (fun z => z) atTop (ball 0 1))
    (harc : ∀ a ∈ sphere (0 : ℂ) 1 \ B, ∃ ε > 0, ∀ᶠ n in atTop,
      MapsTo (F n) (ball a ε ∩ sphere (0 : ℂ) 1) (sphere 0 1)) :
    TendstoLocallyUniformlyOn F (fun z => z) atTop (closedBall (0 : ℂ) 1 \ B) := by
  intro u hu x hx
  by_cases hxball : x ∈ ball (0 : ℂ) 1
  · obtain ⟨V, hV, hE⟩ := hconv u hu x hxball
    have hVn : V ∈ 𝓝 x := by
      rwa [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hxball)] at hV
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hVn, hE⟩
  · have hxs : x ∈ sphere (0 : ℂ) 1 := by
      have hle : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx.1
      have hge : 1 ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hxball
      simpa only [mem_sphere, dist_zero_right] using le_antisymm hle hge
    obtain ⟨Ω, hΩ, hC⟩ := exists_boundary_neighbourhood_convergence_of_shared_arc
      hxs hFc hFd hi hmap hconv (harc x ⟨hxs, hx.2⟩)
    obtain ⟨V, hV, hE⟩ := hC u hu x ⟨mem_of_mem_nhds hΩ, hx.1⟩
    have hfilter : 𝓝[closedBall (0 : ℂ) 1 \ B] x ≤ 𝓝[Ω ∩ closedBall (0 : ℂ) 1] x := by
      rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hΩ)]
      exact nhdsWithin_mono _ sdiff_subset
    exact ⟨V, hfilter hV, hE⟩

end FunctionTheory
