import FunctionTheory.Conformal.ReflectionConvergence
import FunctionTheory.Conformal.UnivalentAnnulus
import Mathlib.Topology.Perfect

/-! # Convergence up to a shared circular boundary arc

For injective disk maps converging locally uniformly to the identity, Rouché
supplies an eventual lower bound on an outer annulus. Circle reflection and
Vitali then give convergence on the closed inner side of a symmetric collar
where the maps preserve the unit circle. No lower bound is assumed separately.
-/

open Set Metric Filter EuclideanGeometry
open scoped Topology

namespace FunctionTheory

theorem locallyUniformOn_of_nat_tail
    {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {g : X → Y} {S : Set X} (N : ℕ)
    (h : TendstoLocallyUniformlyOn (fun n => F (n + N)) g atTop S) :
    TendstoLocallyUniformlyOn F g atTop S := by
  intro u hu x hx
  obtain ⟨V, hV, hE⟩ := h u hu x hx
  refine ⟨V, hV, ?_⟩
  have hmap : ∀ᶠ n in map (fun n : ℕ => n + N) atTop,
      ∀ y ∈ V, (g y, F n y) ∈ u := hE
  simpa only [map_add_atTop_eq_nat] using hmap

theorem univalent_boundary_convergence_on_symmetric_collar
    {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hr : 0 < r) (hr1 : r < 1) (haway : ∀ z ∈ Ω, r ≤ ‖z‖)
    (hsymm : MapsTo (inversion (0 : ℂ) 1) Ω Ω)
    (hinner : (Ω ∩ ball (0 : ℂ) 1).Nonempty)
    (hFc : ∀ n, ContinuousOn (F n) (closedBall (0 : ℂ) 1))
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball (0 : ℂ) 1))
    (hi : ∀ n, InjOn (F n) (ball (0 : ℂ) 1))
    (hmap : ∀ n, MapsTo (F n) (closedBall (0 : ℂ) 1) (closedBall 0 1))
    (hboundary : ∀ n, MapsTo (F n) (Ω ∩ sphere (0 : ℂ) 1) (sphere 0 1))
    (hconv : TendstoLocallyUniformlyOn F (fun z => z) atTop (ball 0 1)) :
    TendstoLocallyUniformlyOn F (fun z => z) atTop (Ω ∩ closedBall (0 : ℂ) 1) := by
  have hhalf : 0 < r / 2 := half_pos hr
  obtain ⟨N, hN⟩ := (eventually_atTop.mp
    (eventually_norm_ge_on_outer_annulus hr hr1 hhalf hFd hi hconv))
  obtain ⟨z₀, hz₀⟩ := hinner
  have hacc : AccPt z₀ (𝓟 (Ω ∩ ball (0 : ℂ) 1)) :=
    (hΩ.inter isOpen_ball).preperfect z₀ hz₀
  have hR := reflected_maps_tendsto_of_inner_convergence
    (F := fun n => F (n + N)) hΩ hconn hhalf hsymm
    (fun n => (hFc (n + N)).mono inter_subset_right)
    (fun n => (hFd (n + N)).mono inter_subset_right)
    (fun n => hboundary (n + N))
    (fun n z hz => by
      simpa only [mem_closedBall, dist_zero_right] using hmap (n + N) hz.2)
    (fun n z hz _ => by
      have h := hN (n + N) (by omega) z hz.2 (haway z hz.1)
      linarith)
    (Subset.refl _) hz₀.1 hacc
    (fun z hz => (hconv.tendsto_at hz.2).comp (tendsto_add_atTop_nat N))
  exact locallyUniformOn_of_nat_tail N
    (locallyUniformOn_closedSide_of_reflected_convergence hR)

end FunctionTheory
