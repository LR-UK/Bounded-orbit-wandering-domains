module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.KernelNonconstant
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

/-! # Normal limits of normalised lifts stay in the entire ambient disc

The maximum modulus principle upgrades the earlier small-disc bound. This
allows the kernel argument to use a full extremal disc without losing a
factor in the final Schwarz–Pick comparison.
-/

open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces

theorem normal_lift_limit_maps_disc
    (h : ℕ → unitDisc → unitDisc)
    (w : unitDisc) {φ : ℕ → ℕ} {g : ℂ → ℂ}
    (hl : TendstoLocallyUniformlyOn
      (fun n => planeExtension (fun v => (h (φ n) v : ℂ))) g atTop (ball 0 1))
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = (w : ℂ)) :
    MapsTo g (ball 0 1) (ball 0 1) := by
  have hb : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ 1 := by
    intro z hz
    apply le_of_tendsto (hl.tendsto_at hz).norm
    exact Eventually.of_forall (fun n => by
      rw [show planeExtension (fun v => (h (φ n) v : ℂ)) z =
        (h (φ n) ⟨z,hz⟩ : ℂ) from planeExtension_coe _ ⟨z,hz⟩]
      exact (mem_ball_zero_iff.mp (h (φ n) ⟨z,hz⟩).property).le)
  intro z hz
  apply mem_ball_zero_iff.mpr
  by_contra hn
  have he : ‖g z‖ = 1 := le_antisymm (hb z hz) (le_of_not_gt hn)
  have hm : IsMaxOn (norm ∘ g) (ball 0 1) z := by
    intro y hy
    change ‖g y‖ ≤ ‖g z‖
    rw [he]
    exact hb y hy
  have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hgd hz hm
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have hnorm : ‖(w : ℂ)‖ = 1 := by
    simpa only [comp_apply, const_apply, hg0, he] using hconst hzero
  exact (ne_of_lt (mem_ball_zero_iff.mp w.property)) hnorm

end AreaDeficit.Surfaces
