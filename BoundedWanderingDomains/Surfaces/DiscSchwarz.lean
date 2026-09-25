/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.Surfaces.PlaneReading
import BoundedWanderingDomains.DiscCoveringMetric

/-! # Schwarz–Pick for holomorphic maps of the supplied disc model -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

/-- Schwarz–Pick at an arbitrary point, with curvature −1 normalisation. -/
theorem disc_schwarz_at {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hm : MapsTo g (ball 0 1) (ball 0 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    discDensity (g w) * ‖deriv g w‖ ≤ discDensity w := by
  obtain ⟨m,hmd,hmm,hm0,hscale⟩ := exists_disc_recentring hw
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hs := disc_schwarz_centre (by norm_num : (0 : ℝ) < 1)
    (hg.comp hmd hmm) (hm.comp hmm)
  have hd := deriv_comp (0 : ℂ)
    (hg.differentiableAt (isOpen_ball.mem_nhds (hmm h0)))
    (hmd.differentiableAt (isOpen_ball.mem_nhds h0))
  rw [hd, norm_mul, comp_apply, hm0, div_one] at hs
  have hpos : 0 < ‖deriv m 0‖ := by
    have hnonneg := norm_nonneg (deriv m 0)
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) hnonneg
    rw [hz, mul_zero] at hscale
    norm_num at hscale
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    (discDensity (g w) * ‖deriv g w‖) * ‖deriv m 0‖ ≤ 2 := by
      simpa only [mul_assoc] using hs
    _ = discDensity w * ‖deriv m 0‖ := hscale.symm

/-- Schwarz–Pick for a map of open submanifolds; the derivative is read in
its ordinary complex coordinate. -/
theorem unitDisc_schwarz {h : unitDisc → unitDisc}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (w : unitDisc) :
    discDensity (h w) * ‖deriv (planeExtension (fun z => (h z : ℂ))) w‖ ≤
      discDensity w := by
  have hd := planeExtension_differentiableOn ((mdifferentiable_subtype_val unitDisc).comp hh)
  have hm : MapsTo (planeExtension (fun z => (h z : ℂ))) (ball 0 1) (ball 0 1) := by
    intro z hz
    change planeExtension (fun z => (h z : ℂ)) (⟨z,hz⟩ : unitDisc) ∈ ball 0 1
    rw [planeExtension_coe]
    exact (h ⟨z,hz⟩).2
  simpa only [planeExtension_coe, Function.comp_def] using disc_schwarz_at hd hm w.2

end AreaDeficit.Surfaces
