/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ExtremalDisc
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces

def discDilation (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : unitDisc → unitDisc :=
  fun z => ⟨(r : ℂ) * z, by
    change (r : ℂ) * (z : ℂ) ∈ ball 0 1
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hr1)
      (mem_ball_zero_iff.mp z.2)⟩

@[simp] theorem discDilation_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    discDilation r hr hr1 discZero = discZero := by
  apply Subtype.ext
  simp [discDilation,discZero]

theorem discDilation_holomorphic {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (discDilation r hr hr1) := by
  apply (mdifferentiable_subtypeVal_comp_iff unitDisc _).mp
  intro z
  change MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : unitDisc => (r : ℂ) * (z : ℂ)) z
  apply mdifferentiableAt_subtype_iff.mpr
  exact ((differentiableAt_const (r : ℂ)).mul differentiableAt_id).mdifferentiableAt

theorem discDilation_deriv {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    deriv (planeExtension (fun z => (discDilation r hr hr1 z : ℂ))) 0 = (r : ℂ) := by
  have he : planeExtension (fun z => (discDilation r hr hr1 z : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (r : ℂ) * z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    exact planeExtension_coe _ ⟨z,hz⟩
  rw [he.deriv_eq]
  simp
end AreaDeficit.Surfaces
