/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DiscDilation
import BoundedWanderingDomains.Surfaces.DensityRatioInvariance
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- A uniform disc avoidance radius controls the increase of the hyperbolic density. -/
theorem densityRatio_le_of_disc_avoidance (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (q : DiscCover U) {x : U}
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (havoid : ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      g discZero = (x : M) → ∀ z : unitDisc, ‖(z : ℂ)‖ < r → g z ∈ U) :
    p.densityRatio q x ≤ 1 / r := by
  let c := chartAt ℂ (x : M)
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source := fun z hz =>
    (mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hz).mdifferentiableWithinAt
  have hx : (x : M) ∈ c.source := mem_chart_source ℂ (x : M)
  obtain ⟨g,hg,hg0,hge⟩ := p.density_extremal_disc hc hx
  let a := discDilation r hr.le hr1
  have ha := discDilation_holomorphic hr.le hr1
  have ha0 : a discZero = discZero := discDilation_zero hr.le hr1
  have hga : ∀ z : unitDisc, g (a z) ∈ U := by
    intro z
    apply havoid g hg hg0
    change ‖(r : ℂ) * (z : ℂ)‖ < r
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp z.2) hr).trans_eq (mul_one r)
  let gU : unitDisc → U := fun z => ⟨g (a z),hga z⟩
  have hgU : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) gU :=
    (mdifferentiable_subtypeVal_comp_iff U gU).mp (hg.comp ha)
  have hgU0 : gU discZero = x := Subtype.ext (by change g (a discZero) = x; rw [ha0,hg0])
  let d := c.subtypeRestr (show Nonempty U from ⟨x⟩)
  have hd := mdifferentiableOn_subtypeRestr (show Nonempty U from ⟨x⟩) hc
  have hxd : x ∈ d.source := by
    simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage] using hx
  have hs := q.density_schwarz_disc hgU hd discZero (hgU0.symm ▸ hxd)
  have hcg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (c ∘ g) discZero :=
    ((hc _ (hg0.symm ▸ hx)).mdifferentiableAt (c.open_source.mem_nhds (hg0.symm ▸ hx))).comp
      discZero (hg discZero)
  have hder := planeExtension_deriv_comp (g := c ∘ g) (h := a) (w := discZero)
    (ha0.symm ▸ hcg) (ha discZero)
  rw [ha0] at hder
  have he : d ∘ gU = (c ∘ g) ∘ a := rfl
  rw [he,hder,hgU0,norm_mul] at hs
  have har : deriv (planeExtension (fun z => (a z : ℂ))) (discZero : ℂ) = (r : ℂ) :=
    discDilation_deriv hr.le hr1
  rw [har,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hs
  have hs' : q.density d x * (‖deriv (planeExtension (c ∘ g)) (0 : ℂ)‖ * r) ≤ 2 := by
    simpa [discZero,discDensity,discDenom] using hs
  rw [p.densityRatio_eq q ⟨x⟩ hc hx]
  apply (div_le_div_iff₀ (p.density_pos hc hx) hr).mpr
  change q.density d x * r ≤ 1 * p.density c x
  have hn : 0 < ‖deriv (planeExtension (c ∘ g)) (0 : ℂ)‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro he
    rw [← he,mul_zero] at hge
    norm_num at hge
  nlinarith [hge]
end AreaDeficit.Surfaces.DiscCover
