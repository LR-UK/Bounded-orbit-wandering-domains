module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LogRatioBound
public import BoundedWanderingDomains.DensityDeficit

@[expose] public section

/-! # A fixed chart cutoff through finitely many removed points

The cutoff is supported in a fixed chart region. Finite points omitted from
the old domain are excluded from the integrand, rather than from the cutoff.
This is the form needed for estimates uniform over finite puncture models. -/

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem chart_gain_cutoff_finite_exceptions
    {U : TopologicalSpace.Opens M} (p : DiscCover U)
    {W : TopologicalSpace.Opens U} (q : DiscCover W) (hW : Nonempty W)
    {c : OpenPartialHomeomorph U ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (F : Finset ℂ) {V : Set ℂ} (hV : IsOpen V)
    (hVtarget : ∀ z ∈ V, z ∉ F → z ∈ (c.subtypeRestr hW).target)
    {chi : ℂ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hchi : ContDiff ℝ 2 chi) (hcomp : HasCompactSupport chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hsupp : tsupport chi ⊆ V)
    (hbound : ∀ z ∈ V, z ∉ F → p.chartLogRatio q hW c z ≤ B) :
    (∫⁻ z, ENNReal.ofReal (chi z *
      (if z ∈ F then 0 else
        (q.chartDensity (c.subtypeRestr hW) z)^2 - (p.chartDensity c z)^2))) ≤
      ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  have hd := mdifferentiableOn_subtypeRestr hW hc
  have hmain := AreaDeficit.density_deficit_cutoff F hV hB hchi hcomp hchi0 hsupp
    (a := q.chartDensity (c.subtypeRestr hW)) (b := p.chartDensity c)
    (fun z hz hf => ⟨q.chartDensity_pos hd (hVtarget z hz hf),
      q.chartDensity_contDiffAt hd (hVtarget z hz hf)⟩)
    (fun z hz hf => ⟨p.chartDensity_pos hc
        (c.subtypeRestr_target_subset hW (hVtarget z hz hf)),
      p.chartDensity_contDiffAt hc
        (c.subtypeRestr_target_subset hW (hVtarget z hz hf))⟩)
    (fun z hz hf => q.chartDensity_curvature hd (hVtarget z hz hf))
    (fun z hz hf => p.chartDensity_curvature hc
      (c.subtypeRestr_target_subset hW (hVtarget z hz hf)))
    (fun z hz hf => max_le (hbound z hz hf) hB)
  convert hmain using 1
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ tsupport chi
  · by_cases hf : z ∈ F
    · simp [hf]
    · have hnonneg : 0 ≤ (q.chartDensity (c.subtypeRestr hW) z)^2 -
          (p.chartDensity c z)^2 := by
        rw [← p.chartLogRatio_laplacian q hW hc (hVtarget z (hsupp hz) hf)]
        exact p.chartLogRatio_laplacian_nonneg q hW hc (hVtarget z (hsupp hz) hf)
      simp only [hf,ite_false,max_eq_left hnonneg]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end AreaDeficit.Surfaces.DiscCover
