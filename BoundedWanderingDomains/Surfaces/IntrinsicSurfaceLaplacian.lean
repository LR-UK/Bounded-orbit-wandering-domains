/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateLaplacian
import BoundedWanderingDomains.Surfaces.DensityCoordinateChange
import BoundedWanderingDomains.Surfaces.ChartLaplacianSupport
import BoundedWanderingDomains.Surfaces.SmoothSurface

/-! # The intrinsic Laplacian relative to a disc-cover metric -/

open Set Function InnerProductSpace Laplacian
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The Euclidean coordinate Laplacian divided by the square of the
hyperbolic density. The two factors have the same conformal transformation
law, so their quotient is an intrinsic scalar. -/
noncomputable def intrinsicLaplacian (p : DiscCover M)
    (u : M → ℝ) (x : M) : ℝ :=
  AreaDeficit.Surfaces.chartLaplacian u x /
    (p.density (chartAt ℂ x) x) ^ 2

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
/-- The intrinsic Laplacian can be computed in any holomorphic chart. -/
theorem intrinsicLaplacian_eq_in_chart (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {u : M → ℝ} {x : M} (hxc : x ∈ c.source)
    (hu : ContDiffAt ℝ 2 (u ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x x)) :
    p.intrinsicLaplacian u x =
      Δ (u ∘ c.symm) (c x) / (p.density c x) ^ 2 := by
  let d := chartAt ℂ x
  have hxd : x ∈ d.source := mem_chart_source ℂ x
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source :=
    (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hlap := AreaDeficit.Surfaces.laplacian_coordinate_change
    hc hd hxc hxd hu
  have hdensity := p.density_coordinate_change hc hd hxc hxd
  have hdp : 0 < p.density d x := p.density_pos hd hxd
  have hnorm : 0 < ‖deriv (d ∘ c.symm) (c x)‖ := by
    have hcp : 0 < p.density c x := p.density_pos hc hxc
    have hn : ‖deriv (d ∘ c.symm) (c x)‖ ≠ 0 := by
      intro hn
      rw [hn, mul_zero] at hdensity
      linarith
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
  change Δ (u ∘ d.symm) (d x) / (p.density d x) ^ 2 = _
  rw [hlap]
  have hs : (p.density c x) ^ 2 =
      (p.density d x) ^ 2 * ‖deriv (d ∘ c.symm) (c x)‖ ^ 2 := by
    rw [← hdensity]
    ring
  rw [hs]
  field_simp

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_eq_in_chart_of_contMDiff (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u)
    {x : M} (hxc : x ∈ c.source) :
    p.intrinsicLaplacian u x =
      Δ (u ∘ c.symm) (c x) / (p.density c x) ^ 2 := by
  apply p.intrinsicLaplacian_eq_in_chart hc hxc
  rw [← contMDiffAt_iff_contDiffAt]
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
    AreaDeficit.Surfaces.isManifold_real_of_complex
  exact hu.contMDiffAt.comp _
    (contMDiffAt_symm_of_mem_maximalAtlas
      ((contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas x)
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
/-- For a `C²` scalar function, the intrinsic Laplacian is continuous. -/
theorem intrinsicLaplacian_continuous (p : DiscCover M)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u) :
    Continuous (p.intrinsicLaplacian u) := by
  rw [continuous_iff_continuousAt]
  intro x
  let c := chartAt ℂ x
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  let g : ℂ → ℝ := u ∘ c.symm
  have hg : ContDiffAt ℝ 2 g (c x) := by
    rw [← contMDiffAt_iff_contDiffAt]
    let : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
      AreaDeficit.Surfaces.isManifold_real_of_complex
    exact hu.contMDiffAt.comp _
      (contMDiffAt_symm_of_mem_maximalAtlas
        ((contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas x)
        (c.map_source hxc))
  have hchart : ContinuousAt c x := c.continuousAt hxc
  have hlap : ContinuousAt (fun y => Δ g (c y)) x :=
    (AreaDeficit.laplacian_continuousAt hg).comp hchart
  have hdens : ContinuousAt (fun y => p.chartDensity c (c y)) x :=
    (p.chartDensity_contDiffAt hc (c.map_source hxc)).continuousAt.comp hchart
  have hdenne : p.chartDensity c (c x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (p.chartDensity_pos hc (c.map_source hxc)))
  have hq : ContinuousAt
      (fun y => Δ g (c y) / (p.chartDensity c (c y)) ^ 2) x :=
    hlap.div (hdens.pow 2) hdenne
  apply hq.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hxc] with y hy
  have huy : ContDiffAt ℝ 2 (u ∘ (chartAt ℂ y).symm)
      (chartAt ℂ y y) := by
    rw [← contMDiffAt_iff_contDiffAt]
    let : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
      AreaDeficit.Surfaces.isManifold_real_of_complex
    exact hu.contMDiffAt.comp _
      (contMDiffAt_symm_of_mem_maximalAtlas
        ((contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas y)
        ((chartAt ℂ y).map_source (mem_chart_source ℂ y)))
  rw [p.intrinsicLaplacian_eq_in_chart hc hy huy]
  dsimp only [g, chartDensity, Function.comp_apply]
  rw [c.left_inv hy]

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_eq_zero_of_notMem_tsupport
    (p : DiscCover M) {u : M → ℝ} {x : M} (hx : x ∉ tsupport u) :
    p.intrinsicLaplacian u x = 0 := by
  unfold intrinsicLaplacian
  rw [AreaDeficit.Surfaces.chartLaplacian_eq_zero_of_locally_const
    (notMem_tsupport_iff_eventuallyEq.mp hx)]
  exact zero_div _

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem tsupport_intrinsicLaplacian_subset (p : DiscCover M)
    (u : M → ℝ) : tsupport (p.intrinsicLaplacian u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hxu
  exact hx (p.intrinsicLaplacian_eq_zero_of_notMem_tsupport hxu)

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
private theorem contDiffAt_comp_preferredChart_symm
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u) (x : M) :
    ContDiffAt ℝ 2 (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  rw [← contMDiffAt_iff_contDiffAt]
  let : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
    AreaDeficit.Surfaces.isManifold_real_of_complex
  exact hu.contMDiffAt.comp _
    (contMDiffAt_symm_of_mem_maximalAtlas
      ((contDiffGroupoid 2 𝓘(ℝ, ℂ)).chart_mem_maximalAtlas x)
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_add (p : DiscCover M)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v) (x : M) :
    p.intrinsicLaplacian (u + v) x =
      p.intrinsicLaplacian u x + p.intrinsicLaplacian v x := by
  unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
  have h := (contDiffAt_comp_preferredChart_symm hu x).laplacian_add
    (contDiffAt_comp_preferredChart_symm hv x)
  change Δ ((u ∘ (chartAt ℂ x).symm) +
      (v ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) /
        (p.density (chartAt ℂ x) x) ^ 2 = _
  rw [h]
  ring

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_const (p : DiscCover M) (a : ℝ) (x : M) :
    p.intrinsicLaplacian (fun _ => a) x = 0 := by
  unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
  change Δ (fun _ : ℂ => a) (chartAt ℂ x x) / _ = 0
  simp

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_neg (p : DiscCover M)
    {u : M → ℝ} (_hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u) (x : M) :
    p.intrinsicLaplacian (-u) x = -p.intrinsicLaplacian u x := by
  unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
  change Δ (-(u ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) / _ =
    -(Δ (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) / _)
  rw [laplacian_neg]
  exact neg_div _ _

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_sub (p : DiscCover M)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 v) (x : M) :
    p.intrinsicLaplacian (u - v) x =
      p.intrinsicLaplacian u x - p.intrinsicLaplacian v x := by
  unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
  have h := (contDiffAt_comp_preferredChart_symm hu x).laplacian_sub
    (contDiffAt_comp_preferredChart_symm hv x)
  change Δ ((u ∘ (chartAt ℂ x).symm) -
      (v ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) / _ = _
  rw [h]
  ring

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem intrinsicLaplacian_finsetSum (p : DiscCover M)
    {ι : Type*} (s : Finset ι) (u : ι → M → ℝ)
    (hu : ∀ i ∈ s, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (u i)) (x : M) :
    p.intrinsicLaplacian (fun y => ∑ i ∈ s, u i y) x =
      ∑ i ∈ s, p.intrinsicLaplacian (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold intrinsicLaplacian AreaDeficit.Surfaces.chartLaplacian
      change Δ (fun _ : ℂ => (0 : ℝ)) (chartAt ℂ x x) / _ = 0
      simp
  | @insert i s hi ih =>
      have hui := hu i (Finset.mem_insert_self i s)
      have hus : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2
          (fun y => ∑ j ∈ s, u j y) :=
        ContMDiff.sum fun j hj => hu j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      change p.intrinsicLaplacian
          (u i + fun y => ∑ j ∈ s, u j y) x = _
      rw [p.intrinsicLaplacian_add hui hus x,
        ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

end AreaDeficit.Surfaces.DiscCover
