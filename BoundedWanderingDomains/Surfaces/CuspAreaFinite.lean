module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CuspDensityBounds
public import BoundedWanderingDomains.Surfaces.FinitePunctureAreaBridge
public import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite

@[expose] public section

/-! # Finite intrinsic area near an isolated surface puncture -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

omit [T2Space M] in
/-- The inverse image of a small punctured coordinate disc has finite
intrinsic hyperbolic area. -/
theorem hyperbolicArea_cusp_chart_finite (p : DiscCover M)
    {d : OpenPartialHomeomorph M ℂ}
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ball a R \ {a} ⊆ d.target) :
    p.hyperbolicArea
      (d.symm '' (ball a (R / 2) \ {a})) < ⊤ := by
  let B : Set ℂ := ball a (R / 2) \ {a}
  have hBmeas : MeasurableSet B :=
    measurableSet_ball.diff (measurableSet_singleton a)
  have hBtarget : B ⊆ d.target := by
    intro z hz
    apply hball
    refine ⟨?_, hz.2⟩
    have hzR2 : dist z a < R / 2 := hz.1
    have : R / 2 < R := by linarith
    exact hzR2.trans this
  have hAmeas : MeasurableSet (d.symm '' B) :=
    AreaDeficit.Surfaces.chart_inverse_image_measurable d hBmeas hBtarget
  have hAsource : d.symm '' B ⊆ d.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.map_target (hBtarget hz)
  rw [p.hyperbolicArea_apply_chart hd hAmeas hAsource]
  unfold coordinateArea
  have himage : d '' (d.symm '' B) = B := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [d.right_inv (hBtarget hw)] using hw
    · intro hz
      exact ⟨d.symm z, ⟨z, hz, rfl⟩, d.right_inv (hBtarget hz)⟩
  rw [himage]
  exact p.lintegral_chartDensity_sq_cusp_lt_top hd hR hball

/-- A compact core together with finitely many finite-area cusp patches has
finite total area.  This isolates the final set-theoretic assembly needed for
a compact surface with finitely many punctures. -/
theorem hyperbolicArea_univ_lt_top_of_finite_cusp_cover
    {ι : Type*} (p : DiscCover M) (I : Finset ι)
    (L : Set M) (A : ι → Set M)
    (hL : IsCompact L)
    (hA : ∀ i ∈ I, p.hyperbolicArea (A i) < ⊤)
    (hcover : (Set.univ : Set M) ⊆ L ∪ ⋃ i ∈ I, A i) :
    p.hyperbolicArea Set.univ < ⊤ := by
  apply lt_of_le_of_lt (measure_mono hcover)
  apply lt_of_le_of_lt (measure_union_le _ _)
  apply lt_of_le_of_lt (add_le_add le_rfl
    (measure_biUnion_finset_le I A))
  exact ENNReal.add_lt_top.mpr
    ⟨p.hyperbolicArea_compact_finite hL,
      ENNReal.sum_lt_top.mpr (fun i hi => hA i hi)⟩

end AreaDeficit.Surfaces.DiscCover
