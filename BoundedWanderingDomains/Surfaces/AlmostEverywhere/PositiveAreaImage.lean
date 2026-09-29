module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.PositiveAreaBridge
public import Mathlib.MeasureTheory.Measure.Regular
public import BoundedWanderingDomains.Surfaces.ChartCriticalValues
public import BoundedWanderingDomains.Surfaces.SaturationDynamics
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.OrbitShift

@[expose] public section

/-! # Positive chart area under injective holomorphic maps -/

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Topology Manifold ENNReal

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem HasPositiveChartArea.exists_positive_piece {ι : Type*} [Countable ι]
    {A : Set X} (hpos : HasPositiveChartArea A) (B : ι → Set X)
    (hcover : A ⊆ ⋃ i, B i) : ∃ i, HasPositiveChartArea (A ∩ B i) := by
  by_contra hn
  push Not at hn
  obtain ⟨p, hp⟩ := hpos
  have hnull : ∀ i, volume ((chartAt ℂ p) '' ((A ∩ B i) ∩ (chartAt ℂ p).source)) = 0 := by
    intro i
    exact le_antisymm (not_lt.mp (fun h => hn i ⟨p, h⟩)) bot_le
  have hsubset : A ∩ (chartAt ℂ p).source ⊆ ⋃ i, (A ∩ B i) ∩ (chartAt ℂ p).source := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.1)
    exact mem_iUnion.mpr ⟨i, ⟨hx.1, hi⟩, hx.2⟩
  have hzero := measure_mono_null (image_mono (f := chartAt ℂ p) hsubset) (by
    rw [image_iUnion]
    exact measure_iUnion_null hnull)
  exact (ne_of_gt hp) hzero

variable [MeasurableSpace X] [BorelSpace X]

theorem HasPositiveChartArea.exists_compact_chart_patch {A : Set X}
    (hpos : HasPositiveChartArea A) (hA : MeasurableSet A) :
    ∃ (p : X) (K : Set X), IsCompact K ∧ K ⊆ A ∩ (chartAt ℂ p).source ∧
      0 < volume ((chartAt ℂ p) '' K) := by
  obtain ⟨p, hp⟩ := hpos
  let c := chartAt ℂ p
  have hB : MeasurableSet (c '' (A ∩ c.source)) :=
    chart_image_measurable c p (hA.inter c.open_source.measurableSet) inter_subset_right
  obtain ⟨L, hLB, hLc, hLp⟩ := hB.exists_lt_isCompact hp
  have hLt : L ⊆ c.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hLB hz
    exact c.map_source hx.2
  let K := c.symm '' L
  have hKA : K ⊆ A ∩ c.source := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hLB hz
    rwa [c.left_inv hy.2]
  have he : c '' K = L := by
    rw [image_image]
    calc
      _ = id '' L := image_congr (fun z hz => c.right_inv (hLt hz))
      _ = L := image_id L
  refine ⟨p, K, hLc.image_of_continuousOn (c.continuousOn_symm.mono hLt), hKA, ?_⟩
  rw [he]
  exact hLp

end SurfaceDynamics

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Topology Manifold ENNReal

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]

theorem positive_chart_area_image_of_compact
    {c : OpenPartialHomeomorph M ℂ} {d : OpenPartialHomeomorph N ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source)
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hopen : IsOpenMap f)
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ c.source)
    (hfd : f '' K ⊆ d.source) (hinj : InjOn f K)
    (hpos : 0 < volume (c '' K)) : 0 < volume (d '' (f '' K)) := by
  let g := d ∘ f ∘ c.symm
  let T := c '' K
  have hTc : IsCompact T := hK.image_of_continuousOn (c.continuousOn.mono hKc)
  have hTm : MeasurableSet T := hTc.measurableSet
  have hgan : AnalyticOnNhd ℂ g T := by
    rintro z ⟨x, hx, rfl⟩
    exact analyticAt_writtenInCharts hc hd hf (hKc hx) (hfd ⟨x, hx, rfl⟩)
  have hder : ∀ z ∈ T, HasDerivAt g (deriv g z) z := by
    rintro z ⟨x, hx, rfl⟩
    exact DiscCover.hasDerivAt_writtenInCharts hc hd hf (hKc hx) (hfd ⟨x, hx, rfl⟩)
  have hginj : InjOn g T := by
    rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩ he
    have he' : f x = f y := d.injOn (hfd ⟨x, hx, rfl⟩) (hfd ⟨y, hy, rfl⟩) (by
      simpa only [g, comp_apply, c.left_inv (hKc hx), c.left_inv (hKc hy)] using he)
    exact congrArg c (hinj hx hy he')
  have himage : g '' T = d '' (f '' K) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hKc hx)]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨c x, ⟨x, hx, rfl⟩, by simp [g, c.left_inv (hKc hx)]⟩
  have hcrit : (T ∩ {z | deriv g z = 0}).Finite := by
    apply ((finite_chart_critical_points hc hd hf hopen hK hKc hfd).image c).subset
    rintro z ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, ⟨hx, hz⟩, rfl⟩
  by_contra hn
  have hzero : volume (d '' (f '' K)) = 0 := le_antisymm (not_lt.mp hn) bot_le
  have hjac := AreaDeficit.holomorphic_change_of_variables hTm hder hginj (fun _ => 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, himage] at hjac
  have hwc : ContinuousOn (fun z => ENNReal.ofReal (‖deriv g z‖ ^ 2)) T := by
    intro z hz
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (((hgan z hz).deriv.continuousAt.norm).pow 2)).continuousWithinAt
  have hae := (setLIntegral_eq_zero_iff' hTm (hwc.aemeasurable hTm)).mp (hjac ▸ hzero)
  have hcritnull : volume (T ∩ {z | deriv g z = 0}) = 0 := hcrit.measure_zero volume
  have hnotcrit : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ T ∩ {z | deriv g z = 0} := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hcritnull
  have hnotT : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ T := by
    filter_upwards [hae, hnotcrit] with z hz hnz hzT
    apply hnz
    refine ⟨hzT, ?_⟩
    have hsq : ‖deriv g z‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp (hz hzT)
    have hnorm : ‖deriv g z‖ = 0 := by nlinarith [norm_nonneg (deriv g z)]
    exact norm_eq_zero.mp hnorm
  have hTzero : volume T = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnotT
  exact (ne_of_gt hpos) hTzero

end SurfaceDynamics

open Set Function Filter MeasureTheory
open AreaDeficit.Surfaces
open scoped Topology Manifold ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
theorem positive_chart_area_totalize_image (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAs : A ⊆ f.source)
    (hinj : InjOn f.totalize A) (hpos : HasPositiveChartArea A) :
    HasPositiveChartArea (f.totalize '' A) := by
  classical
  obtain ⟨s, hsc, hcover⟩ := countable_cover_nhds (fun x : X => chart_source_mem_nhds ℂ x)
  let : Countable s := hsc.to_subtype
  let B : s → Set X := fun q => f.totalize ⁻¹' (chartAt ℂ (q : X)).source
  have hcoverA : A ⊆ ⋃ q, B q := by
    intro x hx
    have hh : f.totalize x ∈ ⋃ q ∈ s, (chartAt ℂ q).source := hcover ▸ mem_univ _
    obtain ⟨q, hq⟩ := mem_iUnion.mp hh
    obtain ⟨hqs, hq⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨q, hqs⟩, hq⟩
  obtain ⟨q, hqpos⟩ := hpos.exists_positive_piece B hcoverA
  have hABm : MeasurableSet (A ∩ B q) :=
    hA.inter ((chartAt ℂ (q : X)).open_source.measurableSet.preimage
      (f.measurable_totalize hf.2.continuous))
  obtain ⟨p, K, hK, hKAB, hKpos⟩ := hqpos.exists_compact_chart_patch hABm
  let c := chartAt ℂ p
  let d := chartAt ℂ (q : X)
  have hKA : K ⊆ A := fun x hx => (hKAB hx).1.1
  have hKs : K ⊆ f.source := hKA.trans hAs
  obtain ⟨a, ha⟩ := hpos.nonempty
  let hSN : Nonempty f.source := ⟨⟨a, hAs ha⟩⟩
  let cs := c.subtypeRestr hSN
  let KS : Set f.source := Subtype.val ⁻¹' K
  have hvalK : Subtype.val '' KS = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hKs hx⟩, hx, rfl⟩
  have hKSc : IsCompact KS := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, hvalK]
    exact hK
  have hKScs : KS ⊆ cs.source := by
    intro x hx
    simpa [cs] using (hKAB hx).2
  have hcs : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cs cs.source := by
    apply mdifferentiableOn_subtypeRestr hSN
    intro x hx
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) hx).mdifferentiableWithinAt
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source := by
    intro x hx
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) hx).mdifferentiableWithinAt
  have himage : cs '' KS = c '' K := by
    change (c ∘ Subtype.val) '' KS = c '' K
    rw [image_comp, hvalK]
  have hfd : f.map '' KS ⊆ d.source := by
    rintro y ⟨x, hx, rfl⟩
    rw [← f.totalize_eq x.property]
    exact (hKAB hx).1.2
  have hfinj : InjOn f.map KS := by
    intro x hx y hy he
    exact Subtype.ext (hinj (hKA hx) (hKA hy) (by
      rwa [f.totalize_eq x.property, f.totalize_eq y.property]))
  have hpimage := positive_chart_area_image_of_compact hcs hd hf.2 hf.1
    hKSc hKScs hfd hfinj (by rw [himage]; exact hKpos)
  refine ⟨q, lt_of_lt_of_le hpimage (measure_mono (image_mono ?_))⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨⟨x, hKA hx, f.totalize_eq x.property⟩, hfd ⟨x, hx, rfl⟩⟩

theorem positive_chart_area_imageAt (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAtr : A ⊆ f.trapped)
    (hinj : f.InjectiveOnSaturation A) (hpos : HasPositiveChartArea A) (n : ℕ) :
    HasPositiveChartArea (f.imageAt n A) := by
  induction n with
  | zero => simpa using hpos
  | succ n ih =>
      rw [← f.totalize_image_imageAt hAtr n]
      exact f.positive_chart_area_totalize_image hf (f.measurableSet_imageAt hf.2.continuous hAtr hinj hA n)
        (f.imageAt_subset_source hAtr n)
        ((f.totalize_injOn_saturation hAtr hinj).mono (fun x hx => mem_iUnion.mpr ⟨n, hx⟩)) ih

end SurfaceDynamics.LocalMap
