module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.CompactSource
public import BoundedWanderingDomains.Surfaces.CompactClusterSeparation
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.CompactAreaRestriction
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.PositiveAreaImage

@[expose] public section

/-! # Almost-everywhere escape or derived-singular accumulation -/

open Set Function Filter OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X]

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]

theorem LocalMap.exists_compact_tail_away_from_derived_of_no_subsequence
    (f : LocalMap X) {x : X} (hx : x ∈ f.trapped)
    (hno : ¬ f.HasEscapingOrDerivedSingularSubsequence x) :
    ∃ K : Set X, IsCompact K ∧ Disjoint K (derivedSet f.singularValues) ∧
      ∀ᶠ n in atTop, (f.totalize^[n]) x ∈ K := by
  let u := fun n => f.orbit n ⟨x, hx⟩
  obtain ⟨L, hL, huL⟩ := compact_range_of_no_escaping_subsequence u (by
    rintro ⟨φ, hφ, hlim⟩
    apply hno
    refine ⟨φ, hφ, Or.inl ?_⟩
    simpa only [f.compactifiedIterate_eq_orbit _ ⟨x, hx⟩] using hlim)
  have hsep : ∀ a, MapClusterPt a atTop u → a ∉ derivedSet f.singularValues := by
    intro a ha had
    obtain ⟨φ, hφ, hlim⟩ := ha.tendsto_subseq
    apply hno
    refine ⟨φ, hφ, Or.inr ⟨a, had, ?_⟩⟩
    simpa only [f.compactifiedIterate_eq_orbit _ ⟨x, hx⟩, Function.comp_def, u] using
      (OnePoint.continuous_coe.tendsto a).comp hlim
  let C : Set X := {a | MapClusterPt a atTop u}
  have hCc : IsCompact C := hL.of_isClosed_subset isClosed_setOfPred_clusterPt
    (fun a ha => hL.isClosed.mem_of_mapClusterPt ha (Eventually.of_forall huL))
  obtain ⟨B, hBo, hCB, hBder, hBc⟩ := exists_open_between_and_isCompact_closure hCc
    (isClosed_derivedSet f.singularValues).isOpen_compl (fun a ha => hsep a ha)
  refine ⟨closure B, hBc, disjoint_left.mpr (fun a ha => hBder ha), ?_⟩
  filter_upwards [eventually_mem_of_compact_cluster_subset u hL huL hBo (fun a ha => hCB ha)] with n hn
  rw [f.totalize_iterate_orbit n ⟨x, hx⟩]
  exact subset_closure hn

end SurfaceDynamics

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ae_has_escaping_or_derived_singular_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.HasEscapingOrDerivedSingularSubsequence := by
  classical
  let O : Opens X := ⟨(derivedSet f.singularValues)ᶜ,
    (isClosed_derivedSet f.singularValues).isOpen_compl⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let E : CompactExhaustion O := CompactExhaustion.choice O
  let K : ℕ → Set X := fun j => Subtype.val '' E j
  have hK : ∀ j, IsCompact (K j) := fun j => (E.isCompact j).image continuous_subtype_val
  have hKO : ∀ j, K j ⊆ O := by
    rintro j x ⟨y, _, rfl⟩
    exact y.property
  have hKavoid : ∀ j, Disjoint (K j) (derivedSet f.singularValues) := fun j =>
    disjoint_left.mpr (fun x hx => hKO j hx)
  let B : ℕ × ℕ → Set X := fun j => A ∩ ⋂ n : ℕ, (f.totalize^[n + j.2]) ⁻¹' K j.1
  have hBm : ∀ j, MeasurableSet (B j) := fun j => hA.inter
    (MeasurableSet.iInter (fun n => (hK j.1).isClosed.measurableSet.preimage
      ((f.measurable_totalize hf.2.continuous).iterate (n + j.2))))
  have hBtr : ∀ j, B j ⊆ f.trapped := fun _ _ hx => (hAbad hx.1).1
  apply chartAlmostEverywhere_of_countable_null_cover B
  · rintro x ⟨hxA, hxno⟩
    obtain ⟨L, hL, hLavoid, hxL⟩ :=
      f.exists_compact_tail_away_from_derived_of_no_subsequence (hAbad hxA).1 hxno
    have hLO : L ⊆ O := fun y hy => disjoint_left.mp hLavoid hy
    let LO : Set O := Subtype.val ⁻¹' L
    have hLOc : IsCompact LO := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert hL using 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, hLO hy⟩, hy, rfl⟩
    obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact hLOc
    obtain ⟨N, hN⟩ := eventually_atTop.mp hxL
    refine mem_iUnion.mpr ⟨(j, N), hxA, mem_iInter.mpr ?_⟩
    intro n
    have hh := hN (n + N) (by omega)
    exact ⟨⟨(f.totalize^[n + N]) x, hLO hh⟩, hj hh, rfl⟩
  · intro j p
    by_contra hnonzero
    have hpos : HasPositiveChartArea (B j) := ⟨p, pos_iff_ne_zero.mpr hnonzero⟩
    have hdisB : Pairwise (fun n m : ℕ =>
        Disjoint (f.imageAt n (B j)) (f.imageAt m (B j))) := by
      intro n m hnm
      apply (hdis hnm).mono
      · rintro y ⟨x, hx, hxy⟩; exact ⟨x, hx.1, hxy⟩
      · rintro y ⟨x, hx, hxy⟩; exact ⟨x, hx.1, hxy⟩
    have hinjB : f.InjectiveOnSaturation (B j) := by
      apply hinj.mono
      intro x hx
      obtain ⟨n, y, hy, hyx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, y, hy.1, hyx⟩
    let C := f.imageAt j.2 (B j)
    have hCm : MeasurableSet C := f.measurableSet_imageAt hf.2.continuous (hBtr j) hinjB (hBm j) j.2
    have hCbad : C ⊆ f.trapped \ f.omega :=
      f.imageAt_subset_trapped_diff_omega hf.2.continuous (inter_subset_left.trans hAbad) j.2
    have hCdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n C) (f.imageAt m C)) :=
      f.pairwise_disjoint_imageAt_shift (hBtr j) hdisB j.2
    have hCinj : f.InjectiveOnSaturation C := hinjB.mono
      (fun x hx => f.saturation_imageAt_subset (hBtr j) j.2 hx)
    have hCpos : HasPositiveChartArea C := f.positive_chart_area_imageAt hf (hBm j) (hBtr j) hinjB hpos j.2
    have hsat : f.saturation C ⊆ K j.1 := by
      intro y hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      rw [f.imageAt_imageAt (hBtr j), f.imageAt_eq_totalize_iterate_image (hBtr j)] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      exact mem_iInter.mp hx.2 n
    exact no_compact_positive_area_saturation_away_from_derived f hf hCm hCbad hCdis hCinj hCpos
      (hK j.1) (hKavoid j.1) hsat

end SurfaceDynamics.LocalMap
