/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainArea

/-! # Comparing ambient domain area with intrinsic subtype area -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- On a connected open domain, the componentwise density is the density of
any supplied disc cover of that domain. -/
theorem domainDensity_eq_connected (p : DiscCover M)
    (U : TopologicalSpace.Opens M) [ConnectedSpace U]
    (q : DiscCover U) (hUN : Nonempty U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (x : U) (hxc : (x : M) ∈ c.source) :
    p.domainDensity U c x =
      q.density (c.subtypeRestr hUN) x := by
  let V := componentDomain U (x : M)
  have hVU : V = U := by
    apply TopologicalSpace.Opens.ext
    exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected
      |>.connectedComponentIn x.property
  unfold domainDensity
  exact density_eq_of_domain_eq hVU (p.componentCover U x) q
    ⟨componentPoint U x⟩ hUN hc (mem_componentDomain x.property)
    x.property hxc

/-- In one ambient chart, domain area agrees with the intrinsic area of the
corresponding subset of a connected open subtype. -/
theorem domainArea_eq_hyperbolicArea_preimage_of_subset_chart
    (p : DiscCover M) (U : TopologicalSpace.Opens M) [ConnectedSpace U]
    (q : DiscCover U) (hUN : Nonempty U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hAc : A ⊆ c.source) :
    p.domainArea U A = q.hyperbolicArea (Subtype.val ⁻¹' A) := by
  let d := c.subtypeRestr hUN
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source :=
    mdifferentiableOn_subtypeRestr hUN hc
  have hpremeas : MeasurableSet (Subtype.val ⁻¹' A : Set U) :=
    hA.preimage measurable_subtype_coe
  have hpresource : Subtype.val ⁻¹' A ⊆ d.source := by
    intro x hx
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
      using hAc hx
  rw [p.domainArea_coordinate_formula U hc hA hAc,
    q.hyperbolicArea_apply_chart hd hpremeas hpresource]
  unfold coordinateArea
  have himage : d '' (Subtype.val ⁻¹' A : Set U) = c '' A := by
    ext z
    constructor
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨(x : M), hxA, rfl⟩
    · rintro ⟨x, hxA, rfl⟩
      let y : U := ⟨x, hAU hxA⟩
      exact ⟨y, hxA, rfl⟩
  rw [himage]
  apply setLIntegral_congr_fun
    (chart_image_measurable c (p.projection discZero) hA hAc)
  rintro z ⟨x, hxA, rfl⟩
  have hxU : x ∈ U := hAU hxA
  have hxt : c x ∈ domainChartSet U c := by
    refine ⟨c.map_source (hAc hxA), ?_⟩
    change c.symm (c x) ∈ (U : Set M)
    rwa [c.left_inv (hAc hxA)]
  dsimp only
  rw [p.domainChartDensity_of_mem U c hxt]
  have he := p.domainDensity_eq_connected U q hUN hc
    (⟨x, hxU⟩ : U) (hAc hxA)
  change ENNReal.ofReal ((p.domainDensity U c ⟨c.symm (c x), hxt.2⟩)^2) =
    ENNReal.ofReal ((q.density d (d.symm (c x)))^2)
  have hcx : c.symm (c x) = x := c.left_inv (hAc hxA)
  have hdt : c x ∈ d.target := by
    change c x ∈ (c.subtypeRestr hUN).target
    exact c.map_subtype_source hUN (x := (⟨x, hxU⟩ : U)) (hAc hxA)
  have hds : ((d.symm (c x) : U) : M) = c.symm (c x) :=
    c.subtypeRestr_symm_apply hUN hdt
  congr 2
  rw [hcx] at hds
  have hsub : d.symm (c x) = (⟨x, hxU⟩ : U) := Subtype.ext hds
  rw [hsub]
  simpa only [hcx] using he

/-- Domain area is supported on the open domain whose intrinsic metric it
uses. -/
theorem domainArea_compl_eq_zero (p : DiscCover M)
    (U : TopologicalSpace.Opens M) :
    p.domainArea U (U : Set M)ᶜ = 0 := by
  rw [domainArea, withDensity_apply _ U.isOpen.measurableSet.compl]
  apply setLIntegral_eq_zero U.isOpen.measurableSet.compl
  intro x hx
  have hxU : x ∉ U := hx
  simp [domainDensityRatio, hxU]

/-- For a connected open set, its ambient domain area is exactly the total
intrinsic area of any supplied disc cover of the subtype. -/
theorem domainArea_univ_eq_hyperbolicArea_univ_connected
    (p : DiscCover M) (U : TopologicalSpace.Opens M) [ConnectedSpace U]
    (q : DiscCover U) (hUN : Nonempty U) :
    p.domainArea U Set.univ = q.hyperbolicArea Set.univ := by
  letI : Nonempty M := ⟨p.projection discZero⟩
  let P : ChartPartition M := Classical.choice (exists_chartPartition (M := M))
  let B : ℕ → Set M := fun n => (U : Set M) ∩ P.piece n
  have hBmeas : ∀ n, MeasurableSet (B n) := fun n =>
    U.isOpen.measurableSet.inter (P.measurable n)
  have hBchart : ∀ n, B n ⊆ (P.chart n).source := fun n =>
    inter_subset_right.trans (P.subordinate n)
  have hBU : ∀ n, B n ⊆ U := fun _ => inter_subset_left
  have hBdis : Pairwise (Disjoint on B) :=
    pairwise_disjoint_mono P.disjoint (fun _ => inter_subset_right)
  have hBcover : ⋃ n, B n = (U : Set M) := by
    rw [← inter_iUnion, P.covers, inter_univ]
  have hprecover : ⋃ n, (Subtype.val : U → M) ⁻¹' B n =
      (Set.univ : Set U) := by
    ext x
    simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
    have hx : (x : M) ∈ ⋃ n, P.piece n := by rw [P.covers]; exact mem_univ _
    rw [mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, x.property, hn⟩
  have hpredis : Pairwise
      (Disjoint on fun n => (Subtype.val : U → M) ⁻¹' B n) := by
    intro i j hij
    exact (hBdis hij).preimage _
  have hpremeas : ∀ n, MeasurableSet
      ((Subtype.val : U → M) ⁻¹' B n) := fun n =>
    (hBmeas n).preimage measurable_subtype_coe
  have hlocal : ∀ n,
      p.domainArea U (B n) =
        q.hyperbolicArea ((Subtype.val : U → M) ⁻¹' B n) := fun n =>
    p.domainArea_eq_hyperbolicArea_preimage_of_subset_chart U q hUN
      (P.holomorphic n) (hBmeas n) (hBU n) (hBchart n)
  have hsupport : p.domainArea U (U : Set M) =
      p.domainArea U Set.univ := by
    apply measure_eq_measure_of_null_sdiff (subset_univ (U : Set M))
    apply measure_mono_null
      (show (Set.univ : Set M) \ (U : Set M) ⊆ (U : Set M)ᶜ by simp)
    exact p.domainArea_compl_eq_zero U
  calc
    p.domainArea U Set.univ = p.domainArea U (U : Set M) := hsupport.symm
    _ = ∑' n, p.domainArea U (B n) := by
      rw [← hBcover, measure_iUnion hBdis hBmeas]
    _ = ∑' n, q.hyperbolicArea ((Subtype.val : U → M) ⁻¹' B n) :=
      tsum_congr hlocal
    _ = q.hyperbolicArea Set.univ := by
      rw [← hprecover, measure_iUnion hpredis hpremeas]

end AreaDeficit.Surfaces.DiscCover

#print axioms AreaDeficit.Surfaces.DiscCover.domainDensity_eq_connected
#print axioms AreaDeficit.Surfaces.DiscCover.domainArea_eq_hyperbolicArea_preimage_of_subset_chart
#print axioms AreaDeficit.Surfaces.DiscCover.domainArea_univ_eq_hyperbolicArea_univ_connected
