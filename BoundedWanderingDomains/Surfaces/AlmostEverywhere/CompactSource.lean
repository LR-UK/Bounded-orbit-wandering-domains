/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions
import BoundedWanderingDomains.Surfaces.SurfacePositiveArea
import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange

/-! # Almost-everywhere escape from source compact sets -/

open Set Function Filter MeasureTheory OnePoint
open scoped Topology Manifold

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Every compact subset of the actual source is left arbitrarily late. -/
def LocalMap.FrequentlyLeavesSourceCompacts (f : LocalMap X) (x : X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ f.source →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      f.compactifiedIterate n x ∉ ((↑) : X → OnePoint X) '' K

theorem ChartAlmostEverywhere.mono {A : Set X} {P Q : X → Prop}
    (h : ChartAlmostEverywhere A P) (hPQ : ∀ x ∈ A, P x → Q x) :
    ChartAlmostEverywhere A Q := by
  intro p
  apply measure_mono_null (image_mono (inter_subset_inter_left _ ?_)) (h p)
  rintro x ⟨hx, hn⟩
  exact ⟨hx, fun hp => hn (hPQ x hx hp)⟩

theorem chartAlmostEverywhere_of_countable_null_cover
    {ι : Type*} [Countable ι] {A : Set X} {P : X → Prop} (B : ι → Set X)
    (hcover : {x ∈ A | ¬ P x} ⊆ ⋃ n, B n)
    (hnull : ∀ n p, volume ((chartAt ℂ p) '' (B n ∩ (chartAt ℂ p).source)) = 0) :
    ChartAlmostEverywhere A P := by
  intro p
  apply measure_mono_null (image_mono (inter_subset_inter_left _ hcover))
  rw [iUnion_inter, image_iUnion]
  exact measure_iUnion_null (fun n => hnull n p)

namespace LocalMap

variable [T2Space X] [LocallyCompactSpace X]

omit [ChartedSpace ℂ X] [T2Space X] [LocallyCompactSpace X] in
theorem exists_compact_source_orbit_of_not_frequently_leaves
    (f : LocalMap X) {x : X} (hx : x ∈ f.trapped)
    (hno : ¬ f.FrequentlyLeavesSourceCompacts x) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ f.source ∧
      ∀ n, (f.totalize^[n]) x ∈ K := by
  classical
  simp only [FrequentlyLeavesSourceCompacts, not_forall, not_exists, not_and,
    not_not] at hno
  obtain ⟨K, hK, hKs, N, htail⟩ := hno
  let F : Set X := (fun n => (f.totalize^[n]) x) '' (Finset.range N : Set ℕ)
  refine ⟨K ∪ F, hK.union ((Finset.finite_toSet _).image _).isCompact, ?_, ?_⟩
  · rintro y (hy | ⟨n, _, rfl⟩)
    · exact hKs hy
    · change (f.totalize^[n]) x ∈ f.source
      rw [f.totalize_iterate_orbit n ⟨x, hx⟩]
      exact f.orbit_mem_source n ⟨x, hx⟩
  · intro n
    by_cases hn : N ≤ n
    · apply Or.inl
      obtain ⟨y, hy, he⟩ := htail n hn
      rw [f.compactifiedIterate_eq_orbit n ⟨x, hx⟩] at he
      have he' := OnePoint.coe_injective he
      rw [f.totalize_iterate_orbit n ⟨x, hx⟩, ← he']
      exact hy
    · exact Or.inr ⟨n, by simpa using (Nat.lt_of_not_ge hn), rfl⟩

variable [SecondCountableTopology X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X]

omit [ChartedSpace ℂ X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) 1 X] [MeasurableSpace X] [BorelSpace X] in
theorem has_source_escaping_subsequence_of_frequently_leaves
    (f : LocalMap X) {x : X} (hx : x ∈ f.trapped)
    (hleave : f.FrequentlyLeavesSourceCompacts x) :
    f.HasSourceEscapingSubsequence x := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  let u : ℕ → f.source := fun n => ⟨f.orbit n ⟨x, hx⟩, f.orbit_mem_source n ⟨x, hx⟩⟩
  have hex : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : OnePoint f.source)) atTop (𝓝 (∞ : OnePoint f.source)) := by
    by_contra hno
    obtain ⟨K, hK, hu⟩ := compact_range_of_no_escaping_subsequence u hno
    obtain ⟨n, _, hn⟩ := hleave (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro y ⟨z, _, rfl⟩; exact z.property) 0
    apply hn
    exact ⟨(u n : X), ⟨u n, hu n, rfl⟩, (f.compactifiedIterate_eq_orbit n ⟨x, hx⟩).symm⟩
  obtain ⟨φ, hφ, hlim⟩ := hex
  refine ⟨φ, hφ, ?_⟩
  intro K hK hKs
  let KO : Set f.source := Subtype.val ⁻¹' K
  have hKO : IsCompact KO := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hK using 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hy; exact ⟨⟨y, hKs hy⟩, hy, rfl⟩
  filter_upwards [(tendsto_infty_iff_leaves_compacts _).mp hlim KO hKO] with n hn
  rintro ⟨y, hy, he⟩
  apply hn
  change f.orbit (φ n) ⟨x, hx⟩ ∈ K
  rw [f.compactifiedIterate_eq_orbit (φ n) ⟨x, hx⟩] at he
  exact OnePoint.coe_injective he ▸ hy

theorem ae_frequently_leaves_source_compacts
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.FrequentlyLeavesSourceCompacts := by
  classical
  let : LocallyCompactSpace f.source := f.source.isOpen.locallyCompactSpace
  let E : CompactExhaustion f.source := CompactExhaustion.choice f.source
  let K : ℕ → Set X := fun j => Subtype.val '' E j
  have hK : ∀ j, IsCompact (K j) := fun j =>
    (E.isCompact j).image continuous_subtype_val
  have hKs : ∀ j, K j ⊆ f.source := by
    rintro j x ⟨y, _, rfl⟩
    exact y.property
  let B : ℕ → Set X := fun j => A ∩ ⋂ n : ℕ, (f.totalize^[n]) ⁻¹' K j
  have hBA : ∀ j, B j ⊆ A := fun _ => inter_subset_left
  have hBm : ∀ j, MeasurableSet (B j) := fun j => hA.inter
    (MeasurableSet.iInter (fun n => (hK j).isClosed.measurableSet.preimage
      ((f.measurable_totalize hf.2.continuous).iterate n)))
  have hsatK : ∀ j, f.saturation (B j) ⊆ K j := by
    intro j y hy
    obtain ⟨n, x, hx, hxy⟩ := mem_iUnion.mp hy
    have hxt : x ∈ f.trapped := (hAbad hx.1).1
    have hy' : y = f.orbit n ⟨x, hxt⟩ :=
      Option.some.inj (hxy.symm.trans (f.iterate_eq_some_orbit n ⟨x, hxt⟩))
    have hh := mem_iInter.mp hx.2 n
    change (f.totalize^[n]) x ∈ K j at hh
    rwa [f.totalize_iterate_orbit n ⟨x, hxt⟩, ← hy'] at hh
  apply chartAlmostEverywhere_of_countable_null_cover B
  · rintro x ⟨hxA, hxno⟩
    obtain ⟨L, hL, hLs, hxL⟩ :=
      f.exists_compact_source_orbit_of_not_frequently_leaves (hAbad hxA).1 hxno
    let LO : Set f.source := Subtype.val ⁻¹' L
    have hLO : IsCompact LO := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert hL using 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hLs hy⟩, hy, rfl⟩
    obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact hLO
    refine mem_iUnion.mpr ⟨j, hxA, mem_iInter.mpr ?_⟩
    intro n
    exact ⟨⟨(f.totalize^[n]) x, hLs (hxL n)⟩, hj (hxL n), rfl⟩
  · intro j p
    by_contra hnonzero
    have hpos : HasPositiveChartArea (B j) := ⟨p, pos_iff_ne_zero.mpr hnonzero⟩
    have hdisB : Pairwise (fun n m : ℕ =>
        Disjoint (f.imageAt n (B j)) (f.imageAt m (B j))) := by
      intro n m hnm
      apply (hdis hnm).mono
      · rintro y ⟨x, hx, hxy⟩
        exact ⟨x, hx.1, hxy⟩
      · rintro y ⟨x, hx, hxy⟩
        exact ⟨x, hx.1, hxy⟩
    have hinjB : f.InjectiveOnSaturation (B j) := by
      apply hinj.mono
      intro x hx
      obtain ⟨n, y, hy, hyx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, y, hy.1, hyx⟩
    exact noCompactPositiveAreaWanderingSetClaim f hf (B j) (hBm j)
      ((hBA j).trans hAbad) hdisB hinjB hpos ⟨K j, hK j, hKs j, hsatK j⟩

theorem ae_has_source_escaping_subsequence
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A f.HasSourceEscapingSubsequence :=
  (f.ae_frequently_leaves_source_compacts hf hA hAbad hdis hinj).mono
    (fun _ hx hp => f.has_source_escaping_subsequence_of_frequently_leaves (hAbad hx).1 hp)

end LocalMap
end SurfaceDynamics
