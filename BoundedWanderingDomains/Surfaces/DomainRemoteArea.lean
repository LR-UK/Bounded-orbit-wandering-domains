/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainAreaGain
import BoundedWanderingDomains.Surfaces.DomainCompactGain

/-! # Intrinsic compact remote-removal bounds for arbitrary open domains -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem remote_domain_intrinsic_chart_gain (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {L D : Set ℂ} (hL : IsCompact L) (hD : IsOpen D) (hLD : L ⊆ D)
    (hDc : D ⊆ c.target) (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (A : Set M) (hA : IsClosed A),
      p.domainAreaGain ⟨Aᶜ,hA.isOpen_compl⟩
        ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩
        ((c.symm '' L) ∩ (A ∪ K)ᶜ) ≤ B := by
  obtain ⟨B,hB,hbound⟩ := p.remote_domain_chart_compact_gain hK hC hCK hc hL hD hLD hDc hDC
  refine ⟨B,hB,?_⟩
  intro A hA
  have hLt : L ⊆ c.target := hLD.trans hDc
  have hm : MeasurableSet ((c.symm '' L) ∩ (A ∪ K)ᶜ) :=
    (hL.image_of_continuousOn (c.symm.continuousOn.mono hLt)).measurableSet.inter
      (hA.union hK).measurableSet.compl
  have hs : ((c.symm '' L) ∩ (A ∪ K)ᶜ) ⊆ c.source := by
    rintro x ⟨⟨z,hz,rfl⟩,_⟩
    exact c.map_target (hLt hz)
  have he : c '' ((c.symm '' L) ∩ (A ∪ K)ᶜ) =
      L ∩ domainChartSet ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ c := by
    ext z
    constructor
    · rintro ⟨x,⟨⟨w,hw,rfl⟩,hx⟩,rfl⟩
      rw [c.right_inv (hLt hw)]
      exact ⟨hw,hLt hw,hx⟩
    · rintro ⟨hz,hzt,hzV⟩
      exact ⟨c.symm z,⟨⟨z,hz,rfl⟩,hzV⟩,c.right_inv hzt⟩
  rw [p.domainAreaGain_coordinate_formula _ _ hc hm hs,he]
  exact hbound A hA

variable [LocallyCompactSpace M]

/-- On a compact set separated from the new closed obstacle, the intrinsic
area gain has one finite bound valid for every old closed complement.
Disconnected domains are included componentwise. -/
theorem remote_compact_domainAreaGain_bound (p : DiscCover M)
    {K L : Set M} (hK : IsClosed K) (hL : IsCompact L) (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (A : Set M) (hA : IsClosed A),
      p.domainAreaGain ⟨Aᶜ,hA.isOpen_compl⟩
        ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ (L ∩ (A ∪ K)ᶜ) ≤ B := by
  have hLK' : L ⊆ Kᶜ := fun _ hx hxK => disjoint_left.mp hLK hx hxK
  obtain ⟨C,hC,hLC,hCKsub⟩ := exists_compact_between hL hK.isOpen_compl hLK'
  have hCK : Disjoint C K := disjoint_left.mpr (fun _ hx hxK => hCKsub hx hxK)
  obtain ⟨I,T,D,hT,hD,hTD,hDc,hDC,hcover⟩ := compact_finite_chart_patches hL hLC
  have hlocal : ∀ x : L, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (A : Set M) (hA : IsClosed A),
      p.domainAreaGain ⟨Aᶜ,hA.isOpen_compl⟩
        ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩
        (((chartAt ℂ (x : M)).symm '' T x) ∩ (A ∪ K)ᶜ) ≤ B := by
    intro x
    exact p.remote_domain_intrinsic_chart_gain hK hC hCK
      (mdifferentiable_chart (I := 𝓘(ℂ)) (x : M)).1
      (hT x) (hD x) (hTD x) (hDc x) (hDC x)
  choose B hB hbound using hlocal
  refine ⟨∑ x ∈ I, B x, ?_, ?_⟩
  · exact ENNReal.sum_ne_top.mpr (fun x _ => hB x)
  intro A hA
  let U : TopologicalSpace.Opens M := ⟨Aᶜ,hA.isOpen_compl⟩
  let V : TopologicalSpace.Opens M := ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩
  calc
    p.domainAreaGain U V (L ∩ (A ∪ K)ᶜ) ≤
        p.domainAreaGain U V (⋃ x ∈ I,
          ((chartAt ℂ (x : M)).symm '' T x) ∩ (A ∪ K)ᶜ) := by
      apply measure_mono
      intro y hy
      obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hcover hy.1)
      exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy.2⟩
    _ ≤ ∑ x ∈ I, p.domainAreaGain U V
        (((chartAt ℂ (x : M)).symm '' T x) ∩ (A ∪ K)ᶜ) :=
      measure_biUnion_finset_le I _
    _ ≤ ∑ x ∈ I, B x := Finset.sum_le_sum (fun x _ => hbound x A hA)

/-- The same estimate on the whole compact set, since the intrinsic gain
measure is supported on the smaller domain. -/
theorem remote_compact_domainAreaGain (p : DiscCover M)
    {K L : Set M} (hK : IsClosed K) (hL : IsCompact L) (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (A : Set M) (hA : IsClosed A),
      p.domainAreaGain ⟨Aᶜ,hA.isOpen_compl⟩
        ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ L ≤ B := by
  obtain ⟨B,hB,hbound⟩ := p.remote_compact_domainAreaGain_bound hK hL hLK
  refine ⟨B,hB,?_⟩
  intro A hA
  rw [← p.domainAreaGain_inter _ _ L]
  exact hbound A hA

/-- Open-domain formulation: localisation inside a fixed neighbourhood
has uniformly bounded gain on a compact subset of that neighbourhood. -/
theorem compact_localization_domainAreaGain (p : DiscCover M)
    (D : TopologicalSpace.Opens M) {L : Set M}
    (hL : IsCompact L) (hLD : L ⊆ D) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ U : TopologicalSpace.Opens M,
      p.domainAreaGain U (U ⊓ D) L ≤ B := by
  obtain ⟨B,hB,hbound⟩ := p.remote_compact_domainAreaGain D.isOpen.isClosed_compl hL
    (disjoint_left.mpr (fun _ hx hxD => hxD (hLD hx)))
  refine ⟨B,hB,?_⟩
  intro U
  have hU : (⟨(U : Set M)ᶜᶜ,U.isOpen.isClosed_compl.isOpen_compl⟩ :
      TopologicalSpace.Opens M) = U := by ext x; simp
  have hV : (⟨((U : Set M)ᶜ ∪ (D : Set M)ᶜ)ᶜ,
      (U.isOpen.isClosed_compl.union D.isOpen.isClosed_compl).isOpen_compl⟩ :
      TopologicalSpace.Opens M) = U ⊓ D := by ext x; simp
  simpa only [hU,hV] using hbound (U : Set M)ᶜ U.isOpen.isClosed_compl

end AreaDeficit.Surfaces.DiscCover
