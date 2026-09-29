module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ConfigurationCover
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactInnerExhaustions
public import BoundedWanderingDomains.Surfaces.SingularEncounters.SurfaceFiniteControl
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.NullCover
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.PositiveAreaImage

@[expose] public section

/-! # Almost-everywhere singular encounters on an arbitrary surface -/

open Set Function Filter MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ae_has_escaping_or_singular_encounters
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {A : Set X} (hA : MeasurableSet A) (hAbad : A ⊆ f.trapped \ f.omega)
    (hdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n A) (f.imageAt m A)))
    (hinj : f.InjectiveOnSaturation A) :
    ChartAlmostEverywhere A (f.HasEscapingOrSingularEncounters hf.2.continuous) := by
  classical
  obtain ⟨B, hBc, hBb⟩ := exists_countable_embeddedDisc_basis (X := X)
  let countableDiscs : Countable B := hBc.to_subtype
  let D : B → TopologicalSpace.Opens X := fun Q => Q.val.carrier
  obtain ⟨T, hTc, hT⟩ := f.exists_countable_pool_of_finite_obstructions hf.2.continuous D
  let countablePool : Countable T := hTc.to_subtype
  choose L hL hLD hLcover using fun i : B => exists_compact_inner_exhaustion (D i)
  let K := CompactExhaustion.choice X
  let Cfg := ℕ × ℕ × Finset (B × ℕ) × Finset T
  let C : Cfg → Set X := fun j => f.componentControlTail hf.2.continuous D L j.2.2.1
    (Subtype.val '' (j.2.2.2 : Set T)) (K j.1) A j.2.1
  have hCm : ∀ j, MeasurableSet (C j) := fun j =>
    f.measurableSet_componentControlTail hf.2.continuous D L
      (fun i m => (hL i m).measurableSet) j.2.2.1 _ _ A
      (K.isCompact j.1).measurableSet hA j.2.1
  have hCtr : ∀ j, C j ⊆ f.trapped := fun _ _ hx => (hAbad hx.1).1
  apply chartAlmostEverywhere_of_countable_null_cover C
  · exact f.no_encounters_subset_controlled_tails hf.2.continuous B hBb T
      (fun Q hQ a ha => hT ⟨Q, hQ⟩ a ha) L hLD hLcover K (fun x hx => (hAbad hx).1)
  · intro j chart
    by_contra hnonzero
    have hpos : HasPositiveChartArea (C j) := ⟨chart, pos_iff_ne_zero.mpr hnonzero⟩
    have hdisC : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n (C j)) (f.imageAt m (C j))) := by
      intro n m hnm
      apply (hdis hnm).mono
      · rintro y ⟨x, hx, hxy⟩; exact ⟨x, hx.1, hxy⟩
      · rintro y ⟨x, hx, hxy⟩; exact ⟨x, hx.1, hxy⟩
    have hinjC : f.InjectiveOnSaturation (C j) := by
      apply hinj.mono
      intro x hx
      obtain ⟨n, y, hy, hyx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, y, hy.1, hyx⟩
    let S := f.imageAt j.2.1 (C j)
    have hSm : MeasurableSet S :=
      f.measurableSet_imageAt hf.2.continuous (hCtr j) hinjC (hCm j) j.2.1
    have hSbad : S ⊆ f.trapped \ f.omega :=
      f.imageAt_subset_trapped_diff_omega hf.2.continuous (inter_subset_left.trans hAbad) j.2.1
    have hSdis : Pairwise (fun n m : ℕ => Disjoint (f.imageAt n S) (f.imageAt m S)) :=
      f.pairwise_disjoint_imageAt_shift (hCtr j) hdisC j.2.1
    have hSinj : f.InjectiveOnSaturation S := hinjC.mono
      (fun x hx => f.saturation_imageAt_subset (hCtr j) j.2.1 hx)
    have hSpos : HasPositiveChartArea S :=
      f.positive_chart_area_imageAt hf (hCm j) (hCtr j) hinjC hpos j.2.1
    have hsat : f.saturation S ⊆ K j.1 ∩
        f.componentControlRegion hf.2.continuous D L j.2.2.1
          (Subtype.val '' (j.2.2.2 : Set T)) := by
      intro y hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      rw [f.imageAt_imageAt (hCtr j), f.imageAt_eq_totalize_iterate_image (hCtr j)] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      exact mem_iInter.mp hx.2 n
    let E : Finset X := j.2.2.2.image Subtype.val
    have hE : (E : Set X) = Subtype.val '' (j.2.2.2 : Set T) := Finset.coe_image
    apply no_compact_positive_area_saturation_of_finite_component_control f hf
      hSm hSbad hSdis hSinj hSpos
      (K.isCompact j.1) (hsat.trans inter_subset_left)
      (fun i : j.2.2.1 => i.val.1.val) E (fun i : j.2.2.1 => L i.val.1 i.val.2)
      (fun i => hL i.val.1 i.val.2) (fun i => hLD i.val.1 i.val.2)
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsat hy).2
    refine ⟨i, hi.2, ?_⟩
    rw [hE]
    exact hi.1

end SurfaceDynamics.LocalMap
