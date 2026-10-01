module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.FiniteVisitedWandering
public import BoundedWanderingDomains.Surfaces.Disconnected.FiniteComponents
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenComponents
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenEncounterTransport
public import BoundedWanderingDomains.Surfaces.Disconnected.AmbientEncounterTransport

@[expose] public section

/-! # The compact wandering-orbit theorem without ambient connectedness -/

open Set Function Filter Topology TopologicalSpace
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]

theorem compact_wandering_singular_encounters_disconnected
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (S : ℕ → Set X) (hS : ∀ n, f.IsComponent (S n))
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m)))
    (z : f.trapped) (hzS : ∀ n, f.orbit n z ∈ S n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ a ∈ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous (S 0) z a := by
  classical
  have hfinite : (range (fun n => ConnectedComponents.mk (f.orbit n z))).Finite :=
    (finite_components_of_isCompact hK).subset (by rintro _ ⟨n, rfl⟩; exact ⟨_, hzK n, rfl⟩)
  let I := hfinite.toFinset
  let O := componentUnion I
  have hO : IsClosed (O : Set X) := isClosed_componentUnion I
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hzO : ∀ n, f.orbit n z ∈ O := fun n =>
    (mem_componentUnion I _).mpr (hfinite.mem_toFinset.mpr (mem_range_self n))
  have hSO : ∀ n, S n ⊆ O := by
    intro n y hy
    have hc : IsPreconnected (S n) := by
      obtain ⟨a, _, ha⟩ := hS n
      rw [ha]
      exact isPreconnected_connectedComponentIn
    have he : ConnectedComponents.mk y = ConnectedComponents.mk (f.orbit n z) :=
      ConnectedComponents.coe_eq_coe'.mpr (hc.subset_connectedComponent (hzS n) hy)
    apply (mem_componentUnion I y).mpr
    rw [he]
    exact (mem_componentUnion I _).mp (hzO n)
  obtain ⟨hSs, hfS⟩ := f.component_orbit_forward hf S hS z hzS
  obtain ⟨V, hVs, hVO, hm, hfull⟩ := f.exists_full_restriction_to_open hf O
  have hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X)) := by
    have he : (Subtype.val : f.source → X) ⁻¹' (V : Set X) =
        (Subtype.val ⁻¹' (O : Set X)) ∩ f.map ⁻¹' (O : Set X) := by
      ext u
      constructor
      · intro hu
        exact ⟨hVO hu, hm ⟨u, hu⟩⟩
      · rintro ⟨hu, hfu⟩
        exact hfull u hu hfu
    rw [he]
    exact (hO.preimage continuous_subtype_val).inter (hO.preimage hf.2.continuous)
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hSV : ∀ n, S n ⊆ V := by
    intro n x hx
    apply hfull ⟨x, hSs n hx⟩ (hSO n hx)
    rw [← f.totalize_eq (hSs n hx)]
    exact hSO (n + 1) (hfS n hx)
  have hStr : ∀ n, S n ⊆ r.trapped := by
    intro n x hx
    have hxt : x ∈ f.trapped := by
      obtain ⟨a, _, ha⟩ := hS n
      exact (f.omega_subset_trapped_interior.trans interior_subset)
        (connectedComponentIn_subset _ _ (ha ▸ hx))
    apply f.restrictSource_mem_trapped_of_orbit_mem V hVs hxt
    intro k
    rw [← f.totalize_iterate_orbit k ⟨x, hxt⟩]
    apply hSV (n + k)
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hfS (n + k) ih
  have hSr : ∀ n, r.IsComponent (S n) := fun n =>
    f.isComponent_restrictSource_of_trapped V hVs (hS n) (hStr n)
  let R : ℕ → Set O := fun n => Subtype.val ⁻¹' S n
  have hR : ∀ n, g.IsComponent (R n) := fun n =>
    r.isComponent_restrictAmbient_of_isClosed O hO hVO hm (hSr n)
  have hz0 : (z : X) ∈ r.trapped := hStr 0 (hzS 0)
  let zo : O := ⟨z, hzO 0⟩
  let zg : g.trapped := ⟨zo, (r.mem_restrictAmbient_trapped_iff O hVO hm zo).mpr hz0⟩
  have hb : ∀ n, (g.orbit n zg : X) = f.orbit n z := by
    intro n
    have he := r.restrictAmbient_iterate_val O hVO hm n zo
    rw [g.iterate_eq_some_orbit n zg,
      f.restrictSource_iterate_eq_of_restricted_trapped V hVs hz0 n,
      f.iterate_eq_some_orbit n z] at he
    exact Option.some.inj he
  have hRdis : Pairwise (fun n m => Disjoint (R n) (R m)) :=
    fun _ _ hnm => (hdis hnm).preimage Subtype.val
  have hzgR : ∀ n, g.orbit n zg ∈ R n := by
    intro n
    change (g.orbit n zg : X) ∈ S n
    rw [hb]
    exact hzS n
  have hKO : IsCompact ((Subtype.val : O → X) ⁻¹' K) :=
    hO.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hzgK : ∀ n, g.orbit n zg ∈ (Subtype.val ⁻¹' K : Set O) := by
    intro n
    change (g.orbit n zg : X) ∈ K
    rw [hb]
    exact hzK n
  have hvisit : ∀ c : ConnectedComponents O, ∃ n, ConnectedComponents.mk (g.orbit n zg) = c := by
    apply visits_all_components_of_ambient_labels O hO
    intro x
    obtain ⟨n, hn⟩ := hfinite.mem_toFinset.mp ((mem_componentUnion I (x : X)).mp x.property)
    exact ⟨n, by rw [hb]; exact hn⟩
  obtain ⟨a, _, henc⟩ := g.compact_wandering_encounters_on_finitely_many_visited_components hg R hR
    hRdis zg hzgR hKO hzgK hvisit
  have hRt : R 0 ⊆ g.trapped := by
    obtain ⟨a, _, ha⟩ := hR 0
    exact (ha ▸ connectedComponentIn_subset _ _).trans (g.omega_subset_trapped_interior.trans interior_subset)
  have hencR := HasSingularEncounterSequenceAt.of_restrictAmbient r hr.2.continuous O hVO hm
    hg.2.continuous zg hRt henc
  have himage : (Subtype.val : O → X) '' R 0 = S 0 :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hSO 0 hx⟩, rfl⟩)
  rw [himage] at hencR
  have hfinal := HasSingularEncounterSequenceAt.of_clopenSourceRestriction f hf.2.continuous
    V hVs hVc _ (hStr 0) hencR
  exact ⟨a, hfinal.derived_mem f hf.2.continuous, hfinal⟩

end SurfaceDynamics.LocalMap
