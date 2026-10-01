module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.WanderingAnchors
public import BoundedWanderingDomains.Surfaces.SingularEncounters.HyperbolicWanderingEncounters
public import BoundedWanderingDomains.Surfaces.SingularEncounters.RestrictionEncounterTransport
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterPullback
public import BoundedWanderingDomains.Surfaces.RestrictedWanderingComponents

@[expose] public section

/-! # Compact wandering orbits through finitely many visited ambient components -/

open Set Function Filter Topology TopologicalSpace
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [Finite (ConnectedComponents X)]

theorem compact_wandering_encounters_on_finitely_many_visited_components
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (S : ℕ → Set X) (hS : ∀ n, f.IsComponent (S n))
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m)))
    (z : f.trapped) (hzS : ∀ n, f.orbit n z ∈ S n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K)
    (hvisited : ∀ c : ConnectedComponents X, ∃ n, ConnectedComponents.mk (f.orbit n z) = c) :
    ∃ a ∈ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous (S 0) z a := by
  classical
  obtain ⟨hSs, hfS⟩ := f.component_orbit_forward hf S hS z hzS
  obtain ⟨N, O, p, hNC, hSO, C, hC, hCO, htailC, B, hB, hremoved, havoidB⟩ :=
    f.exists_componentwise_anchor_restriction hf S hS hdis hfS z hzS hK hzK hvisited
  let : NoncompactComponents O := hNC
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let : MeasurableSpace O := borel O
  let : BorelSpace O := ⟨rfl⟩
  obtain ⟨V, hVs, hVO, hm, hfull⟩ := f.exists_full_restriction_to_open hf O
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hSV : ∀ n, S (n + N) ⊆ V := by
    intro n x hx
    apply hfull ⟨x, hSs (n + N) hx⟩ (hSO n hx)
    rw [← f.totalize_eq (hSs (n + N) hx)]
    apply hSO (n + 1)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfS (n + N) hx
  let zN := f.trappedMap^[N] z
  have hshift : ∀ n, f.orbit n zN = f.orbit (n + N) z := by
    intro n
    change ((f.trappedMap^[n]) ((f.trappedMap^[N]) z) : X) = ((f.trappedMap^[n + N]) z : X)
    rw [iterate_add_apply]
  have hzNr : (zN : X) ∈ r.trapped := f.restrictSource_mem_trapped_of_orbit_mem V hVs zN.property
    (fun n => hshift n ▸ hSV n (hzS (n + N)))
  have hSO0 : S N ⊆ O := by simpa only [Nat.zero_add] using hSO 0
  let zo : O := ⟨zN, hSO0 (hzS N)⟩
  let zg : g.trapped := ⟨zo, (r.mem_restrictAmbient_trapped_iff O hVO hm zo).mpr hzNr⟩
  have hb : ∀ n, (g.orbit n zg : X) = f.orbit (n + N) z := by
    intro n
    have hh := r.restrictAmbient_iterate_val O hVO hm n zo
    rw [g.iterate_eq_some_orbit n zg,
      f.restrictSource_iterate_eq_some_orbit V hVs zN.property
        (fun k => hshift k ▸ hSV k (hzS (k + N))) n] at hh
    exact (Option.some.inj hh).trans (hshift n)
  have hCOc : IsCompact ((Subtype.val : O → X) ⁻¹' C) := by
    rw [IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
    convert hC using 1
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hCO hx⟩, rfl⟩)
  have hgK : ∀ n, g.orbit n zg ∈ (Subtype.val ⁻¹' C : Set O) := by
    intro n
    change (g.orbit n zg : X) ∈ C
    rw [hb]
    exact htailC n
  have hfTail : ∀ n, MapsTo f.totalize (S (n + N)) (S (n + 1 + N)) := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfS (n + N)
  have hR := f.components_restrictAmbient_restrictSource_of_compact_orbit_connected hf O V p hVs hVO hm
    (fun n => S (n + N)) (fun n => hS (n + N)) hSV hfTail zg
    (fun n => hb n ▸ hzS (n + N)) hCOc hgK
  have hRdis : Pairwise (fun n m => Disjoint (Subtype.val ⁻¹' S (n + N) : Set O)
      (Subtype.val ⁻¹' S (m + N))) := by
    intro n m hnm
    exact (hdis (by omega : n + N ≠ m + N)).preimage Subtype.val
  obtain ⟨a, _, henc⟩ := SurfaceDynamics.compact_wandering_singular_encounters_of_components p g hg
    (fun n => Subtype.val ⁻¹' S (n + N)) hR hRdis zg
    (fun n => by change (g.orbit n zg : X) ∈ S (n + N); rw [hb]; exact hzS _) hCOc hgK
  have hzgS : (zg : O) ∈ (Subtype.val ⁻¹' S (0 + N) : Set O) := by
    change (zN : X) ∈ S (0 + N)
    simpa only [Nat.zero_add, zN, LocalMap.orbit] using hzS N
  obtain ⟨φ, _, hlim⟩ := HasSingularEncounterSequenceAt.successor_orbit_limit g hg.2.continuous henc hzgS
  have hlimX : Tendsto (fun n => f.orbit (φ n + N + 1) z) atTop (𝓝 (a : X)) := by
    have hh := continuous_subtype_val.continuousAt.tendsto.comp hlim
    change Tendsto (fun n => (g.orbit (φ n + 1) zg : X)) atTop (𝓝 (a : X)) at hh
    simpa only [hb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have haB : (a : X) ∉ B := by
    intro ha
    apply disjoint_left.mp havoidB ha
    exact isClosed_closure.mem_of_tendsto hlimX (Eventually.of_forall (fun n =>
      subset_closure (mem_range_self (φ n))))
  have hWg : (Subtype.val ⁻¹' S (0 + N) : Set O) ⊆ g.trapped := by
    obtain ⟨w, _, hw⟩ := hR 0
    exact (hw ▸ connectedComponentIn_subset _ _).trans
      (g.omega_subset_trapped_interior.trans interior_subset)
  have hencX := HasSingularEncounterSequenceAt.of_fullRestriction f hf.2.continuous
    O V hVs hVO hm hg.2.continuous hfull hB.isClosed hremoved zg zN rfl hWg haB henc
  have himage : Subtype.val '' (Subtype.val ⁻¹' S (0 + N) : Set O) = S N := by
    rw [Nat.zero_add]
    exact image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hSO0 hy⟩, rfl⟩)
  rw [himage] at hencX
  have hfinal := HasSingularEncounterSequenceAt.pullback_along_components f hf.2.continuous
    S hSs hfS N hencX
  exact ⟨a, hfinal.derived_mem f hf.2.continuous, hfinal⟩

end SurfaceDynamics.LocalMap
