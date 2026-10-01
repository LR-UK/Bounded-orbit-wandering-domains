module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactOrbitNormal
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseDiscImages
public import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs
public import BoundedWanderingDomains.Surfaces.SubdomainCover
public import BoundedWanderingDomains.Surfaces.ComponentDomains
public import BoundedWanderingDomains.BarrierComponents

@[expose] public section

/-! # A compact marked orbit makes its entire barrier component normal -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
theorem trapped_barrier_component (f : LocalMap X) (hf : Continuous f.map)
    [LocallyConnectedSpace X] {A : Set X} (_hA : IsClosed A)
    (hfront : frontier (f.source : Set X) ⊆ A)
    (hback : ∀ x : f.source, f.map x ∈ A → (x : X) ∈ A)
    {x : X} (hx : x ∈ f.trapped) (hxA : x ∉ A) :
    connectedComponentIn Aᶜ x ⊆ f.trapped := by
  let C := connectedComponentIn Aᶜ x
  have hxC : x ∈ C := mem_connectedComponentIn hxA
  have hCA : C ⊆ Aᶜ := connectedComponentIn_subset _ _
  have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCs : C ⊆ f.source := AreaDeficit.preconnected_subset_of_avoids_frontier
    hCc f.source.isOpen hfront hCA ⟨x, hxC, f.trapped_subset_source hx⟩
  have hit : ∀ n, ContinuousOn (f.totalize^[n]) C ∧
      MapsTo (f.totalize^[n]) C ((f.source : Set X) \ A) := by
    intro n
    induction n with
    | zero => exact ⟨continuousOn_id, fun y hy => ⟨hCs hy, hCA hy⟩⟩
    | succ n ih =>
        have hc : ContinuousOn (f.totalize^[n + 1]) C := by
          simpa only [iterate_succ'] using (f.continuousOn_totalize hf).comp ih.1
            (fun y hy => (ih.2 hy).1)
        have ha : f.totalize^[n + 1] '' C ⊆ Aᶜ := by
          rintro y ⟨w, hw, rfl⟩ hyA
          apply (ih.2 hw).2
          apply hback ⟨(f.totalize^[n]) w, (ih.2 hw).1⟩
          rwa [iterate_succ_apply', f.totalize_eq (ih.2 hw).1] at hyA
        have hs : f.totalize^[n + 1] '' C ⊆ f.source :=
          AreaDeficit.preconnected_subset_of_avoids_frontier (hCc.image _ hc)
            f.source.isOpen hfront ha ⟨(f.totalize^[n + 1]) x, ⟨x, hxC, rfl⟩,
              by rw [f.totalize_iterate_orbit (n + 1) ⟨x, hx⟩]; exact f.orbit_mem_source _ _⟩
        exact ⟨hc, fun y hy => ⟨hs ⟨y, hy, rfl⟩, ha ⟨y, hy, rfl⟩⟩⟩
  intro y hy
  rw [← f.trappedSet_totalize_eq_trapped]
  exact fun n => ((hit n).2 hy).1

omit [LocallyCompactSpace X] in
theorem compact_orbits_on_connected_trapped_open
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : ComponentwiseDiscCover X)
    (W : TopologicalSpace.Opens X) [ConnectedSpace W]
    (hW : (W : Set X) ⊆ f.trapped) (x : W)
    {K : Set X} (hK : IsCompact K)
    (hxK : ∀ n, f.orbit n ⟨x, hW x.property⟩ ∈ K) :
    ∀ y : W, ∃ L : Set X, IsCompact L ∧
      ∀ n, f.orbit n ⟨y, hW y.property⟩ ∈ L := by
  classical
  obtain ⟨q, hq0⟩ := (Classical.choice (p.nonempty_subdomain W)).exists_centred x
  let F : ℕ → unitDisc → X := fun n => f.orbitOn W hW n ∘ q.projection
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (f.mdifferentiable_orbitOn hf W hW n).comp q.holomorphic
  have hF0 : ∀ n, F n discZero ∈ K := by
    intro n
    simpa only [F, comp_apply, hq0, orbitOn] using hxK n
  intro y
  obtain ⟨w, hw⟩ := q.surjective y
  obtain ⟨L, hL, hbound⟩ := p.compact_disc_images hK
    (show ‖(w : ℂ)‖ < 1 from mem_ball_zero_iff.mp w.property)
  have hyK : ∀ n, f.orbitOn W hW n y ∈ L := by
    intro n
    have hh := hbound (F n) (hF n) (hF0 n) w le_rfl
    simpa only [F, comp_apply, hw] using hh
  exact ⟨L, hL, hyK⟩

theorem connected_trapped_open_subset_omega_of_compact_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : ComponentwiseDiscCover X)
    (W : TopologicalSpace.Opens X) [ConnectedSpace W]
    (hW : (W : Set X) ⊆ f.trapped) (x : W)
    {K : Set X} (hK : IsCompact K)
    (hxK : ∀ n, f.orbit n ⟨x, hW x.property⟩ ∈ K) :
    (W : Set X) ⊆ f.omega := by
  intro y hy
  obtain ⟨L, hL, hyL⟩ :=
    f.compact_orbits_on_connected_trapped_open hf p W hW x hK hxK ⟨y, hy⟩
  exact f.mem_omega_of_compact_orbit hf p W hW ⟨y, hy⟩ hL hyL

theorem barrier_component_subset_omega_of_compact_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : ComponentwiseDiscCover X)
    {A : Set X} (hA : IsClosed A)
    (hfront : frontier (f.source : Set X) ⊆ A)
    (hback : ∀ x : f.source, f.map x ∈ A → (x : X) ∈ A)
    {x : X} (hx : x ∈ f.trapped) (hxA : x ∉ A)
    {K : Set X} (hK : IsCompact K) (hxK : ∀ n, f.orbit n ⟨x, hx⟩ ∈ K) :
    connectedComponentIn Aᶜ x ⊆ f.omega := by
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let W := componentDomain ⟨Aᶜ, hA.isOpen_compl⟩ x
  let : ConnectedSpace W := componentDomain_connected hxA
  exact f.connected_trapped_open_subset_omega_of_compact_orbit hf p W
    (f.trapped_barrier_component hf.2.continuous hA hfront hback hx hxA)
    ⟨x, mem_componentDomain hxA⟩ hK hxK

end SurfaceDynamics.LocalMap
