module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompactWanderingEncounters
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseLocalCover

@[expose] public section

/-! # The combined compact-orbit theorem without chosen component covers -/

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics

theorem compact_wandering_singular_encounters_of_components
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NoncompactComponents X]
    (p : ComponentwiseDiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (R : ℕ → Set X) (hR : ∀ n, f.IsComponent (R n))
    (hdis : Pairwise (fun n m => Disjoint (R n) (R m)))
    (z : f.trapped) (hzR : ∀ n, f.orbit n z ∈ R n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K) :
    ∃ x ∈ K ∩ derivedSet f.singularValues,
      f.HasSingularEncounterSequenceAt hf.2.continuous (R 0) z x := by
  classical
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hRo : ∀ n, IsOpen (R n) := by
    intro n
    obtain ⟨x, _, hRx⟩ := hR n
    rw [hRx]
    exact f.isOpen_omega.connectedComponentIn
  let U : ℕ → TopologicalSpace.Opens X := fun n => ⟨R n, hRo n⟩
  have hq : ∀ n, ∃ q : DiscCover (U n), (q.projection discZero : X) = f.orbit n z := by
    intro n
    have hUc : IsConnected (U n : Set X) := by
      obtain ⟨x, hx, hRx⟩ := hR n
      change IsConnected (R n)
      rw [hRx]
      exact isConnected_connectedComponentIn_iff.mpr hx
    let : ConnectedSpace (U n) := Subtype.connectedSpace hUc
    obtain ⟨q, hq⟩ := (Classical.choice (p.nonempty_subdomain (U n))).exists_centred ⟨_, hzR n⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  choose q hq0 using hq
  exact BKL.compact_wandering_singular_encounters p f hf U q hR hdis z hq0 hK hzK

end SurfaceDynamics
