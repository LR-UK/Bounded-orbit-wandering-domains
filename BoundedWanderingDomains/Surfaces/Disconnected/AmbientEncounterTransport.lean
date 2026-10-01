module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.RestrictionEncounterTransport

@[expose] public section

/-! # Returning encounters from an open ambient submanifold -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

theorem HasSingularEncounterSequenceAt.of_restrictAmbient
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : LocalMap X) (hf : Continuous f.map) (O : TopologicalSpace.Opens X)
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    (hg : Continuous (f.restrictAmbient O hsource hmap).map)
    (zg : (f.restrictAmbient O hsource hmap).trapped)
    {W : Set O} (hW : W ⊆ (f.restrictAmbient O hsource hmap).trapped) {x : O}
    (h : (f.restrictAmbient O hsource hmap).HasSingularEncounterSequenceAt hg W zg x) :
    f.HasSingularEncounterSequenceAt hf (Subtype.val '' W)
      ⟨((zg : O) : X), (f.mem_restrictAmbient_trapped_iff O hsource hmap (zg : O)).mp zg.property⟩
      (x : X) := by
  exact HasSingularEncounterSequenceAt.of_fullRestriction f hf O f.source subset_rfl hsource hmap
    hg (fun u _ _ => u.property) (B := ∅) isClosed_empty
    (fun u hu => False.elim (hu (hsource u.property))) zg _ rfl hW (notMem_empty _) h

end SurfaceDynamics.LocalMap
