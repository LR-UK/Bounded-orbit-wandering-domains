/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BoundaryBarrierPackage
import BoundedWanderingDomains.Surfaces.RestrictionSaturationBridge

/-! # Boundary-puncture reduction for a compact wandering saturation -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- A compactly contained bad forward saturation admits one relatively
compact restricted source and an increasing finite puncture barrier whose
closure contains the original set.  This packages the topological reduction
needed before the finite-model area contradiction. -/
theorem exists_positiveArea_boundaryBarrier
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (hsourceO : (f.source : Set X) ⊆ O)
    {A K : Set X} (hA : A ⊆ f.trapped \ f.omega)
    (hK : IsCompact K) (hKsource : K ⊆ f.source)
    (hsatK : f.saturation A ⊆ K) :
    ∃ (V : TopologicalSpace.Opens X)
      (hVsource : closure (V : Set X) ⊆ f.source) (P : ℕ → Finset X),
      K ⊆ V ∧ IsCompact (closure (V : Set X)) ∧ Monotone P ∧
      (∀ n x (hx : x ∈ V), x ∈ P n →
        f.map ⟨x, hVsource (subset_closure hx)⟩ ∈ P n) ∧
      A ⊆ (f.restrictSource V
        (subset_trans subset_closure hVsource)).trapped \
        (f.restrictSource V
          (subset_trans subset_closure hVsource)).omega ∧
      A ⊆ closure (⋃ n, ((P n : Finset X) : Set X)) := by
  obtain ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward, hbad⟩ :=
    f.exists_boundaryBarrierFinsetPackage_in_subsurface
      hf O p hsourceO hK hKsource
  let hVs : (V : Set X) ⊆ f.source :=
    subset_trans subset_closure hVsource
  have hsatV : f.saturation A ⊆ V := hsatK.trans hKV
  have hArestrict :
      A ⊆ (f.restrictSource V hVs).trapped \ (f.restrictSource V hVs).omega :=
    f.subset_restrictSource_trapped_diff_omega_of_saturation_subset
      V hVs hA hsatV
  exact ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPforward,
    hArestrict, hArestrict.trans hbad⟩

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.exists_positiveArea_boundaryBarrier
