/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.RestrictedBarrierComponents

/-! # Complete boundary-preimage package inside a covered subsurface -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- A compact set in the source of a local map whose source lies in a fixed
disc-covered subsurface admits the complete finite boundary-preimage package,
including identification of complementary and normality components. -/
theorem exists_boundaryBarrierPackage_in_subsurface
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (hsourceO : (f.source : Set X) ⊆ O)
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ f.source) :
    ∃ (V : TopologicalSpace.Opens X)
      (hVsource : closure (V : Set X) ⊆ f.source) (P : ℕ → Set X),
      K ⊆ V ∧ IsCompact (closure (V : Set X)) ∧
      Monotone P ∧ (∀ n, (P n).Finite) ∧
      frontier (V : Set X) ⊆ closure (⋃ n, P n) ∧
      let g := f.restrictSource V (subset_trans subset_closure hVsource)
      Disjoint (closure (⋃ n, P n)) g.omega ∧
      g.trapped \ g.omega ⊆ closure (⋃ n, P n) ∧
      (∀ x ∈ g.omega,
        connectedComponentIn (closure (⋃ n, P n))ᶜ x =
          connectedComponentIn g.omega x) := by
  obtain ⟨V0, hVsource, P, hVopen, hKV, hVcompact, hPmono, hPfinite,
      hfront, hnormal, hback⟩ :=
    f.exists_boundaryPunctureSequence hf hK hKsource
  let V : TopologicalSpace.Opens X := ⟨V0, hVopen⟩
  have hVO : closure (V : Set X) ⊆ O := hVsource.trans hsourceO
  let g := f.restrictSource V (subset_trans subset_closure hVsource)
  have hdis : Disjoint (closure (⋃ n, P n)) g.omega := hnormal hVopen
  have homega : g.omega = interior g.trapped :=
    f.omega_restrictSource_eq_interior_trapped hf O V p
      (subset_trans subset_closure hVsource) hVcompact hVO
  have hbad : g.trapped \ g.omega ⊆ closure (⋃ n, P n) := by
    letI : LocallyPathConnectedSpace X :=
      ChartedSpace.locallyPathConnectedSpace ℂ X
    exact g.trapped_diff_omega_subset_barrier
      (f.isOpenHolomorphic_restrictSource hf V
        (subset_trans subset_closure hVsource)).2.continuous
      isClosed_closure (by
        change frontier (V : Set X) ⊆ closure (⋃ n, P n)
        exact hfront)
      (fun x hx => hback (x : X) x.property hx) homega
  refine ⟨V, hVsource, P, hKV, hVcompact, hPmono, hPfinite,
    hfront, hdis, hbad, ?_⟩
  intro x hx
  exact f.restricted_barrier_component_eq_omega hf O V p
    (subset_trans subset_closure hVsource) hVcompact hVO
    isClosed_closure hfront (fun y hy => hback (y : X) y.property hy) hdis hx

end SurfaceDynamics.LocalMap

#print axioms SurfaceDynamics.LocalMap.exists_boundaryBarrierPackage_in_subsurface
