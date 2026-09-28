/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactSurfaceCovering

/-! # Open interior model of a compact surface covering -/

open Set Function Topology

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [T2Space M]
  [TopologicalSpace N] [T2Space N]

/-- The open part of a compact source that maps into an open target. -/
def compactCoverDomain (K : Set M) (S : TopologicalSpace.Opens N)
    (f : M → N) (hf : Continuous f) : TopologicalSpace.Opens M :=
  ⟨interior K ∩ f ⁻¹' S, isOpen_interior.inter (S.isOpen.preimage hf)⟩

omit [T2Space M] [T2Space N] in
/-- A compact covering whose target fibres lie in the compact interior is
equivalently a covering between the corresponding open surface domains. -/
theorem compact_interior_isCoveringMap
    {f : M → N} {K : Set M} (S : TopologicalSpace.Opens N)
    (_hK : IsCompact K) (hf : Continuous f)
    (hint : ∀ z ∈ K, f z ∈ S → z ∈ interior K)
    (hcov : IsCoveringMapOn (fun z : K => f z) S) :
    IsCoveringMap (fun z : compactCoverDomain K S f hf =>
      (⟨f z, z.2.2⟩ : S)) := by
  let W := compactCoverDomain K S f hf
  let P : Set K := (fun z : K => f z) ⁻¹' (S : Set N)
  let e : W ≃ₜ P :=
    { toFun := fun z => ⟨⟨(z : M), interior_subset z.2.1⟩, z.2.2⟩
      invFun := fun z => ⟨(z.1 : M), hint z z.1.2 z.2, z.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hpre := hcov.isCoveringMap_restrictPreimage
  have hcomp := hpre.comp_homeomorph e
  convert hcomp using 1
  funext z
  rfl

end SurfaceDynamics
