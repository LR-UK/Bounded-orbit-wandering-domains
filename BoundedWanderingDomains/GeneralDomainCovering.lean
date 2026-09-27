/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import RiemannDynamics.Uniformization.PuncturedPlaneBridge
import RiemannDynamics.Uniformization.Trichotomy

/-!
# Disc coverings for arbitrary hyperbolic plane domains

The finite-puncture construction extends to any connected open set omitting
two points, using the existing uniformisation trichotomy.
-/

open Set Metric Function TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

/-- Uniformisation gives a holomorphic disc covering of any infinite,
connected open plane set that omits two points. -/
theorem exists_disc_covering_open_domain (U : Opens ℂ)
    [ConnectedSpace U] (x₀ : U) (hinf : (U : Set ℂ).Infinite)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U) :
    ∃ p : ℂ → ℂ, AreaDeficit.IsHolomorphicDiscCovering p U := by
  let : T2Space (PathCover x₀) := t2space_pathCover x₀
  let : SimplyConnectedSpace (PathCover x₀) := simplyConnectedSpace_pathCover x₀
  let : SecondCountableTopology (PathCover x₀) := secondCountableTopology_pathCover x₀
  exact exists_disc_covering_of_models U x₀ hinf hab ha hb
    (uniformization_trichotomy (PathCover x₀))

/-- Every component of the complement of a closed set omitting two points
has a holomorphic disc covering. -/
theorem exists_disc_covering_complement_component
    {A : Set ℂ} (hA : IsClosed A) {z a b : ℂ}
    (hz : z ∉ A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ p : ℂ → ℂ, AreaDeficit.IsHolomorphicDiscCovering p
      (connectedComponentIn Aᶜ z) := by
  let U : Set ℂ := connectedComponentIn Aᶜ z
  have hUopen : IsOpen U := hA.isOpen_compl.connectedComponentIn
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUconn : IsConnected U := ⟨⟨z, hzU⟩, isPreconnected_connectedComponentIn⟩
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUconn
  have hUinf : U.Infinite := infinite_of_mem_nhds z (hUopen.mem_nhds hzU)
  exact exists_disc_covering_open_domain ⟨U, hUopen⟩ ⟨z, hzU⟩ hUinf
    hab (fun h => (connectedComponentIn_subset _ _ h) ha)
    (fun h => (connectedComponentIn_subset _ _ h) hb)

end RiemannDynamics

namespace AreaDeficit

/-- The density of a hyperbolic domain is independent of the choice of
holomorphic universal disc covering. -/
theorem IsHolomorphicDiscCovering.coveringDensity_eq
    {S : Set ℂ} {p q : ℂ → ℂ}
    (hp : IsHolomorphicDiscCovering p S)
    (hq : IsHolomorphicDiscCovering q S)
    {z : ℂ} (hz : z ∈ S) :
    coveringDensity p z = coveringDensity q z := by
  have compare {u v : ℂ → ℂ}
      (hu : IsHolomorphicDiscCovering u S)
      (hv : IsHolomorphicDiscCovering v S) :
      coveringDensity u z ≤ coveringDensity v z := by
    obtain ⟨g, hgdiff, hgmap, hg0, hgext⟩ := hv.density_extremal hz
    have hnorm : 0 < ‖deriv g 0‖ := by
      have hne : ‖deriv g 0‖ ≠ 0 := by
        intro heq
        rw [heq, mul_zero] at hgext
        norm_num at hgext
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hs := hu.density_schwarz hgdiff hgmap
    rw [hg0] at hs
    exact (mul_le_mul_iff_left₀ hnorm).mp (hs.trans_eq hgext.symm)
  exact le_antisymm (compare hp hq) (compare hq hp)

end AreaDeficit
