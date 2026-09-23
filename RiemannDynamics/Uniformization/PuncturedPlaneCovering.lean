/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import RiemannDynamics.Uniformization.PuncturedPlaneBridge
import RiemannDynamics.Uniformization.Trichotomy
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric Function TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

/-- A finitely punctured plane with at least two punctures has a
holomorphic universal covering by the unit disc. No metric or area
hypothesis is used. -/
theorem exists_disc_covering_finitely_punctured_plane
    (P : Finset ℂ) (hP : 2 ≤ P.card) :
    ∃ p : ℂ → ℂ, AreaDeficit.IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ) := by
  let U : Opens ℂ := ⟨(↑P : Set ℂ)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩
  have hc : IsPathConnected (U : Set ℂ) :=
    P.finite_toSet.countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  let : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hc
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  let x₀ : U := ⟨z₀, hz₀⟩
  let : T2Space (PathCover x₀) := t2space_pathCover x₀
  let : SimplyConnectedSpace (PathCover x₀) := simplyConnectedSpace_pathCover x₀
  let : SecondCountableTopology (PathCover x₀) := secondCountableTopology_pathCover x₀
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hP
  have hmodels := uniformization_trichotomy (PathCover x₀)
  exact exists_disc_covering_of_models U x₀ P.finite_toSet.infinite_compl hab
    (fun h => h ha) (fun h => h hb) hmodels

#print axioms exists_disc_covering_finitely_punctured_plane

end RiemannDynamics
