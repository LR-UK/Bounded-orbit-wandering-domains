module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.EntireSurfaceModel
public import BoundedWanderingDomains.MeromorphicSingularValues
public import BoundedWanderingDomains.Surfaces.SurfaceDerivedLimits

@[expose] public section

/-! # Entire derived-singular accumulation from the combined surface theorem -/

open Set Function Filter OnePoint MeromorphicDynamics
open scoped Topology Manifold

namespace BoundedWanderingDomains

theorem entire_wandering_derived_singular_limit
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m : ℕ => Disjoint (U n) (U m)))
    {z : ℂ} (hz : z ∈ U 0) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (((f^[φ n]) z : ℂ) : OnePoint ℂ)) atTop (𝓝 a) := by
  have hnonconst : ¬ ∃ c, ∀ z, f z = c := by
    rintro ⟨c, hc⟩
    exact htrans ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  have hwand := surfaceModel_isWanderingComponent_of_fatouComponents
    (fun n => isFatouComponent_of_entire hf (hU n)) hforward hdis
  have hzfinite : (z : OnePoint ℂ) ∈ finiteImage (U 0) := ⟨z, hz, rfl⟩
  have hztrapped := hwand.subset_trapped (surfaceModel f) hzfinite
  have hzpole := poleAvoiding_of_mem_surfaceModel_trapped hztrapped
  obtain ⟨φ, hφ, hescape | ⟨a, ha, hlimit⟩⟩ :=
    SurfaceDynamics.wanderingDerivedSingularLimitClaim (surfaceModel f)
      (surfaceModel_isOpenHolomorphic_of_entire hf hnonconst) (finiteImage (U 0)) hwand
      (z : OnePoint ℂ) hzfinite
  · exfalso
    apply SurfaceDynamics.not_tendsto_infty_of_range_subset_compact
      (fun n => (((f^[φ n]) z : ℂ) : OnePoint ℂ)) isCompact_univ (fun _ => mem_univ _)
    simpa only [surfaceModel_compactifiedIterate_coe_of_poleAvoiding f _ hzpole] using hescape
  · refine ⟨a, ?_, φ, hφ, ?_⟩
    · apply derived_singularValues_subset_of_entire hf
      simpa only [surfaceModel_singularValues] using ha
    · apply OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff.mpr
      change Tendsto (fun n =>
        ((((f^[φ n]) z : ℂ) : OnePoint ℂ) : OnePoint (OnePoint ℂ))) atTop
        (𝓝 (a : OnePoint (OnePoint ℂ)))
      simpa only [Function.comp_apply,
        surfaceModel_compactifiedIterate_coe_of_poleAvoiding f _ hzpole] using hlimit

end BoundedWanderingDomains
