module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteBasisConfiguration
public import BoundedWanderingDomains.Surfaces.SingularEncounters.NormalizedFiniteControl
public import BoundedWanderingDomains.Surfaces.SingularEncounters.PointEncounterAlternative
public import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

/-! # Points without singular encounters lie in finite-control tail configurations -/

open Set Function Filter Topology OnePoint

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]

theorem no_encounters_subset_controlled_tails
    (f : LocalMap X) (hf : Continuous f.map)
    (B : Set (EmbeddedDisc X))
    (hB : TopologicalSpace.IsTopologicalBasis
      ((fun Q : EmbeddedDisc X => (Q.carrier : Set X)) '' B))
    (T : Set X)
    (hT : ∀ Q ∈ B, ∀ a : f.source, (f.componentSingularValues hf Q.carrier a).Finite →
      f.componentSingularValues hf Q.carrier a ⊆ T)
    (L : B → ℕ → Set X)
    (hLD : ∀ i m, L i m ⊆ i.val.carrier)
    (hLcover : ∀ i x, x ∈ i.val.carrier → ∃ m, x ∈ interior (L i m))
    (K : CompactExhaustion X) {A : Set X} (hAtr : A ⊆ f.trapped) :
    {x ∈ A | ¬ f.HasEscapingOrSingularEncounters hf x} ⊆
      ⋃ j : ℕ × ℕ × Finset (B × ℕ) × Finset T,
        f.componentControlTail hf (fun Q : B => Q.val.carrier) L j.2.2.1
          (Subtype.val '' (j.2.2.2 : Set T)) (K j.1) A j.2.1 := by
  classical
  rintro x ⟨hxA, hxno⟩
  let z : f.trapped := ⟨x, hAtr hxA⟩
  have hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (f.orbit (φ n) z : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) := by
    rintro ⟨φ, hφ, hlim⟩
    apply hxno
    refine ⟨z.2, Or.inl ⟨φ, hφ, ?_⟩⟩
    exact hlim.congr' (Eventually.of_forall fun n =>
      (f.compactifiedIterate_eq_orbit (φ n) z).symm)
  obtain ⟨C, hC, hcC⟩ := compact_range_of_no_escaping_subsequence (fun n => f.orbit n z) hno
  obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact hC
  let c : ℕ → f.source := fun n => ⟨f.orbit n z, f.orbit_mem_source n z⟩
  have hfinite : ∀ y ∈ C, f.LocallyFiniteBasisEncounters hf B c y := by
    intro y _
    by_contra hy
    exact hxno ⟨z.2, Or.inr ⟨y, f.encounters_of_not_locally_finite_basis hf B hB z hy⟩⟩
  have hnormalized : ∀ y ∈ C, ∃ i : B, y ∈ i.val.carrier ∧ ∃ (E : Finset T) (N : ℕ),
      ∀ n, N ≤ n → f.map (c n) ∈ i.val.carrier →
        f.componentSingularValues hf i.val.carrier (c n) ⊆ Subtype.val '' (E : Set T) := by
    intro y hy
    obtain ⟨Q, hQB, hyQ, E, N, hcontrol⟩ :=
      LocallyFiniteBasisEncounters.from_pool f hf B T hT c (hfinite y hy)
    exact ⟨⟨Q, hQB⟩, hyQ, E, N, hcontrol⟩
  have hmapC : ∀ n, f.map (c n) ∈ C := by
    intro n
    exact f.orbit_succ n z ▸ hcC (n + 1)
  obtain ⟨J, E, N, hconfig⟩ := f.finite_configuration_of_locally_finite_basis hf
    (fun Q : B => Q.val.carrier) L hLD hLcover T c hC hmapC hnormalized
  apply mem_iUnion.mpr
  refine ⟨(j, N, J, E), hxA, mem_iInter.mpr ?_⟩
  intro n
  change (f.totalize^[n + N]) (z : X) ∈ K j ∩ _
  rw [f.totalize_iterate_orbit (n + N) z]
  exact ⟨hj (hcC (n + N)), hconfig (n + N) (by omega)⟩

end SurfaceDynamics.LocalMap
