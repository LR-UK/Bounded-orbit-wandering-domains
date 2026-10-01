module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ComponentDomains
public import BoundedWanderingDomains.Surfaces.NoEscapeCompactRange

@[expose] public section

/-! # Ambient components and compactly contained orbits

These constructions make no assumption about how a local map sends different
pieces of its source into ambient components.
-/

open Set Function Filter Topology TopologicalSpace OnePoint
open scoped Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- An ambient connected component, as an open complex submanifold. -/
def ambientComponent (c : ConnectedComponents X) : Opens X := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  exact ⟨ConnectedComponents.mk ⁻¹' {c},
    (isOpen_discrete _).preimage ConnectedComponents.continuous_coe⟩

@[simp] theorem mem_ambientComponent (c : ConnectedComponents X) (x : X) :
    x ∈ ambientComponent c ↔ ConnectedComponents.mk x = c := Iff.rfl

theorem ambientComponent_mk (x : X) :
    (ambientComponent (ConnectedComponents.mk x) : Set X) = connectedComponent x := by
  ext y
  exact ConnectedComponents.coe_eq_coe'

theorem isClosed_ambientComponent (c : ConnectedComponents X) :
    IsClosed (ambientComponent c : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [ambientComponent_mk]
  exact isClosed_connectedComponent

instance ambientComponent_connectedSpace (c : ConnectedComponents X) :
    ConnectedSpace (ambientComponent c) := by
  apply isConnected_iff_connectedSpace.mp
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [ambientComponent_mk]
  exact isConnected_connectedComponent

theorem ambientComponent_pairwise_disjoint :
    Pairwise (fun c d : ConnectedComponents X =>
      Disjoint (ambientComponent c : Set X) (ambientComponent d : Set X)) := by
  intro c d hcd
  exact disjoint_left.mpr (fun _ hc hd => hcd (hc.symm.trans hd))

theorem iUnion_ambientComponent :
    (⋃ c : ConnectedComponents X, (ambientComponent c : Set X)) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk x, rfl⟩

theorem countable_ambient_components [SecondCountableTopology X] :
    Countable (ConnectedComponents X) :=
  ambientComponent_pairwise_disjoint.countable_of_isOpen_disjoint
    (fun c => (ambientComponent c).isOpen)
    (fun c => by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨x, rfl⟩)

/-- Intersect an open domain with one ambient component, in that component's
own manifold structure. -/
def componentPart (c : ConnectedComponents X) (U : Opens X) : Opens (ambientComponent c) :=
  ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩

@[simp] theorem mem_componentPart (c : ConnectedComponents X) (U : Opens X)
    (x : ambientComponent c) : x ∈ componentPart c U ↔ (x : X) ∈ U := Iff.rfl

@[simp] theorem componentPart_top (c : ConnectedComponents X) :
    componentPart c (⊤ : Opens X) = ⊤ := by
  ext x
  rfl

theorem componentPart_mono (c : ConnectedComponents X) : Monotone (componentPart c) :=
  fun _ _ h _ hx => h hx

noncomputable def componentPunctures (c : ConnectedComponents X) (P : Finset X) :
    Finset (ambientComponent c) := by
  classical
  exact P.subtype (fun x => x ∈ ambientComponent c)

@[simp] theorem mem_componentPunctures (c : ConnectedComponents X) (P : Finset X)
    (x : ambientComponent c) : x ∈ componentPunctures c P ↔ (x : X) ∈ P := by
  classical
  simp [componentPunctures]

theorem componentPunctures_mono (c : ConnectedComponents X) :
    Monotone (componentPunctures c) := by
  classical
  exact Finset.subtype_mono

@[simp] theorem componentPart_finitePunctureDomain [T1Space X]
    (c : ConnectedComponents X) (P : Finset X) :
    componentPart c (finitePunctureDomain P) = finitePunctureDomain (componentPunctures c P) := by
  ext x
  simp

theorem finite_components_of_isCompact {K : Set X} (hK : IsCompact K) :
    (ConnectedComponents.mk '' K).Finite := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  exact isCompact_iff_finite.mp (hK.image ConnectedComponents.continuous_coe)

/-- Every compact set is contained in a finite union of full ambient components. -/
theorem exists_finite_component_cover {K : Set X} (hK : IsCompact K) :
    ∃ I : Finset (ConnectedComponents X),
      K ⊆ ⋃ c ∈ I, (ambientComponent c : Set X) := by
  classical
  let hfin := finite_components_of_isCompact hK
  refine ⟨hfin.toFinset, ?_⟩
  intro x hx
  exact mem_iUnion₂.mpr ⟨ConnectedComponents.mk x,
    hfin.mem_toFinset.mpr ⟨x, hx, rfl⟩, rfl⟩

variable [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]

theorem finite_components_of_no_escaping_subsequence (u : ℕ → X)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : OnePoint X)) atTop (𝓝 (∞ : OnePoint X))) :
    (range (fun n => ConnectedComponents.mk (u n))).Finite := by
  obtain ⟨K, hK, hu⟩ := SurfaceDynamics.compact_range_of_no_escaping_subsequence u hno
  apply (finite_components_of_isCompact hK).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨u n, hu n, rfl⟩

theorem escaping_subsequence_of_infinite_components (u : ℕ → X)
    (hinf : (range (fun n => ConnectedComponents.mk (u n))).Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : OnePoint X)) atTop (𝓝 (∞ : OnePoint X)) := by
  by_contra hno
  exact hinf (finite_components_of_no_escaping_subsequence u hno)

end AreaDeficit.Surfaces
