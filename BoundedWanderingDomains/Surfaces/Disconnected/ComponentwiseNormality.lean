module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCover
public import BoundedWanderingDomains.Surfaces.CompactCentreNormal

@[expose] public section

/-! # Compact-centre normality without ambient connectedness -/

open Set Function Filter Topology
open scoped Manifold

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
  [LocallyCompactSpace X]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] in
/-- A disc with centre in an ambient component stays in that component. This
concerns one holomorphic disc, not an entire component of a local map's source. -/
theorem disc_mapsTo_component {F : unitDisc → X}
    (hF : Continuous F) (c : ConnectedComponents X)
    (hc : F discZero ∈ ambientComponent c) : MapsTo F univ (ambientComponent c) := by
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  have hr : IsPreconnected (range F) := isPreconnected_range hF
  have hsub := hr.subset_connectedComponent (mem_range_self discZero)
  have he : c = ConnectedComponents.mk (F discZero) := hc.symm
  rw [he, ambientComponent_mk]
  exact fun z _ => hsub (mem_range_self z)

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] in
/-- Passing to a subsequence fixes the ambient component of compact centre
values. All points of each disc then lie in that same component. -/
theorem exists_disc_subsequence_in_component
    {K : Set X} (hK : IsCompact K) (F : ℕ → unitDisc → X)
    (hF : ∀ n, Continuous (F n)) (hcentre : ∀ n, F n discZero ∈ K) :
    ∃ (φ : ℕ → ℕ) (c : ConnectedComponents X), StrictMono φ ∧
      ∀ n z, F (φ n) z ∈ ambientComponent c := by
  have hfreq : ∃ᶠ n in atTop, ∃ c ∈ ConnectedComponents.mk '' K,
      F n discZero ∈ ambientComponent c :=
    (Eventually.of_forall (fun n => ⟨ConnectedComponents.mk (F n discZero),
      ⟨F n discZero, hcentre n, rfl⟩, rfl⟩)).frequently
  obtain ⟨c, _, hc⟩ := (finite_components_of_isCompact hK).frequently_exists.mp hfreq
  obtain ⟨φ, hφ, hφc⟩ := extraction_of_frequently_atTop hc
  refine ⟨φ, c, hφ, ?_⟩
  intro n z
  exact disc_mapsTo_component (hF (φ n)) c (hφc n) (mem_univ z)

omit [T2Space X] [LocallyCompactSpace X] in
theorem exists_normal_disc_subsequence_comp (p : ComponentwiseDiscCover X)
    {Y : Type*} [UniformSpace Y] (j : X → Y) (hj : Continuous j)
    {K : Set X} (hK : IsCompact K) (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K) :
    ∃ (φ : ℕ → ℕ) (G : unitDisc → Y), StrictMono φ ∧
      TendstoLocallyUniformly (fun n z => j (F (φ n) z)) G atTop := by
  obtain ⟨φ, c, hφ, hFc⟩ :=
    exists_disc_subsequence_in_component hK F (fun n => (hF n).continuous) hcentre
  let H : ℕ → unitDisc → ambientComponent c := fun n z => ⟨F (φ n) z, hFc n z⟩
  have hH : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) (H n)).mp
    exact hF (φ n)
  have hKc : IsCompact (Subtype.val ⁻¹' K : Set (ambientComponent c)) :=
    (isClosed_ambientComponent c).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  obtain ⟨ψ, G, hψ, hlim⟩ := (p.cover c).exists_normal_disc_subsequence_comp
    (fun x => j (x : X)) (hj.comp continuous_subtype_val)
    hKc H hH (fun n => hcentre (φ n))
  exact ⟨φ ∘ ψ, G, hφ.comp hψ, hlim⟩

theorem exists_normal_disc_subsequence (p : ComponentwiseDiscCover X)
    {K : Set X} (hK : IsCompact K) (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K) :
    letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
    ∃ (φ : ℕ → ℕ) (G : unitDisc → OnePoint X), StrictMono φ ∧
      TendstoLocallyUniformly (fun n z => (F (φ n) z : OnePoint X)) G atTop := by
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  exact p.exists_normal_disc_subsequence_comp (fun x => (x : OnePoint X))
    OnePoint.continuous_coe hK F hF hcentre

theorem exists_normal_disc_subsequence_ambient
    (O : TopologicalSpace.Opens X) (p : ComponentwiseDiscCover O)
    {K : Set O} (hK : IsCompact K) (F : ℕ → unitDisc → O)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K) :
    letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
    ∃ (φ : ℕ → ℕ) (G : unitDisc → OnePoint X), StrictMono φ ∧
      TendstoLocallyUniformly (fun n z => ((F (φ n) z : X) : OnePoint X)) G atTop := by
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  exact p.exists_normal_disc_subsequence_comp (fun x => ((x : X) : OnePoint X))
    (OnePoint.continuous_coe.comp continuous_subtype_val) hK F hF hcentre

theorem exists_normal_disc_subsequence_compact_range
    (O : TopologicalSpace.Opens X) (p : ComponentwiseDiscCover O)
    {K : Set O} (hK : IsCompact K) (F : ℕ → unitDisc → O)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hrange : ∀ n z, F n z ∈ K) :
    letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
    ∃ (φ : ℕ → ℕ) (G : unitDisc → OnePoint X), StrictMono φ ∧
      TendstoLocallyUniformly (fun n z => ((F (φ n) z : X) : OnePoint X)) G atTop :=
  p.exists_normal_disc_subsequence_ambient O hK F hF (fun n => hrange n discZero)

end AreaDeficit.Surfaces.ComponentwiseDiscCover
