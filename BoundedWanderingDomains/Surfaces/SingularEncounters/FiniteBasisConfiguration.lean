module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.MeasurableConfigurations
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-! # A compact controlled orbit determines one finite configuration -/

open Set Function Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem finite_configuration_of_locally_finite_basis
    (f : LocalMap X) (hf : Continuous f.map) {ι : Type*}
    (D : ι → TopologicalSpace.Opens X) (L : ι → ℕ → Set X)
    (hLD : ∀ i m, L i m ⊆ D i)
    (hLcover : ∀ i x, x ∈ D i → ∃ m, x ∈ interior (L i m))
    (T : Set X) (c : ℕ → f.source) {K : Set X} (hK : IsCompact K)
    (hcK : ∀ n, f.map (c n) ∈ K)
    (hfinite : ∀ x ∈ K, ∃ i, x ∈ D i ∧ ∃ (E : Finset T) (N : ℕ),
      ∀ n, N ≤ n → f.map (c n) ∈ D i →
        f.componentSingularValues hf (D i) (c n) ⊆ Subtype.val '' (E : Set T)) :
    ∃ (J : Finset (ι × ℕ)) (E : Finset T) (N : ℕ), ∀ n, N ≤ n →
      (c n : X) ∈ f.componentControlRegion hf D L J (Subtype.val '' (E : Set T)) := by
  classical
  choose i hi E N hcontrol using fun x : K => hfinite x x.2
  choose m hm using fun x : K => hLcover (i x) x (hi x)
  have hcover : K ⊆ ⋃ x : K, interior (L (i x) (m x)) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hm ⟨x, hx⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => interior (L (i x) (m x)))
    (fun _ => isOpen_interior) hcover
  let J : Finset (ι × ℕ) := I.image (fun x => (i x, m x))
  let F : Finset T := I.biUnion E
  refine ⟨J, F, I.sup N, ?_⟩
  intro n hn
  obtain ⟨x, hxI, hfxL⟩ := mem_iUnion₂.mp (hI (hcK n))
  have hxJ : (i x, m x) ∈ J := Finset.mem_image.mpr ⟨x, hxI, rfl⟩
  have hfxD : f.map (c n) ∈ D (i x) := hLD (i x) (m x) (interior_subset hfxL)
  have hobs : f.componentSingularValues hf (D (i x)) (c n) ⊆
      Subtype.val '' (F : Set T) := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hcontrol x n ((Finset.le_sup hxI).trans hn) hfxD hs
    exact ⟨t, Finset.mem_biUnion.mpr ⟨x, hxI, ht⟩, rfl⟩
  apply mem_iUnion.mpr
  refine ⟨⟨(i x, m x), hxJ⟩, ?_, ?_⟩
  · exact (f.mem_finiteObstructionSource_iff hf _ _ (c n)).mpr ⟨hfxD, hobs⟩
  · change f.totalize (c n) ∈ L (i x) (m x)
    rw [f.totalize_eq (c n).2]
    exact interior_subset hfxL

end SurfaceDynamics.LocalMap
