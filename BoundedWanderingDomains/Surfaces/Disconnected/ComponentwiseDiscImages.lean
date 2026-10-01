module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseNormality
public import BoundedWanderingDomains.Surfaces.WanderingDiscShrink

@[expose] public section

/-! # Compact control and shrinking with changing ambient components -/

open Set Function Filter Topology
open scoped Manifold

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
  [LocallyCompactSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
theorem compact_disc_images (p : ComponentwiseDiscCover X)
    {K : Set X} (hK : IsCompact K) {r : ℝ} (hr : r < 1) :
    ∃ C : Set X, IsCompact C ∧
      ∀ g : unitDisc → X, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
        g discZero ∈ K → ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → g z ∈ C := by
  classical
  obtain ⟨I, hI⟩ := exists_finite_component_cover hK
  have hKc : ∀ c : ↥I, IsCompact (Subtype.val ⁻¹' K : Set (ambientComponent c.val)) :=
    fun c => (isClosed_ambientComponent c.val).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  choose C hC hcontrol using fun c : ↥I => (p.cover c.val).compact_disc_images (hKc c) hr
  refine ⟨⋃ c : ↥I, Subtype.val '' C c,
    isCompact_iUnion (fun c => (hC c).image continuous_subtype_val), ?_⟩
  intro g hg hgK z hz
  obtain ⟨c, hc, hgc⟩ := mem_iUnion₂.mp (hI hgK)
  let i : ↥I := ⟨c, hc⟩
  have hgcAll : ∀ w, g w ∈ ambientComponent c :=
    fun w => disc_mapsTo_component hg.continuous c hgc (mem_univ w)
  let H : unitDisc → ambientComponent c := fun w => ⟨g w, hgcAll w⟩
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := by
    apply (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) H).mp
    exact hg
  exact mem_iUnion.mpr ⟨i, H z, hcontrol i H hH hgK z hz, rfl⟩

omit [LocallyCompactSpace X] in
theorem disjoint_disc_images_eventually_in_cover
    (p : ComponentwiseDiscCover X) {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {ι : Sort*} (V : ι → Set X) (hV : ∀ i, IsOpen (V i))
    (hcover : K ⊆ ⋃ i, V i) {r : ℝ} (hr1 : r < 1) :
    ∀ᶠ n in atTop, ∃ i, ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → F n z ∈ V i := by
  classical
  by_contra hno
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hno)
  obtain ⟨ψ, c, hψ, hFc⟩ := exists_disc_subsequence_in_component hK
    (fun n => F (φ n)) (fun n => (hF (φ n)).continuous) (fun n => hcentre (φ n))
  let θ := φ ∘ ψ
  have hθ : StrictMono θ := hφ.comp hψ
  let H : ℕ → unitDisc → ambientComponent c := fun n z => ⟨F (θ n) z, hFc n z⟩
  have hH : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff (ambientComponent c) (H n)).mp
    exact hF (θ n)
  have hHdis : Pairwise (fun n m => Disjoint (range (H n)) (range (H m))) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro y ⟨z, hz⟩ ⟨w, hw⟩
    have he : F (θ n) z = F (θ m) w := congrArg Subtype.val (hz.trans hw.symm)
    exact disjoint_left.mp (hdis (hθ.injective.ne hnm)) (mem_range_self z)
      (he.symm ▸ mem_range_self w)
  have hKc : IsCompact (Subtype.val ⁻¹' K : Set (ambientComponent c)) :=
    (isClosed_ambientComponent c).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hevent := (p.cover c).disjoint_disc_images_eventually_in_cover hKc H hH
    (fun n => hcentre (θ n)) hHdis (fun i => Subtype.val ⁻¹' V i)
    (fun i => (hV i).preimage continuous_subtype_val) (by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨i, hi⟩) hr1
  obtain ⟨n, hn⟩ := hevent.exists
  exact hbad (ψ n) hn

end AreaDeficit.Surfaces.ComponentwiseDiscCover
