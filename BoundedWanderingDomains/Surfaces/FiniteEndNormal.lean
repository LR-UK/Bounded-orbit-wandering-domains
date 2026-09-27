/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactCentreNormal
import BoundedWanderingDomains.Surfaces.DiscComparisonInfinity
import BoundedWanderingDomains.Surfaces.BoundaryEscape
import Mathlib.Topology.Connected.Clopen

/-! # Normal convergence at a finite compactification end

A family of holomorphic discs in a finitely punctured compact surface whose
centres approach one puncture converges to that puncture on smaller discs.
Compact avoidance in the supplied universal disc cover and connectedness
give the result without a new uniformisation or normal-family assumption.
-/

open Set Function Filter Metric TopologicalSpace
open scoped Topology Manifold

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]

/-- Uniform convergence to a deleted end on every smaller covering disc. -/
theorem DiscCover.eventually_maps_radius_into_end_neighborhood
    (E : Finset X) (O : Opens X) (hO : ∀ x, x ∈ O ↔ x ∉ E)
    (p : DiscCover O) (F : ℕ → unitDisc → O)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    {a : X} (ha : a ∈ E)
    (hcentre : Tendsto (fun n => (F n discZero : X)) atTop (𝓝 a))
    {N : Set X} (hN : N ∈ 𝓝 a) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, ∀ z : unitDisc, ‖(z : ℂ)‖ < r → (F n z : X) ∈ N := by
  classical
  obtain ⟨N₀, hN₀N, hN₀open, haN₀⟩ := mem_nhds_iff.mp hN
  let H : Set X := (↑(E.erase a) : Set X)
  have hHclosed : IsClosed H := (E.erase a).finite_toSet.isClosed
  have haH : a ∉ H := by simp [H]
  obtain ⟨V, hVopen, haV, hVN, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure
      (isCompact_singleton : IsCompact ({a} : Set X))
      (hN₀open.sdiff hHclosed) (by simpa using And.intro haN₀ haH)
  have haV' : a ∈ V := haV (by simp)
  have hfrontO : frontier V ⊆ O := by
    intro x hx
    apply (hO x).mpr
    intro hxE
    by_cases hxa : x = a
    · subst x
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hVopen) hx haV'
    · exact (hVN (frontier_subset_closure hx)).2
        (Finset.mem_erase.mpr ⟨hxa, hxE⟩)
  let K : Set O := (Subtype.val : O → X) ⁻¹' frontier V
  have hK : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have heq : (Subtype.val : O → X) '' K = frontier V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hfrontO hx⟩, hx, rfl⟩
    rw [heq]
    exact hVcompact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC, havoid⟩ := p.compact_uniform_avoidance_outside hK hr1
  have hescape : Tendsto (fun n => F n discZero) atTop (cocompact O) :=
    tendsto_cocompact_openSubtype_of_tendsto_boundary O
      (fun haO => (hO a).mp haO ha) _ hcentre
  filter_upwards [hescape.eventually hC.compl_mem_cocompact,
    hcentre.eventually (hVopen.mem_nhds haV')] with n hnC hnV
  let B := ball (0 : ℂ) r
  letI : ConnectedSpace B := Subtype.connectedSpace (isConnected_ball hr)
  let j : B → unitDisc := fun z => ⟨z, mem_ball_zero_iff.mpr
    ((mem_ball_zero_iff.mp z.property).trans hr1)⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let G : B → X := fun z => (F n (j z) : X)
  have hG : Continuous G := continuous_subtype_val.comp ((hF n).continuous.comp hj)
  have hGF : Disjoint (range G) (frontier V) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z, rfl⟩ hx
    exact havoid (F n) (hF n) hnC (j z)
      (le_of_lt (mem_ball_zero_iff.mp z.property)) hx
  have hcover : range G ⊆ V ∪ (closure V)ᶜ := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Or.inl hxV
    · refine Or.inr (fun hxcl => ?_)
      apply Set.disjoint_left.mp hGF hx
      rw [frontier, hVopen.interior_eq]
      exact ⟨hxcl, hxV⟩
  have hsub : range G ⊆ V :=
    (isPreconnected_range hG).subset_left_of_subset_union hVopen
      isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hx hxcl => hxcl (subset_closure hx)))
      hcover ⟨(F n discZero : X), ⟨⟨0, mem_ball_self hr⟩, rfl⟩, hnV⟩
  intro z hz
  apply hN₀N
  apply (hVN (subset_closure (hsub ?_))).1
  exact ⟨⟨z, mem_ball_zero_iff.mpr hz⟩, rfl⟩

end AreaDeficit.Surfaces
