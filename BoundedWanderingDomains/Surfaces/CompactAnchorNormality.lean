/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactPunctureMontel
import BoundedWanderingDomains.Surfaces.CompactOrbitNormal
import BoundedWanderingDomains.Surfaces.LocalMapPunctureBarrier
import BoundedWanderingDomains.Surfaces.SaturationDynamics

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X]

/-- Omitting a fixed hyperbolising finite set makes the partial iterates
normal in the compact ambient surface, including limits at the punctures. -/
theorem mem_omega_of_omits_finite_anchors
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (E : Finset X) (O : TopologicalSpace.Opens X) (hO : ∀ x, x ∈ O ↔ x ∉ E)
    (p : DiscCover O) (W : TopologicalSpace.Opens X)
    (hW : (W : Set X) ⊆ f.trapped)
    (horbitO : ∀ n y, f.orbitOn W hW n y ∈ O) (x : W) : (x : X) ∈ f.omega := by
  obtain ⟨D, hDcenter, hDsub⟩ := exists_coordDisk_center_closedCarrier_subset W.isOpen x.property
  let V : Set X := range D.param
  have hVopen : IsOpen V := D.isOpenEmbedding_param.isOpen_range
  have hxV : (x : X) ∈ V := by
    refine ⟨discZero, ?_⟩
    rw [D.param_zero, hDcenter]
  have hVW : V ⊆ W := by
    rintro y ⟨z, rfl⟩
    exact hDsub (D.param_mem_closedCarrier z)
  have hVT : V ⊆ f.trapped := hVW.trans hW
  refine ⟨V, hVopen, hxV, hVT, ?_⟩
  intro s hs
  let d : unitDisc → W := fun z => ⟨D.param z, hVW ⟨z, rfl⟩⟩
  let F : ℕ → unitDisc → O := fun n z => ⟨f.orbitOn W hW (s n) (d z), horbitO (s n) (d z)⟩
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d :=
    (mdifferentiable_subtypeVal_comp_iff W d).mp D.mdifferentiable_param
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff O (F n)).mp
    exact (f.mdifferentiable_orbitOn hf W hW (s n)).comp hd
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨a, G, ha, hconv⟩ := p.exists_normal_disc_subsequence_finite_complement E O hO F hF
  let e : unitDisc ≃ₜ V := D.isOpenEmbedding_param.toIsEmbedding.toHomeomorph
  let q : V → unitDisc := e.symm
  refine ⟨a, ha, G ∘ q, ?_⟩
  apply (hconv.comp q e.symm.continuous).congr
  intro n y
  have he : D.param (q y) = (y : X) := congrArg Subtype.val (e.apply_symm_apply y)
  rw [f.compactifiedIterate_eq_orbit (s (a n)) ⟨y, hVT y.property⟩]
  change (((F (a n) (q y) : O) : X) : OnePoint X) =
    (f.orbitOn W hW (s (a n)) ⟨(y : X), hVW y.property⟩ : OnePoint X)
  simp only [F]
  congr 2
  exact Subtype.ext he

/-- Every non-normal point is accumulated by the backward orbit of any
fixed finite set whose complement is disc-covered. -/
theorem compl_omega_subset_closure_backward_anchors
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (hsource : f.source = ⊤)
    (E : Finset X) (O : TopologicalSpace.Opens X) (hO : ∀ x, x ∈ O ↔ x ∉ E)
    (p : DiscCover O) {S : Set X} (hES : (E : Set X) ⊆ S)
    (hback : ∀ x : f.source, f.map x ∈ S → (x : X) ∈ S) :
    f.omegaᶜ ⊆ closure S := by
  classical
  have hall : ∀ x : X, x ∈ f.source := by intro x; rw [hsource]; trivial
  have htrap : ∀ x : X, x ∈ f.trapped := by
    intro x
    rw [← f.trappedSet_totalize_eq_trapped]
    exact fun n => hall _
  let W : TopologicalSpace.Opens X := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩
  have hforward : MapsTo f.totalize (W : Set X) W := by
    intro x hx hfx
    exact hx (f.closure_source_backward_invariant hf.1 hback ⟨x, hall x⟩
      (by rwa [f.totalize_eq (hall x)] at hfx))
  have hWtrap : (W : Set X) ⊆ f.trapped := fun x _ => htrap x
  have hWO : ∀ n y, f.orbitOn W hWtrap n y ∈ O := by
    intro n y
    apply (hO _).mpr
    intro he
    have hh := hforward.iterate n y.property
    rw [f.totalize_iterate_orbit n ⟨y, hWtrap y.property⟩] at hh
    exact hh (subset_closure (hES he))
  intro x hx
  by_contra hn
  exact hx (f.mem_omega_of_omits_finite_anchors hf E O hO p W hWtrap hWO ⟨x, hn⟩)

end SurfaceDynamics.LocalMap
