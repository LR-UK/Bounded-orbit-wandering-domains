module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenCompactification
public import BoundedWanderingDomains.Surfaces.LocalMapSubsurface

@[expose] public section

/-! # Normality under a clopen change of ambient manifold -/

open Set Function Filter Topology TopologicalSpace OnePoint
open AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
theorem compactifiedIterate_restrictAmbient (f : LocalMap X)
    (O : Opens X)
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    (n : ℕ) (x : O) :
    OnePoint.map (Subtype.val : O → X)
        ((f.restrictAmbient O hsource hmap).compactifiedIterate n x) =
      f.compactifiedIterate n (x : X) := by
  have he := f.restrictAmbient_iterate_val O hsource hmap n x
  unfold compactifiedIterate
  rw [← he]
  cases (f.restrictAmbient O hsource hmap).iterate n x <;> rfl

theorem isNormalOn_image_restrictAmbient_of_isClosed (f : LocalMap X)
    (O : Opens X) [LocallyCompactSpace O] (hO : IsClosed (O : Set X))
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    {W : Set O} (hW : (f.restrictAmbient O hsource hmap).IsNormalOn W) :
    f.IsNormalOn ((Subtype.val : O → X) '' W) := by
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  let : UniformSpace (OnePoint O) := uniformSpaceOfCompactR1
  let e : W ≃ₜ ((Subtype.val : O → X) '' W) :=
    IsEmbedding.subtypeVal.homeomorphImage W
  intro φ hφ
  obtain ⟨ψ, hψ, G, hG⟩ := hW φ hφ
  let J := OnePoint.map (Subtype.val : O → X)
  have hJ : UniformContinuous J := CompactSpace.uniformContinuous_of_continuous
    (continuous_onePoint_clopen_inclusion O hO)
  refine ⟨ψ, hψ, J ∘ G ∘ e.symm, ?_⟩
  apply (hJ.comp_tendstoLocallyUniformly (hG.comp e.symm e.symm.continuous)).congr
  intro n x
  change J ((f.restrictAmbient O hsource hmap).compactifiedIterate (φ (ψ n))
    ((e.symm x : W) : O)) = f.compactifiedIterate (φ (ψ n)) (x : X)
  exact (f.compactifiedIterate_restrictAmbient O hsource hmap (φ (ψ n)) (e.symm x)).trans
    (congrArg (f.compactifiedIterate (φ (ψ n)))
      (congrArg Subtype.val (e.apply_symm_apply x)))

theorem image_omega_restrictAmbient_of_isClosed (f : LocalMap X)
    (O : Opens X) [LocallyCompactSpace O] (hO : IsClosed (O : Set X))
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O) :
    (Subtype.val : O → X) '' (f.restrictAmbient O hsource hmap).omega ⊆ f.omega := by
  rintro _ ⟨x, ⟨W, hW, hx, hWt, hWn⟩, rfl⟩
  refine ⟨Subtype.val '' W, O.isOpen.isOpenMap_subtype_val W hW,
    ⟨x, hx, rfl⟩, ?_, f.isNormalOn_image_restrictAmbient_of_isClosed O hO hsource hmap hWn⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (f.mem_restrictAmbient_trapped_iff O hsource hmap y).mp (hWt hy)

omit [LocallyCompactSpace X] in
theorem clopenCollapse_compactifiedIterate_restrictAmbient (f : LocalMap X)
    (O : Opens X) (hO : IsClosed (O : Set X))
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    (n : ℕ) (x : O) :
    clopenCompactificationRetraction O hO (f.compactifiedIterate n (x : X)) =
      (f.restrictAmbient O hsource hmap).compactifiedIterate n x := by
  rw [← f.compactifiedIterate_restrictAmbient O hsource hmap n x]
  generalize (f.restrictAmbient O hsource hmap).compactifiedIterate n x = y
  induction y using OnePoint.rec <;> simp

theorem isNormalOn_restrictAmbient_preimage_of_isClosed (f : LocalMap X)
    (O : Opens X) [LocallyCompactSpace O] (hO : IsClosed (O : Set X))
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O)
    {W : Set X} (hW : f.IsNormalOn W) :
    (f.restrictAmbient O hsource hmap).IsNormalOn ((Subtype.val : O → X) ⁻¹' W) := by
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  let : UniformSpace (OnePoint O) := uniformSpaceOfCompactR1
  let j : ((Subtype.val : O → X) ⁻¹' W) → W := fun x => ⟨(x : O), x.property⟩
  have hj : Continuous j := by fun_prop
  let J := clopenCompactificationRetraction O hO
  have hJ : UniformContinuous J := CompactSpace.uniformContinuous_of_continuous J.continuous
  intro φ hφ
  obtain ⟨ψ, hψ, G, hG⟩ := hW φ hφ
  refine ⟨ψ, hψ, J ∘ G ∘ j, ?_⟩
  apply (hJ.comp_tendstoLocallyUniformly (hG.comp j hj)).congr
  intro n x
  exact f.clopenCollapse_compactifiedIterate_restrictAmbient O hO hsource hmap (φ (ψ n)) x

theorem omega_restrictAmbient_eq_preimage_of_isClosed (f : LocalMap X)
    (O : Opens X) [LocallyCompactSpace O] (hO : IsClosed (O : Set X))
    (hsource : (f.source : Set X) ⊆ O) (hmap : ∀ x : f.source, f.map x ∈ O) :
    (f.restrictAmbient O hsource hmap).omega = (Subtype.val : O → X) ⁻¹' f.omega := by
  apply Subset.antisymm
  · intro x hx
    exact f.image_omega_restrictAmbient_of_isClosed O hO hsource hmap ⟨x, hx, rfl⟩
  · rintro x ⟨W, hW, hx, hWt, hWn⟩
    refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hx, ?_,
      f.isNormalOn_restrictAmbient_preimage_of_isClosed O hO hsource hmap hWn⟩
    intro y hy
    exact (f.mem_restrictAmbient_trapped_iff O hsource hmap y).mpr (hWt hy)

end SurfaceDynamics.LocalMap
