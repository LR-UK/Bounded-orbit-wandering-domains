/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceSingularCovering
import BoundedWanderingDomains.Surfaces.ChartPartitionCoveringTransport
import BoundedWanderingDomains.Surfaces.CompactFiniteRemoval
import BoundedWanderingDomains.Surfaces.SaturationDynamics

/-! # Exact area transport over regular values of the actual local map -/

open Set Function MeasureTheory Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

def regularCoverDomain (f : LocalMap X) (Y : TopologicalSpace.Opens X)
    (hf : Continuous f.map) : TopologicalSpace.Opens X :=
  ⟨Subtype.val '' (f.map ⁻¹' (Y : Set X)),
    f.source.isOpen.isOpenMap_subtype_val _ (Y.isOpen.preimage hf)⟩

theorem exists_regular_domain_cover (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (Y : TopologicalSpace.Opens X) (hY : (Y : Set X) ⊆ f.singularValuesᶜ) :
    ∃ F : f.regularCoverDomain Y hf.2.continuous → Y,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ IsCoveringMap F ∧
      (fun x : f.regularCoverDomain Y hf.2.continuous => f.totalize x) =
        (fun x => (F x : X)) := by
  let W : TopologicalSpace.Opens f.source := ⟨f.map ⁻¹' (Y : Set X), Y.isOpen.preimage hf.2.continuous⟩
  let T := f.regularCoverDomain Y hf.2.continuous
  let e : W ≃ₜ T := IsEmbedding.subtypeVal.homeomorphImage (W : Set f.source)
  let G : W → Y := fun x => ⟨f.map x, x.property⟩
  let F : T → Y := G ∘ e.symm
  have hcov : IsCoveringMap F :=
    ((f.isCoveringMapOn_compl_singularValues.mono hY).isCoveringMap_restrictPreimage).comp_homeomorph e.symm
  have heq : (Subtype.val : f.source → X) ∘ (Subtype.val : W → f.source) ∘ e.symm =
      (Subtype.val : T → X) := by
    funext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  have hed : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm := by
    apply (mdifferentiable_subtypeVal_comp_iff W e.symm).mp
    apply (mdifferentiable_subtypeVal_comp_iff f.source _).mp
    rw [heq]
    exact mdifferentiable_subtype_val T
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    apply (mdifferentiable_subtypeVal_comp_iff Y G).mp
    exact hf.2.comp (mdifferentiable_subtype_val W)
  refine ⟨F, hfd.comp hed, hcov, ?_⟩
  funext x
  have hxval : (((e.symm x : W) : f.source) : X) = (x : X) := congrFun heq x
  have hxs : (x : X) ∈ f.source := hxval ▸ ((e.symm x : W) : f.source).property
  rw [f.totalize_eq hxs]
  change f.map ⟨(x : X), hxs⟩ = f.map (e.symm x : f.source)
  exact congrArg f.map (Subtype.ext hxval.symm)

theorem exists_uniform_singular_area_advance
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (E : Finset X) {H L : Set X} (hH : IsClosed H) (hL : IsCompact L)
    (hLH : Disjoint L H) (hS : f.singularValues ⊆ H ∪ (E : Set X)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ P : Finset X,
      (∀ x : f.source, (x : X) ∈ P → f.map x ∈ P) →
      ∀ W : Set X, MeasurableSet W → W ⊆ f.source → InjOn f.totalize W →
      f.totalize '' W ⊆ L →
      (∀ x ∈ W, f.totalize x ∉ P ∧ f.totalize x ∉ E) →
      p.domainArea (finitePunctureDomain P) W ≤
        p.domainArea (finitePunctureDomain P) (f.totalize '' W) + C := by
  obtain ⟨C, hC, hgain⟩ := p.compact_finite_remote_removal_gain E hH hL hLH
  refine ⟨C, hC, ?_⟩
  intro P hforward W hW hWs hinj himageL havoid
  let U := finitePunctureDomain P
  let Y := finiteRemovalDomain U E ⊓ (⟨Hᶜ, hH.isOpen_compl⟩ : TopologicalSpace.Opens X)
  let T := f.regularCoverDomain Y hf.2.continuous
  have hY : (Y : Set X) ⊆ f.singularValuesᶜ := by
    intro x hx hs
    rcases hS hs with hh | he
    · exact hx.2 hh
    · exact hx.1.2 he
  obtain ⟨F, hF, hcov, hFeq⟩ := f.exists_regular_domain_cover hf Y hY
  have hTU : T ≤ U := by
    rintro x ⟨w, hw, rfl⟩ hxP
    exact hw.1.1 (hforward w hxP)
  have hWT : W ⊆ T := by
    intro x hx
    refine ⟨⟨x, hWs hx⟩, ?_, rfl⟩
    change f.map ⟨x, hWs hx⟩ ∈ Y
    rw [← f.totalize_eq (hWs hx)]
    exact ⟨havoid x hx, fun hh => disjoint_left.mp hLH (himageL ⟨x, hx, rfl⟩) hh⟩
  have him : MeasurableSet (f.totalize '' W) := by
    letI : PolishSpace X := surfacePolishSpace
    exact hW.image_of_continuousOn_injOn ((f.continuousOn_totalize hf.2.continuous).mono hWs) hinj
  calc
    p.domainArea U W ≤ p.domainArea T W := p.domainArea_mono_on hTU hW hWT
    _ = p.domainArea Y (f.totalize '' W) :=
      p.domainArea_eq_image_of_openDomain_covering T Y F hF hcov hFeq
        (f.measurable_totalize hf.2.continuous) hW hWT hinj
    _ ≤ p.domainArea U (f.totalize '' W) + p.domainAreaGain U Y (f.totalize '' W) :=
      p.domainArea_le_add_gain U Y him
    _ ≤ p.domainArea U (f.totalize '' W) + C :=
      add_le_add le_rfl ((measure_mono himageL).trans (hgain U))

end SurfaceDynamics.LocalMap
