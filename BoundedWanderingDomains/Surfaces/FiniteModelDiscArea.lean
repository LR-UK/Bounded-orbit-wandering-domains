module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CoveringDiscArea
public import BoundedWanderingDomains.Surfaces.DomainKernelArea
public import BoundedWanderingDomains.Surfaces.DomainAreaSubtype

@[expose] public section

/-! # Finite-model bounds control embedded covering discs of the limit -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem disc_area_le_of_finite_model_bounds (p : DiscCover M)
    {A : Set M} (hA : IsClosed A) (P : ℕ → Finset M) (hP : Monotone P)
    (hPA : ∀ n, (P n : Set M) ⊆ A)
    (hclosure : closure (⋃ n, (P n : Set M)) = A)
    (U : TopologicalSpace.Opens M) (q : DiscCover U)
    (hcentre : ((q.projection discZero : U) : M) ∉ A)
    (hcomp : (U : Set M) = connectedComponentIn Aᶜ (q.projection discZero : M))
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {r : ℝ} (hr1 : r < 1)
    (hchart : ∀ z : unitDisc, ‖(z : ℂ)‖ < r → (q.projection z : M) ∈ c.source)
    (hinj : InjOn q.projection {z : unitDisc | ‖(z : ℂ)‖ < r})
    {H : ℝ≥0∞}
    (hbound : ∀ n, p.domainArea (finitePunctureDomain (P n))
      ((fun z => (q.projection z : M)) '' {z : unitDisc | ‖(z : ℂ)‖ < r}) ≤ H) :
    (∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal ((discDensity z)^2)) ≤ H := by
  let O : TopologicalSpace.Opens M := ⟨Aᶜ, hA.isOpen_compl⟩
  let x : O := ⟨q.projection discZero, hcentre⟩
  have hUO : U = componentDomain O (x : M) := TopologicalSpace.Opens.ext hcomp
  let : ConnectedSpace U := hUO ▸ componentDomain_connected hcentre
  let hUN : Nonempty U := ⟨q.projection discZero⟩
  let D := {z : unitDisc | ‖(z : ℂ)‖ < r}
  let B := (fun z => (q.projection z : M)) '' D
  have hD : IsOpen D := isOpen_lt continuous_subtype_val.norm continuous_const
  have hBo : IsOpen B :=
    (U.isOpen.isOpenMap_subtype_val.comp q.isOpenMap) _ hD
  have hBU : B ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact (q.projection z).property
  have hBc : B ⊆ c.source := by
    rintro y ⟨z, hz, rfl⟩
    exact hchart z hz
  have hBO : B ⊆ O := by
    rw [hUO] at hBU
    exact hBU.trans (componentDomain_le O x)
  have hlimit : p.domainArea O B ≤ H :=
    p.domainArea_le_of_finite_model_bounds hA P hP hPA hclosure hBo.measurableSet hBO hbound
  have hcomponent : p.domainArea O B = p.domainArea U B := by
    rw [hUO]
    exact p.domainArea_component O x hBo.measurableSet (hUO ▸ hBU)
  rw [hcomponent] at hlimit
  rw [p.domainArea_eq_hyperbolicArea_preimage_of_subset_chart U q hUN hc
    hBo.measurableSet hBU hBc] at hlimit
  have hpre : (Subtype.val : U → M) ⁻¹' B = q.projection '' D := by
    ext y
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨z, hz, Subtype.ext he⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [hpre] at hlimit
  have hform := q.hyperbolicArea_image_radius (mdifferentiableOn_subtypeRestr hUN hc)
    hr1 (fun z hz => by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
        using hchart z hz) hinj
  rw [hform] at hlimit
  exact hlimit

end AreaDeficit.Surfaces.DiscCover
