/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainArea
import BoundedWanderingDomains.Surfaces.ComponentKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Passing finite-model area bounds to the limiting open domain -/

open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem domainDensityRatio_tendsto_finite_punctures (p : DiscCover M)
    {A : Set M} (hA : IsClosed A) (P : ℕ → Finset M) (hP : Monotone P)
    (hPA : ∀ n, (P n : Set M) ⊆ A)
    (hclosure : closure (⋃ n, (P n : Set M)) = A)
    {x : M} (hx : x ∉ A) :
    Tendsto (fun n => p.domainDensityRatio (finitePunctureDomain (P n)) x) atTop
      (𝓝 (p.domainDensityRatio ⟨Aᶜ, hA.isOpen_compl⟩ x)) := by
  let c := chartAt ℂ x
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hxc := mem_chart_source ℂ x
  have hxn : ∀ n, x ∈ finitePunctureDomain (P n) := fun n h => hx (hPA n h)
  have heq : ∀ n, p.domainDensityRatio (finitePunctureDomain (P n)) x =
      p.domainDensity (finitePunctureDomain (P n)) c ⟨x, hxn n⟩ / p.density c x :=
    fun n => p.domainDensityRatio_eq _ hc (hxn n) hxc
  rw [p.domainDensityRatio_eq _ hc hx hxc]
  simp_rw [heq]
  exact (p.domainDensity_tendsto_finite_punctures hA P hP hPA hclosure hx hc hxc).div_const _

/-- Fatou's lemma transfers a uniform finite-puncture bound to the
intrinsic metric on the complement of the limiting closed puncture set. -/
theorem domainArea_le_of_finite_model_bounds (p : DiscCover M)
    {A : Set M} (hA : IsClosed A) (P : ℕ → Finset M) (hP : Monotone P)
    (hPA : ∀ n, (P n : Set M) ⊆ A)
    (hclosure : closure (⋃ n, (P n : Set M)) = A)
    {B : Set M} (hB : MeasurableSet B) (hBA : B ⊆ Aᶜ)
    {H : ℝ≥0∞} (hbound : ∀ n, p.domainArea (finitePunctureDomain (P n)) B ≤ H) :
    p.domainArea ⟨Aᶜ, hA.isOpen_compl⟩ B ≤ H := by
  let w : ℕ → M → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal ((p.domainDensityRatio (finitePunctureDomain (P n)) x)^2)
  have hw : ∀ n, Measurable (w n) := fun n =>
    ((p.domainDensityRatio_measurable _).pow_const 2).ennreal_ofReal
  rw [domainArea, withDensity_apply _ hB]
  calc
    _ = ∫⁻ x in B, liminf (fun n => w n x) atTop ∂p.hyperbolicArea := by
      apply setLIntegral_congr_fun hB
      intro x hx
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((p.domainDensityRatio_tendsto_finite_punctures hA P hP hPA hclosure
          (hBA hx)).pow 2)).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x in B, w n x ∂p.hyperbolicArea) atTop :=
      lintegral_liminf_le' (fun n => (hw n).aemeasurable)
    _ ≤ H := by
      apply liminf_le_of_frequently_le' (Frequently.of_forall ?_)
      intro n
      simpa only [domainArea, withDensity_apply _ hB] using hbound n

/-- Restricting a domain to the component containing the set does not
change its intrinsic area there. -/
theorem domainArea_component (p : DiscCover M) (U : TopologicalSpace.Opens M)
    (x : U) {B : Set M} (hB : MeasurableSet B)
    (hBU : B ⊆ componentDomain U (x : M)) :
    p.domainArea U B = p.domainArea (componentDomain U (x : M)) B := by
  simp only [domainArea, withDensity_apply _ hB]
  apply setLIntegral_congr_fun hB
  intro y hy
  let c := chartAt ℂ y
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) y).1
  have hyc := mem_chart_source ℂ y
  have hyU := componentDomain_le U (x : M) (hBU hy)
  dsimp only
  rw [p.domainDensityRatio_eq U hc hyU hyc,
    p.domainDensityRatio_eq _ hc (hBU hy) hyc]
  congr 3
  let V := componentDomain U (x : M)
  have hVU : componentDomain V y = V := by
    let : ConnectedSpace V := componentDomain_connected x.property
    apply TopologicalSpace.Opens.ext
    exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected
      |>.connectedComponentIn (hBU hy)
  rw [p.domainDensity_eq_on_component U x ⟨y, hyU⟩ (hBU hy) (p.componentCover U x) hc hyc]
  unfold domainDensity
  exact (density_eq_of_domain_eq hVU
    (p.componentCover V ⟨y, hBU hy⟩) (p.componentCover U x)
    ⟨componentPoint V ⟨y, hBU hy⟩⟩ ⟨componentPoint U x⟩ hc
    (mem_componentDomain (hBU hy)) (hBU hy) hyc).symm

end AreaDeficit.Surfaces.DiscCover
