/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LocallyUniformSingularLimits
import BoundedWanderingDomains.SphericalEscape

/-! # Global wandering-domain statements in the paper's formulations

Promote a pointwise subsequential limit to a locally uniform constant limit
on the original wandering component. In particular, infinity is a limit
function on every entire wandering component. All maps remain plane-valued.
-/

open Set Filter Function Metric OnePoint NoWanderingDomains
open scoped Topology

namespace BoundedWanderingDomains

/-- A pointwise subsequential limit on a wandering component is a constant
locally uniform limit after extraction of a further subsequence. -/
theorem wandering_orbit_locallyUniform_of_pointwise_limit
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {a : OnePoint ℂ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[ψ k]) w : OnePoint ℂ)) (fun _ => a) atTop (U 0) := by
  let : UniformSpace (OnePoint ℂ) := (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace
  have hUo : IsOpen (U 0) := by
    obtain ⟨p, _, hp⟩ := hU 0
    rw [hp]
    exact (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  have hUc : IsPreconnected (U 0) := by
    obtain ⟨p, _, hp⟩ := hU 0
    rw [hp]
    exact isPreconnected_connectedComponentIn
  obtain ⟨b, hb, c, hc, hbc⟩ := (infinite_of_mem_nhds z (hUo.mem_nhds hz)).nontrivial
  have hit : ∀ n, MapsTo (f^[n]) (U 0) (U n) := by
    intro n
    induction n with
    | zero => exact mapsTo_id _
    | succ n ih => simpa only [iterate_succ'] using (hforward n).comp ih
  let F : ℕ → ℂ → OnePoint ℂ := fun n w => ((f^[φ (n+1)]) w : OnePoint ℂ)
  have hFc : ∀ n, Continuous (F n) :=
    fun n => OnePoint.continuous_coe.comp (hf.iterate _).continuous
  have hFh : ∀ n, SphereHolomorphicOn (F n) (U 0) :=
    fun n => (hf.iterate _).differentiableOn.sphereHolomorphicOn hUo
  have hN : ∀ w ∈ U 0, IsNormalAt (range F) w := by
    intro w hw
    apply FunctionTheory.isNormalAt_of_two_omitted_values hbc hUo
      (by rintro _ ⟨n, rfl⟩; exact hFh n) ?_ hw
    rintro _ ⟨n, rfl⟩ v hv
    have hn : φ (n+1) ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ n) (hφ.id_le _))
    refine ⟨?_, ?_, OnePoint.coe_ne_infty _⟩
    · intro he
      exact disjoint_left.mp (hdis hn) (OnePoint.coe_injective he ▸ hit _ hv) hb
    · intro he
      exact disjoint_left.mp (hdis hn) (OnePoint.coe_injective he ▸ hit _ hv) hc
  obtain ⟨ψ, g, hψ, hg⟩ := AreaDeficit.spherical_subsequence_of_local_normality hUo hFc hN
  have hFd : Pairwise (fun n m => Disjoint ((F (ψ n)) '' U 0) ((F (ψ m)) '' U 0)) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro p ⟨v, hv, hvp⟩ ⟨w, hw, hwp⟩
    have he : (f^[φ (ψ n+1)]) v = (f^[φ (ψ m+1)]) w :=
      OnePoint.coe_injective (hvp.trans hwp.symm)
    exact disjoint_left.mp (hdis (hφ.injective.ne (by
      have := hψ.injective.ne hnm
      omega))) (hit _ hv) (he ▸ hit _ hw)
  have hconst := AreaDeficit.limit_constant_of_disjoint_sphere_images
    hUo hUc hz (fun n => hFh (ψ n)) hg hFd
  have hseq : StrictMono (fun n => ψ n+1) := fun i j hij => Nat.add_lt_add_right (hψ hij) 1
  have hga : g z = a := tendsto_nhds_unique (hg.tendsto_at hz) (hlim.comp hseq.tendsto_atTop)
  refine ⟨fun n => φ (ψ n+1), hφ.comp hseq, ?_⟩
  have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
      ComplexDynamics.riemannSphereUniformSpace := unique_uniformity_of_compact rfl rfl
  have hres := hg.congr_right (fun w hw => (hconst w hw).trans hga)
  rw [← heq]
  exact hres

/-- Theorem 1: every entire wandering component has infinity as a locally
uniform subsequential limit function. No connectivity or injectivity assumption. -/
theorem wandering_orbit_locallyUniform_infty
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[φ k]) w : OnePoint ℂ))
      (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  have hunbounded : ¬Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z)) := by
    intro hb
    exact (Unconditional.no_bounded_wandering_domains_transcendental_entire
      hf htrans hU hz hforward hb) hdis
  obtain ⟨φ, hφ, hlim⟩ := exists_subsequence_tendsto_infty_of_unbounded
    (fun n : ℕ => (f^[n]) z) hunbounded
  exact wandering_orbit_locallyUniform_of_pointwise_limit hf hU hz hforward hdis hφ hlim

/-- Theorem 3 in its pointwise form. The locally uniform version remains
available as `wandering_orbit_locallyUniform_spherical_singular_derivedSet`. -/
theorem wandering_orbit_pointwise_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto
        (fun k => ((f^[φ k]) z : OnePoint ℂ)) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    wandering_orbit_locallyUniform_spherical_singular_derivedSet hf htrans hU hz hforward hdis
  exact ⟨a, ha, φ, hφ, hlim.tendsto_at hz⟩

end BoundedWanderingDomains
