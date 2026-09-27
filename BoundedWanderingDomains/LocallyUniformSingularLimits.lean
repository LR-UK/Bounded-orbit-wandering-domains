/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SingularLimits
import BoundedWanderingDomains.NormalFamilyOnDomain

/-! # Locally uniform derived singular limits on the entire wandering component -/

open Set Filter Function Metric OnePoint NoWanderingDomains
open scoped Topology

namespace BoundedWanderingDomains

theorem wandering_orbit_locallyUniform_spherical_singular_derivedSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ derivedSet (ComplexDynamics.sphericalSingularValues f), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoLocallyUniformlyOn
        (fun k w => ((f^[φ k]) w : OnePoint ℂ)) (fun _ => a) atTop (U 0) := by
  let : UniformSpace (OnePoint ℂ) := (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    wandering_orbit_subsequence_spherical_singular_derivedSet hf htrans hU hz hforward hdis
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
  refine ⟨a, ha, fun n => φ (ψ n+1), hφ.comp hseq, ?_⟩
  have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
      ComplexDynamics.riemannSphereUniformSpace := unique_uniformity_of_compact rfl rfl
  have hres := hg.congr_right (fun w hw => (hconst w hw).trans hga)
  rw [← heq]
  exact hres

/-- Non-escape in class B follows from derived singular accumulation. -/
theorem no_escaping_wandering_orbit_of_classB
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hB : ComplexDynamics.MemClassB f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ¬ Tendsto (fun n => ((f^[n]) z : OnePoint ℂ)) atTop (𝓝 ∞) :=
  not_tendsto_infty_of_derived_singular_subsequence hB
    (wandering_orbit_subsequence_singularDerivedSet hf htrans hU hz hforward hdis)

end BoundedWanderingDomains
