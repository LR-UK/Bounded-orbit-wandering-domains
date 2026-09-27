/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LocalSingularLimits
import BoundedWanderingDomains.NormalFamilies

/-! # A genuine local derived-singular limit function

Simple connectivity is assumed; injectivity is derived on late intrinsic discs.
The limit is finite and convergence is locally uniform in the Euclidean metric,
since the iteration domain has compact closure.
-/

open Set Function Filter Metric OnePoint NoWanderingDomains
open scoped Topology

namespace BoundedWanderingDomains
open AreaDeficit

theorem local_wandering_orbit_locallyUniform_singular_derivedSet
    {f : ℂ → ℂ} {V : Set ℂ} {z : ℂ} {U : ℕ → Set ℂ}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hz : z ∈ trappedInterior f V)
    (hU : ∀ n, U n = connectedComponentIn (trappedInterior f V) (f^[n] z))
    (hsc : ∀ n, IsSimplyConnected (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∃ a ∈ closure V, (a : OnePoint ℂ) ∈ derivedSet (ComplexDynamics.sphericalSingularValuesOn f V) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun k w => (f^[φ k]) w) (fun _ => a) atTop (U 0) := by
  let : UniformSpace (OnePoint ℂ) := (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    local_wandering_orbit_subsequence_spherical_singular_derivedSet hV hVc hf hn hz hU hsc hdis
  have hfV := hf.mono (subset_closure : V ⊆ closure V)
  have hi := trapped_interior_forward
    (analytic_locally_open hfV (fun x hx => hn x (subset_closure hx)))
  have hzi : ∀ n, f^[n] z ∈ interior (trappedSet f V) := fun n => hi.iterate n hz
  have hUo : ∀ n, IsOpen (U n) := fun n => by rw [hU n]; exact isOpen_interior.connectedComponentIn
  have hzU : z ∈ U 0 := by rw [hU 0]; exact mem_connectedComponentIn hz
  have hUV : ∀ n, U n ⊆ V := fun n => by
    rw [hU n]
    exact (connectedComponentIn_subset _ _).trans (interior_subset.trans (trappedSet_subset f V))
  have hfm : ∀ n, MapsTo f (U n) (U (n+1)) := by
    intro n
    rw [hU n, hU (n+1), iterate_succ_apply']
    exact ((hfV.continuousOn.mono
      (interior_subset.trans (trappedSet_subset f V))).mapsTo_connectedComponentIn
      (hzi n)).mono_right (connectedComponentIn_mono _ hi.image_subset)
  have hit : ∀ n, MapsTo (f^[n]) (U 0) (U n) := by
    intro n
    induction n with
    | zero => exact mapsTo_id _
    | succ n ih => simpa only [iterate_succ'] using (hfm n).comp ih
  have hd : ∀ n, DifferentiableOn ℂ (f^[n]) (U 0) := by
    intro n
    induction n with
    | zero => exact differentiableOn_id
    | succ n ih =>
      simpa only [iterate_succ'] using (hfV.differentiableOn.mono (hUV n)).comp ih (hit n)
  obtain ⟨R, _, hR⟩ := hVc.isBounded.exists_pos_norm_le
  obtain ⟨ψ, g, hψ, hg, _⟩ := bounded_holomorphic_subsequence (hUo 0)
    (fun n => hd (φ n)) (fun n w hw => hR ((f^[φ n]) w) (by
      exact subset_closure (hUV (φ n) (hit (φ n) hw))))
  have hgV : MapsTo g (U 0) (closure V) := by
    intro w hw
    exact isClosed_closure.mem_of_tendsto (hg.tendsto_at hw)
      (Eventually.of_forall (fun n => subset_closure (hUV _ (hit _ hw))))
  have hcoe : UniformContinuousOn ((↑) : ℂ → OnePoint ℂ) (closure V) :=
    hVc.uniformContinuousOn_of_continuous OnePoint.continuous_coe.continuousOn
  have hgs := hcoe.comp_tendstoLocallyUniformlyOn hg hgV
    (Eventually.of_forall (fun n w hw => subset_closure (hUV _ (hit _ hw))))
  have hdisF : Pairwise (fun n m => Disjoint
      ((fun w => ((f^[φ (ψ n)]) w : OnePoint ℂ)) '' U 0)
      ((fun w => ((f^[φ (ψ m)]) w : OnePoint ℂ)) '' U 0)) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro p ⟨v, hv, hvp⟩ ⟨w, hw, hwp⟩
    have he := OnePoint.coe_injective (hvp.trans hwp.symm)
    exact disjoint_left.mp (hdis ((hφ.comp hψ).injective.ne hnm))
      (hit _ hv) (he ▸ hit _ hw)
  have hUc : IsPreconnected (U 0) := by rw [hU 0]; exact isPreconnected_connectedComponentIn
  have hconst := limit_constant_of_disjoint_sphere_images (hUo 0) hUc hzU
    (fun n => (hd (φ (ψ n))).sphereHolomorphicOn (hUo 0)) hgs hdisF
  have hga : (g z : OnePoint ℂ) = a :=
    tendsto_nhds_unique (hgs.tendsto_at hzU) (hlim.comp hψ.tendsto_atTop)
  refine ⟨g z, hgV hzU, hga.symm ▸ ha, φ ∘ ψ, hφ.comp hψ, ?_⟩
  exact hg.congr_right (fun w hw => OnePoint.coe_injective (hconst w hw))

end BoundedWanderingDomains
