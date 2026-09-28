/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.MeromorphicNormalityBridge
import BoundedWanderingDomains.BackwardOrbitMontel
import BoundedWanderingDomains.NormalFamilyOnDomain
import BoundedWanderingDomains.SphericalEscape
import BoundedWanderingDomains.SphericalShrinking
import BoundedWanderingDomains.Surfaces.Statements
import FunctionTheory.Analytic.FiniteOrbitLocalDegree

/-! # Meromorphic escape from the surface theorem -/

open Set Function Filter OnePoint Metric NoWanderingDomains
open scoped Topology Manifold

namespace MeromorphicDynamics

/-- The compact-orbit surface theorem makes every marked orbit in a
meromorphic wandering component unbounded in the plane. -/
theorem wandering_orbit_unbounded_of_surface_theorem
    (hsurface : SurfaceDynamics.NoCompactWanderingOrbitClaim
      (X := OnePoint ℂ))
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ)
    (htrans : ¬ FunctionTheory.IsRationalMeromorphic f)
    {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise fun n m => Disjoint (U n) (U m)) :
    ¬ Bornology.IsBounded (range fun n : ℕ => (f^[n]) z) := by
  intro hb
  have hwandering := surfaceModel_isWanderingComponent_of_fatouComponents
    hU hforward hdis
  have hescape := hsurface (surfaceModel f)
    (surfaceModel_isOpenHolomorphic hf htrans) (finiteImage (U 0))
    hwandering (z : OnePoint ℂ) ⟨z, hz, rfl⟩
  let K0 : Set ℂ := closure (range fun n : ℕ => (f^[n]) z)
  let K : Set (OnePoint ℂ) := finiteImage K0
  have hK0 : IsCompact K0 := hb.isCompact_closure
  have hK : IsCompact K := by
    simpa only [K, finiteImage] using hK0.image OnePoint.continuous_coe
  have hKsource : K ⊆ (surfaceModel f).source := by
    rintro _ ⟨w, _, rfl⟩
    exact coe_mem_finiteSphereOpens w
  obtain ⟨n, hn⟩ := hescape K hK hKsource
  have hzpole : z ∈ poleAvoidingSet f :=
    (fatouSet_subset_poleAvoidingSet f)
      (by
        obtain ⟨a, ha, hUa⟩ := hU 0
        rw [hUa] at hz
        exact connectedComponentIn_subset _ _ hz)
  apply hn
  rw [surfaceModel_compactifiedIterate_coe_of_poleAvoiding f n hzpole]
  refine ⟨((f^[n]) z : OnePoint ℂ), ?_, rfl⟩
  exact ⟨(f^[n]) z, subset_closure (mem_range_self n), rfl⟩

/-- On a meromorphic wandering component, an unbounded marked orbit yields
a further subsequence converging locally uniformly to infinity. -/
theorem wandering_orbit_locallyUniform_infty_of_unbounded
    {f : ℂ → ℂ} {U : ℕ → Set ℂ} {z : ℂ}
    (hU : ∀ n, IsFatouComponent f (U n))
    (hz : z ∈ U 0) (hforward : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise fun n m => Disjoint (U n) (U m))
    (hunbounded : ¬ Bornology.IsBounded (range fun n : ℕ => (f^[n]) z)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ TendstoLocallyUniformlyOn
      (fun k w => ((f^[σ k]) w : OnePoint ℂ))
      (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  classical
  let _ : UniformSpace (OnePoint ℂ) :=
    (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace
  obtain ⟨σ, hσ, hlim⟩ :=
    BoundedWanderingDomains.exists_subsequence_tendsto_infty_of_unbounded
      (fun n : ℕ => (f^[n]) z) hunbounded
  obtain ⟨a, ha, hU0⟩ := hU 0
  have hUo : IsOpen (U 0) := by
    rw [hU0]
    exact (isOpen_fatouSet f).connectedComponentIn
  have hUc : IsPreconnected (U 0) := by
    rw [hU0]
    exact isPreconnected_connectedComponentIn
  have hUfatou : U 0 ⊆ fatouSet f := by
    rw [hU0]
    exact connectedComponentIn_subset _ _
  have hUpole : U 0 ⊆ poleAvoidingSet f :=
    hUfatou.trans (fatouSet_subset_poleAvoidingSet f)
  let : LocallyCompactSpace (U 0) := hUo.locallyCompactSpace
  let F : ℕ → (U 0) → OnePoint ℂ := fun n w => ((f^[σ n]) (w : ℂ) : OnePoint ℂ)
  have hFc : ∀ n, Continuous (F n) := by
    intro n
    rw [continuous_iff_continuousAt]
    intro w
    exact OnePoint.continuous_coe.continuousAt.comp
      ((FunctionTheory.analyticAt_iterate_of_finite_orbit
        (fun j _ => hUpole w.property j)).continuousAt.comp
          continuous_subtype_val.continuousAt)
  have hN : ∀ w : U 0, IsNormalAt (range F) w := by
    intro w
    obtain ⟨W, hWo, hwW, hWp, hWN⟩ := hUfatou w.property
    have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
        ComplexDynamics.riemannSphereUniformSpace :=
      unique_uniformity_of_compact rfl rfl
    rw [← heq] at hWN
    refine ⟨((↑) : U 0 → ℂ) ⁻¹' W, ?_, ?_⟩
    · exact (hWo.preimage continuous_subtype_val).mem_nhds hwW
    · exact BoundedWanderingDomains.normal_family_restrict_subsequence
        (BoundedWanderingDomains.normal_family_of_normalSequenceOn hWN) σ
  obtain ⟨φ, g, hφ, hg⟩ := AreaDeficit.subsequence_of_local_normality hFc hN
  let G : ℂ → OnePoint ℂ := fun w => if hw : w ∈ U 0 then g ⟨w, hw⟩ else ∞
  have hgGsub : TendstoLocallyUniformly
      (fun n (w : U 0) => ((f^[σ (φ n)]) (w : ℂ) : OnePoint ℂ))
      (G ∘ Subtype.val) atTop :=
    hg.congr_right fun w => by simp [G, w.property]
  have hgG : TendstoLocallyUniformlyOn
      (fun n w => ((f^[σ (φ n)]) w : OnePoint ℂ)) G atTop (U 0) :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hgGsub
  have hit : ∀ n, MapsTo (f^[n]) (U 0) (U n) := by
    intro n
    induction n with
    | zero => exact mapsTo_id _
    | succ n ih =>
        simpa only [Function.iterate_succ'] using (hforward n).comp ih
  have hFhol : ∀ n, SphereHolomorphicOn
      (fun w => ((f^[σ (φ n)]) w : OnePoint ℂ)) (U 0) := by
    intro n
    have haIter : AnalyticOnNhd ℂ (f^[σ (φ n)]) (U 0) := by
      intro w hw
      exact FunctionTheory.analyticAt_iterate_of_finite_orbit
        (fun j _ => hUpole hw j)
    exact haIter.differentiableOn.sphereHolomorphicOn hUo
  have hpair : Pairwise fun n m => Disjoint
      ((fun w => ((f^[σ (φ n)]) w : OnePoint ℂ)) '' U 0)
      ((fun w => ((f^[σ (φ m)]) w : OnePoint ℂ)) '' U 0) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro p ⟨v, hv, hvp⟩ ⟨w, hw, hwp⟩
    have heq : (f^[σ (φ n)]) v = (f^[σ (φ m)]) w :=
      OnePoint.coe_injective (hvp.trans hwp.symm)
    exact disjoint_left.mp (hdis ((hσ.comp hφ).injective.ne hnm))
      (hit _ hv) (heq ▸ hit _ hw)
  have hconst : ∀ w ∈ U 0, G w = G z :=
    AreaDeficit.limit_constant_of_disjoint_sphere_images
      hUo hUc hz hFhol hgG hpair
  have hGz : G z = ∞ := by
    exact tendsto_nhds_unique (hgG.tendsto_at hz)
      (hlim.comp hφ.tendsto_atTop)
  refine ⟨σ ∘ φ, hσ.comp hφ, ?_⟩
  have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
      ComplexDynamics.riemannSphereUniformSpace :=
    unique_uniformity_of_compact rfl rfl
  rw [← heq]
  exact hgG.congr_right fun w hw => (hconst w hw).trans hGz

/-- The meromorphic statement follows directly from the surface compact-orbit
theorem, as in the paper. -/
theorem wanderingLocallyUniformInfinityClaim_of_surface_theorem
    (hsurface : SurfaceDynamics.NoCompactWanderingOrbitClaim
      (X := OnePoint ℂ)) :
    ∀ {f : ℂ → ℂ}, MeromorphicNFOn f univ →
      ¬ FunctionTheory.IsRationalMeromorphic f →
      ∀ {U : ℕ → Set ℂ} {z : ℂ},
        (∀ n, IsFatouComponent f (U n)) → z ∈ U 0 →
        (∀ n, MapsTo f (U n) (U (n + 1))) →
        Pairwise (fun n m => Disjoint (U n) (U m)) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ TendstoLocallyUniformlyOn
          (fun k w => ((f^[σ k]) w : OnePoint ℂ))
          (fun _ => (∞ : OnePoint ℂ)) atTop (U 0) := by
  intro f hf htrans U z hU hz hforward hdis
  exact wandering_orbit_locallyUniform_infty_of_unbounded hU hz hforward hdis
    (wandering_orbit_unbounded_of_surface_theorem hsurface hf htrans
      hU hz hforward hdis)

end MeromorphicDynamics
