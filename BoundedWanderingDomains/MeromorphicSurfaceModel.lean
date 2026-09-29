module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.MeromorphicSphereHolomorphic
public import BoundedWanderingDomains.Surfaces.LocalDynamics
public import BoundedWanderingDomains.Surfaces.OpenMapping
public import BoundedWanderingDomains.Surfaces.PlaneReading
public import FunctionTheory.Meromorphic.RationalInfinity

@[expose] public section

/-! # A meromorphic plane map as a local map of the sphere -/

open Set Function OnePoint Topology
open scoped Manifold Topology

namespace MeromorphicDynamics

/-- The finite part of the Riemann sphere, used as the source of a
meromorphic local map. -/
noncomputable def finiteSphereOpens : TopologicalSpace.Opens (OnePoint ℂ) :=
  ⟨RiemannDynamics.sphereChartFinite.source,
    RiemannDynamics.sphereChartFinite.open_source⟩

@[simp] theorem coe_mem_finiteSphereOpens (z : ℂ) :
    (z : OnePoint ℂ) ∈ finiteSphereOpens := by
  change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source
  rw [RiemannDynamics.sphereChartFinite_source]
  exact OnePoint.coe_ne_infty z

/-- The finite source of the sphere model is globally the complex plane. -/
noncomputable def finiteSphereHomeomorph : ℂ ≃ₜ finiteSphereOpens where
  toFun z := ⟨(z : OnePoint ℂ), coe_mem_finiteSphereOpens z⟩
  invFun z := RiemannDynamics.sphereChartFinite (z : OnePoint ℂ)
  left_inv z := by simp
  right_inv z := by
    apply Subtype.ext
    have hzfin : (z : OnePoint ℂ) ∈ finiteSphereOpens := z.property
    have hz : (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source := by
      change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hzfin
      exact hzfin
    simpa only [RiemannDynamics.sphereChartFinite_symm_apply] using
      RiemannDynamics.sphereChartFinite.left_inv hz
  continuous_toFun := continuous_coe.subtype_mk (fun z => coe_mem_finiteSphereOpens z)
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro z
    have hzfin : (z : OnePoint ℂ) ∈ finiteSphereOpens := z.property
    have hz : (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source := by
      change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hzfin
      exact hzfin
    exact (RiemannDynamics.sphereChartFinite.continuousAt hz).comp
      continuous_subtype_val.continuousAt

@[simp] theorem finiteSphereHomeomorph_apply (z : ℂ) :
    (finiteSphereHomeomorph z : OnePoint ℂ) = (z : OnePoint ℂ) := rfl

/-- A meromorphic function is a local self-map of the sphere whose source is
the finite chart. Poles are mapped to the genuine point at infinity. -/
noncomputable def surfaceModel (f : ℂ → ℂ) :
    SurfaceDynamics.LocalMap (OnePoint ℂ) where
  source := finiteSphereOpens
  map z := FunctionTheory.meromorphicSphereValue f
    (RiemannDynamics.sphereChartFinite z)

@[simp] theorem surfaceModel_source (f : ℂ → ℂ) :
    (surfaceModel f).source = finiteSphereOpens := rfl

@[simp] theorem surfaceModel_map_coe (f : ℂ → ℂ) (z : ℂ) :
    (surfaceModel f).map ⟨(z : OnePoint ℂ), coe_mem_finiteSphereOpens z⟩ =
      FunctionTheory.meromorphicSphereValue f z := by
  simp [surfaceModel]

/-- The sphere model is intrinsically holomorphic on its actual source. -/
theorem surfaceModel_mdifferentiable {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (surfaceModel f).map := by
  have hsphere :=
    FunctionTheory.MeromorphicNFOn.mdifferentiable_meromorphicSphereValue hf
  have hchart : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : finiteSphereOpens => RiemannDynamics.sphereChartFinite (z : OnePoint ℂ)) := by
    intro z
    exact (mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas ((0 : ℂ) : OnePoint ℂ)) z.2).comp z
        (AreaDeficit.Surfaces.mdifferentiable_subtype_val finiteSphereOpens z)
  exact hsphere.comp hchart

theorem continuous_surfaceModel_map {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) : Continuous (surfaceModel f).map :=
  (surfaceModel_mdifferentiable hf).continuous

/-- If the honest sphere-valued realization of a meromorphic function is
locally constant, then the meromorphic function is rational (indeed
constant). This is the identity principle needed for the open-mapping
bridge. -/
theorem rational_of_meromorphicSphereValue_eventuallyEq
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    {a : ℂ} {v : OnePoint ℂ}
    (hv : FunctionTheory.meromorphicSphereValue f =ᶠ[𝓝 a] fun _ => v) :
    FunctionTheory.IsRationalMeromorphic f := by
  cases v with
  | infty =>
      have ha := (hf (mem_univ a)).meromorphicAt.eventually_analyticAt
      have hv' := hv.filter_mono
        (nhdsWithin_le_nhds : 𝓝[≠] a ≤ 𝓝 a)
      have hfalse : ∀ᶠ z in 𝓝[≠] a, False := by
        filter_upwards [ha, hv'] with z hzA hzv
        rw [FunctionTheory.meromorphicSphereValue_of_analytic hzA] at hzv
        exact OnePoint.coe_ne_infty _ hzv
      obtain ⟨z, hz⟩ := hfalse.exists
      exact hz.elim
  | coe c =>
      let g : ℂ → ℂ := fun z => f z - c
      have hg : MeromorphicOn g Set.univ := fun z _ =>
        (hf (mem_univ z)).meromorphicAt.sub (analyticAt_const.meromorphicAt)
      have hzero : g =ᶠ[𝓝 a] 0 := by
        filter_upwards [hv] with z hzv
        by_cases hzA : AnalyticAt ℂ f z
        · rw [FunctionTheory.meromorphicSphereValue_of_analytic hzA] at hzv
          exact sub_eq_zero.mpr (OnePoint.coe_eq_coe.mp hzv)
        · rw [FunctionTheory.meromorphicSphereValue_of_not_analytic hzA] at hzv
          exact (OnePoint.infty_ne_coe c hzv).elim
      have htopa : meromorphicOrderAt g a = ⊤ :=
        meromorphicOrderAt_eq_top_iff.mpr
          (hzero.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] a ≤ 𝓝 a))
      have htop (z : ℂ) : meromorphicOrderAt g z = ⊤ :=
        hg.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
          (mem_univ a) (mem_univ z) htopa
      refine ⟨Polynomial.C c, 1, one_ne_zero, ?_⟩
      intro z
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp (htop z)] with w hw
      simp only [g] at hw
      simpa only [Polynomial.eval_C, Polynomial.eval_one, div_one] using
        sub_eq_zero.mp hw

/-- A transcendental meromorphic function is locally nonconstant when read
honestly as a sphere-valued map, including at its poles. -/
theorem not_eventuallyEq_meromorphicSphereValue_const
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    (htrans : ¬ FunctionTheory.IsRationalMeromorphic f) (a : ℂ)
    (v : OnePoint ℂ) :
    ¬ FunctionTheory.meromorphicSphereValue f =ᶠ[𝓝 a] fun _ => v := by
  intro hconst
  exact htrans (rational_of_meromorphicSphereValue_eventuallyEq hf hconst)

/-- The sphere model of a transcendental meromorphic function is open. -/
theorem surfaceModel_isOpenMap {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (htrans : ¬ FunctionTheory.IsRationalMeromorphic f) :
    IsOpenMap (surfaceModel f).map := by
  apply SurfaceDynamics.isOpenMap_of_mdifferentiable_of_locally_nonconstant
    (surfaceModel_mdifferentiable hf)
  intro x hconst
  let z : ℂ := RiemannDynamics.sphereChartFinite (x : OnePoint ℂ)
  let ι : ℂ → (surfaceModel f).source := fun w =>
    ⟨(w : OnePoint ℂ), coe_mem_finiteSphereOpens w⟩
  have hι : Continuous ι :=
    continuous_coe.subtype_mk (fun w => coe_mem_finiteSphereOpens w)
  have hxfin : (x : OnePoint ℂ) ∈ finiteSphereOpens := by
    exact x.property
  have hxsrc : (x : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source := by
    change (x : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hxfin
    exact hxfin
  have hιz : ι z = x := by
    apply Subtype.ext
    simpa only [ι, z, RiemannDynamics.sphereChartFinite_symm_apply] using
      RiemannDynamics.sphereChartFinite.left_inv hxsrc
  have hιt : Filter.Tendsto ι (𝓝 z) (𝓝 x) := by
    rw [← hιz]
    exact hι.tendsto z
  have hc := hconst.comp_tendsto hιt
  have hsphere : FunctionTheory.meromorphicSphereValue f =ᶠ[𝓝 z]
      fun _ => FunctionTheory.meromorphicSphereValue f z := by
    filter_upwards [hc] with w hw
    change (surfaceModel f).map (ι w) = (surfaceModel f).map x at hw
    rw [← hιz] at hw
    simpa only [ι, surfaceModel_map_coe] using hw
  exact not_eventuallyEq_meromorphicSphereValue_const hf htrans z
    (FunctionTheory.meromorphicSphereValue f z) hsphere

/-- The local sphere model supplies exactly the open-holomorphic structure
required by the surface dynamics theorems. -/
theorem surfaceModel_isOpenHolomorphic {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (htrans : ¬ FunctionTheory.IsRationalMeromorphic f) :
    SurfaceDynamics.IsOpenHolomorphic (surfaceModel f) :=
  ⟨surfaceModel_isOpenMap hf htrans, surfaceModel_mdifferentiable hf⟩

@[simp] theorem surfaceModel_step_coe (f : ℂ → ℂ) (z : ℂ) :
    (surfaceModel f).step (z : OnePoint ℂ) =
      Option.some (FunctionTheory.meromorphicSphereValue f z) := by
  simp [SurfaceDynamics.LocalMap.step, surfaceModel]

/-- On an orbit segment containing no pole, partial sphere iteration agrees
with ordinary iteration of the chosen finite representative. -/
theorem surfaceModel_iterate_coe_of_analytic
    (f : ℂ → ℂ) (n : ℕ) (z : ℂ)
    (h : ∀ j < n, AnalyticAt ℂ f ((f^[j]) z)) :
    (surfaceModel f).iterate n (z : OnePoint ℂ) =
      Option.some (((f^[n]) z : ℂ) : OnePoint ℂ) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [SurfaceDynamics.LocalMap.iterate_succ _ n _ (coe_mem_finiteSphereOpens z)]
      rw [surfaceModel_map_coe]
      have ha0 : AnalyticAt ℂ f z := by
        simpa using h 0 (Nat.zero_lt_succ n)
      rw [FunctionTheory.meromorphicSphereValue_of_analytic ha0]
      rw [Function.iterate_succ_apply]
      apply ih
      intro j hj
      simpa only [Function.iterate_succ_apply] using
        h (j + 1) (Nat.succ_lt_succ hj)

/-- Points whose ordinary forward orbit never meets a pole. -/
def poleAvoidingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∀ n : ℕ, AnalyticAt ℂ f ((f^[n]) z)}

/-- A pole-avoiding ordinary orbit is a trapped orbit of the sphere model. -/
theorem poleAvoiding_mem_surfaceModel_trapped {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ poleAvoidingSet f) :
    (z : OnePoint ℂ) ∈ (surfaceModel f).trapped := by
  intro n
  refine ⟨((f^[n]) z : OnePoint ℂ), coe_mem_finiteSphereOpens _, ?_⟩
  exact surfaceModel_iterate_coe_of_analytic f n z
    (fun j hj => hz j)

/-- Conversely, a finite point is trapped by the sphere model only when its
ordinary orbit avoids every pole. -/
theorem poleAvoiding_of_mem_surfaceModel_trapped {f : ℂ → ℂ} {z : ℂ}
    (hz : (z : OnePoint ℂ) ∈ (surfaceModel f).trapped) :
    z ∈ poleAvoidingSet f := by
  have analytic_of_trapped (w : ℂ)
      (hw : (w : OnePoint ℂ) ∈ (surfaceModel f).trapped) :
      AnalyticAt ℂ f w := by
    by_contra hwa
    have hforward := (surfaceModel f).trapped_forward hw
    have hsource := (surfaceModel f).trapped_subset_source hforward
    rw [surfaceModel_map_coe] at hsource
    change FunctionTheory.meromorphicSphereValue f w ∈ finiteSphereOpens at hsource
    rw [FunctionTheory.meromorphicSphereValue_of_not_analytic hwa] at hsource
    change (∞ : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hsource
    rw [RiemannDynamics.sphereChartFinite_source] at hsource
    exact hsource rfl
  have htrapped (n : ℕ) :
      (((f^[n]) z : ℂ) : OnePoint ℂ) ∈ (surfaceModel f).trapped := by
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        have hforward := (surfaceModel f).trapped_forward ih
        have han := analytic_of_trapped ((f^[n]) z) ih
        rw [surfaceModel_map_coe] at hforward
        rw [FunctionTheory.meromorphicSphereValue_of_analytic han] at hforward
        simpa only [Function.iterate_succ_apply'] using hforward
  intro n
  exact analytic_of_trapped ((f^[n]) z) (htrapped n)

theorem poleAvoiding_iff_mem_surfaceModel_trapped {f : ℂ → ℂ} {z : ℂ} :
    z ∈ poleAvoidingSet f ↔
      (z : OnePoint ℂ) ∈ (surfaceModel f).trapped :=
  ⟨poleAvoiding_mem_surfaceModel_trapped,
    poleAvoiding_of_mem_surfaceModel_trapped⟩

/-- On a pole-avoiding orbit the compactified local iterate is precisely the
usual meromorphic iterate included in the sphere. -/
theorem surfaceModel_compactifiedIterate_coe_of_poleAvoiding
    (f : ℂ → ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ poleAvoidingSet f) :
    (surfaceModel f).compactifiedIterate n (z : OnePoint ℂ) =
      ((((f^[n]) z : ℂ) : OnePoint ℂ) : OnePoint (OnePoint ℂ)) := by
  rw [SurfaceDynamics.LocalMap.compactifiedIterate]
  rw [surfaceModel_iterate_coe_of_analytic f n z (fun j hj => hz j)]

end MeromorphicDynamics
