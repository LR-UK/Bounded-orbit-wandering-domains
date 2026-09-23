/-
Adapted from Geoffrey Irving's ray project, Apache 2.0.
Source: Ray/Manifold/RiemannSphere.lean, through the IsManifold instance.
Pinned commit: 753f7131cf96f4651294de4398368abf136c34de.
Public definitions and theorem statements are retained. Imports are restricted
to the atlas construction; obsolete reciprocal-limit helpers use Mathlib.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic

/-- Same model abbreviation as Ray.Manifold.Defs. -/
public noncomputable abbrev OneDimension.I := modelWithCornersSelf ℂ ℂ

open scoped Topology in
private theorem ray_eventually_cobounded (r : ℝ) :
    ∀ᶠ z : ℂ in Bornology.cobounded ℂ, r < ‖z‖ := by
  filter_upwards [eventually_cobounded_le_norm (r + 1)] with z hz
  linarith

/-!
## The Riemann sphere

We give `OnePoint ℂ` the natural analytic manifold structure with two charts,
namely `coe` and `inv ∘ coe`, giving the Riemann sphere `𝕊`.
-/

open Bornology (cobounded)
open Classical
open Complex
open Filter (Tendsto atTop)
open Function (curry uncurry)
open OneDimension
open Set
open scoped Topology OnePoint
noncomputable section

variable {α : Type}

/-- A left inverse to `coe : ℂ → 𝕊`.
    We put this outside the `RiemannSphere` namespace so that `z.toComplex` works. -/
public def OnePoint.toComplex (z : OnePoint ℂ) : ℂ := z.rec 0 id

namespace RiemannSphere

/-- The Riemann sphere, as a complex manifold -/
scoped notation "𝕊" => OnePoint ℂ

-- Basic instances for 𝕊
public instance : Zero 𝕊 := ⟨((0 : ℂ) : 𝕊)⟩
public instance : Inhabited 𝕊 := ⟨0⟩
@[simp] public theorem coe_zero : ((0 : ℂ) : 𝕊) = (0 : 𝕊) := rfl
@[simp] public theorem coe_eq_coe {z w : ℂ} : (z : 𝕊) = w ↔ z = w := OnePoint.coe_eq_coe
@[simp] public theorem coe_eq_zero (z : ℂ) : (z : 𝕊) = (0 : 𝕊) ↔ z = 0 := by
  simp only [← coe_zero, coe_eq_coe]

/-- `coe : ℂ → 𝕊` is injective -/
public theorem injective_coe : Function.Injective (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.coe_injective

/-- `coe : ℂ → 𝕊` is continuous -/
public theorem continuous_coe : Continuous (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.continuous_coe

-- Recursion lemmas
@[simp] public theorem rec_coe {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} (z : ℂ) :
    (z : 𝕊).rec i f = f z := rfl
@[simp] public theorem rec_inf {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} :
    (∞ : 𝕊).rec i f = i := rfl
theorem map_rec {A B : Sort*} (g : A → B) {f : ℂ → A} {i : A} {z : 𝕊} :
    g (z.rec i f) = (z.rec (g i) (g ∘ f)) := by
  induction z using OnePoint.rec
  · simp only [rec_inf]
  · simp only [rec_coe, Function.comp]

-- ∞ is not 0 or finite
@[simp] public theorem inf_ne_coe {z : ℂ} : (∞ : 𝕊) ≠ ↑z := by
  simp only [Ne, OnePoint.infty_ne_coe, not_false_iff]
@[simp] public theorem inf_ne_zero : (∞ : 𝕊) ≠ (0 : 𝕊) := by
  have e : (0 : 𝕊) = ((0 : ℂ) : 𝕊) := rfl; rw [e]; exact inf_ne_coe
@[simp] public theorem zero_ne_inf : (0 : 𝕊) ≠ (∞ : 𝕊) := inf_ne_zero.symm
@[simp] public theorem coe_ne_inf {z : ℂ} : (z : 𝕊) ≠ ∞ := inf_ne_coe.symm
@[simp] public theorem coe_eq_inf_iff {z : ℂ} : (z : 𝕊) = ∞ ↔ False := ⟨coe_ne_inf, False.elim⟩

-- Conversion to ℂ, sending ∞ to 0
@[simp] public theorem toComplex_coe {z : ℂ} : (z : 𝕊).toComplex = z := by rfl
@[simp] public theorem toComplex_inf : (∞ : 𝕊).toComplex = 0 := by rfl
public theorem coe_toComplex {z : 𝕊} (h : z ≠ ∞) : ↑z.toComplex = z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at h
  · simp only [toComplex_coe]
@[simp] public lemma  toComplex_zero : (0 : 𝕊).toComplex = 0 := by rw [← coe_zero, toComplex_coe]
@[simp] public lemma toComplex_eq_zero {z : 𝕊} : z.toComplex = 0 ↔ z = 0 ∨ z = ∞ := by
  induction z using OnePoint.rec
  · simp only [toComplex_inf, or_true]
  · simp only [toComplex_coe, coe_eq_zero, OnePoint.coe_ne_infty, or_false]
public theorem continuousAt_toComplex {z : ℂ} : ContinuousAt OnePoint.toComplex z := by
  simp only [OnePoint.continuousAt_coe]; exact continuousAt_id
public theorem continuousOn_toComplex : ContinuousOn OnePoint.toComplex ({∞}ᶜ) := by
  intro z m; induction z using OnePoint.rec
  · simp only [mem_compl_iff, mem_singleton_iff, not_true] at m
  · exact continuousAt_toComplex.continuousWithinAt

/-- `toComplex` is injective away from `∞` -/
public lemma toComplex_inj {z w : 𝕊} (zi : z ≠ (∞ : 𝕊)) (wi : w ≠ (∞ : 𝕊)) :
    z.toComplex = w.toComplex ↔ z = w := by
  induction' z using OnePoint.rec
  all_goals induction' w using OnePoint.rec
  all_goals simp_all

/-- Inversion in `𝕊`, interchanging `0` and `∞` -/
public def inv (z : 𝕊) : 𝕊 := if z = 0 then ∞ else ↑z.toComplex⁻¹
public instance : Inv 𝕊 := ⟨RiemannSphere.inv⟩
theorem inv_def (z : 𝕊) : z⁻¹ = RiemannSphere.inv z := by rfl
public instance : InvolutiveInv 𝕊 where
  inv := Inv.inv
  inv_inv := by
    simp_rw [inv_def, inv]; apply OnePoint.rec
    · simp only [inf_ne_zero, toComplex_inf, inv_zero, coe_zero, ite_false, toComplex_zero,
        ite_true]
    · intro z; by_cases z0 : z = 0
      · simp only [z0, coe_zero, toComplex_zero, inv_zero, ite_true, inf_ne_zero, toComplex_inf,
          ite_false]
      · simp only [coe_eq_zero, z0, toComplex_coe, ite_false, inv_eq_zero, inv_inv]
@[simp] public lemma inv_zero' : (0 : 𝕊)⁻¹ = ∞ := by simp only [inv_def, inv, if_true]
@[simp] public lemma inv_inf : ((∞ : 𝕊)⁻¹ : 𝕊) = 0 := by simp [inv_def, inv, inf_ne_zero]

public theorem inv_coe {z : ℂ} (z0 : z ≠ 0) : (z : 𝕊)⁻¹ = ↑(z : ℂ)⁻¹ := by
  simp only [inv_def, inv, z0, toComplex_coe, if_false, coe_eq_zero]
@[simp] public lemma inv_eq_inf {z : 𝕊} : z⁻¹ = ∞ ↔ z = 0 := by
  induction z using OnePoint.rec
  · simp only [inv_inf]; exact ⟨Eq.symm, Eq.symm⟩
  · simp only [inv_def, inv, not_not, imp_false, ite_eq_left_iff, OnePoint.coe_ne_infty]
@[simp] public lemma inv_eq_zero {z : 𝕊} : z⁻¹ = 0 ↔ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf]
  · simp only [inv_def, inv, toComplex_coe]
    by_cases z0 : (z : 𝕊) = 0; simp only [if_pos, z0, inf_ne_zero, inf_ne_zero.symm]
    simp only [if_neg z0, coe_ne_inf, iff_false]; rw [coe_eq_zero, _root_.inv_eq_zero]
    simpa only [coe_eq_zero] using z0
public theorem toComplex_inv {z : 𝕊} : z⁻¹.toComplex = z.toComplex⁻¹ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, toComplex_zero, toComplex_inf, inv_zero]
  · by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', toComplex_inf, toComplex_zero, inv_zero]
    · simp only [z0, inv_coe, Ne, not_false_iff, toComplex_coe]

/-- `coe` tends to `∞` `cobounded` -/
public theorem coe_tendsto_inf : Tendsto (fun z : ℂ ↦ (z : 𝕊)) (cobounded ℂ) (𝓝 ∞) := by
  rw [Filter.tendsto_iff_comap, OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
  exact Metric.cobounded_le_cocompact

/-- `coe` tends to `∞` `cobounded`, but without touching `∞` -/
public theorem coe_tendsto_inf' : Tendsto (fun z : ℂ ↦ (z : 𝕊)) (cobounded _) (𝓝[{∞}ᶜ] ∞) := by
  have e : {(∞ : 𝕊)}ᶜ = range (fun z : ℂ ↦ (z : 𝕊)) := by
    ext z; induction' z using OnePoint.rec with z
    · simp only [mem_compl_iff, mem_singleton_iff, not_true, mem_range, OnePoint.coe_ne_infty,
        exists_false]
    · simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true,
        mem_range, coe_eq_coe, exists_eq]
  simp only [e, tendsto_nhdsWithin_range, coe_tendsto_inf]

@[simp] public lemma map_some_cobounded : Filter.map OnePoint.some (cobounded ℂ) = 𝓝[{∞}ᶜ] ∞ := by
  rw [@OnePoint.nhdsNE_infty_eq, Metric.cobounded_eq_cocompact, Filter.coclosedCompact_eq_cocompact]

/-- Inversion is continuous -/
public theorem continuous_inv : Continuous fun z : 𝕊 ↦ z⁻¹ := by
  rw [← continuousOn_univ]; intro z _; apply ContinuousAt.continuousWithinAt
  induction' z using OnePoint.rec with z
  · simp only [OnePoint.continuousAt_infty', Function.comp_def, Filter.coclosedCompact_eq_cocompact,
      inv_inf, ← Metric.cobounded_eq_cocompact]
    have e : ∀ᶠ z : ℂ in cobounded ℂ, ↑z⁻¹ = (↑z : 𝕊)⁻¹ := by
      refine (ray_eventually_cobounded 0).mp (.of_forall fun z z0 ↦ ?_)
      simp only [norm_pos_iff] at z0; rw [inv_coe z0]
    apply Filter.Tendsto.congr' e
    exact Filter.Tendsto.comp continuous_coe.continuousAt Filter.tendsto_inv₀_cobounded
  · simp only [OnePoint.continuousAt_coe, Function.comp_def, inv_def, inv, coe_eq_zero,
      toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, ContinuousAt, OnePoint.nhds_infty_eq, if_true,
        Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      simp only [← nhdsNE_sup_pure, Filter.tendsto_sup]
      constructor
      · refine Filter.Tendsto.mono_right ?_ le_sup_left
        apply tendsto_nhdsWithin_congr (f := fun z : ℂ ↦ (↑z⁻¹ : 𝕊))
        · intro z m
          rw [mem_compl_singleton_iff] at m
          simp only [m, ite_false]
        · simp only [map_some_cobounded]
          apply coe_tendsto_inf'.comp
          exact Filter.tendsto_inv₀_nhdsNE_zero
      · refine Filter.Tendsto.mono_right ?_ le_sup_right
        simp only [Filter.pure_zero, Filter.tendsto_pure, ite_eq_left_iff, Filter.eventually_zero,
          not_true, IsEmpty.forall_iff]
    · have e : ∀ᶠ w : ℂ in 𝓝 z, (if w = 0 then ∞ else ↑w⁻¹ : 𝕊) = ↑w⁻¹ := by
        refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
        simp only [Ne, id_eq] at w0; simp only [w0, if_false]
      simp only [continuousAt_congr e]
      exact continuous_coe.continuousAt.comp (tendsto_inv₀ z0)
instance : ContinuousInv 𝕊 := ⟨continuous_inv⟩

/-- Inversion as an equivalence -/
public def invEquiv : 𝕊 ≃ 𝕊 where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- Inversion as a homeomorphism -/
public def invHomeomorph : 𝕊 ≃ₜ 𝕊 where
  toEquiv := invEquiv
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv
@[simp] public lemma invEquiv_apply (z : 𝕊) : invEquiv z = z⁻¹ := by
  simp only [invEquiv, Equiv.coe_fn_mk]
@[simp] public lemma invEquiv_symm : invEquiv.symm = invEquiv := by
  simp only [Equiv.ext_iff, invEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, forall_const]
@[simp] public lemma invHomeomorph_apply (z : 𝕊) : invHomeomorph z = z⁻¹ := by
  simp only [invHomeomorph]
  exact invEquiv_apply z
@[simp] public lemma invHomeomorph_symm : invHomeomorph.symm = invHomeomorph := Homeomorph.ext (by
  intro x
  show invEquiv.symm x = invEquiv x
  rw [invEquiv_symm])

/-- `coe : ℂ → 𝕊` as an equivalence -/
public def coePartialEquiv : PartialEquiv ℂ 𝕊 where
  toFun := fun x : ℂ ↦ x
  invFun := OnePoint.toComplex
  source := univ
  target := {∞}ᶜ
  map_source' z _ := by
    simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_iff]
  map_target' z _ := mem_univ _
  left_inv' z _ := toComplex_coe
  right_inv' z m := coe_toComplex m

/-- `coe : ℂ → 𝕊` as a partial homeomorphism.  This is the first chart of `𝕊`. -/
public def coeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ 𝕊 where
  toPartialEquiv := coePartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuous_coe.continuousOn
  continuousOn_invFun := continuousOn_toComplex

/-- `inv ∘ coe : ℂ → 𝕊` as a partial homeomorphism.  This is the second chart of `𝕊`. -/
public def invCoeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ 𝕊 :=
  coeOpenPartialHomeomorph.trans invHomeomorph.toOpenPartialHomeomorph

@[simp] lemma coePartialEquiv_target : coePartialEquiv.target = {∞}ᶜ := rfl
@[simp] lemma coeOpenPartialHomeomorph_target : coeOpenPartialHomeomorph.target = {∞}ᶜ := by
  simp only [coeOpenPartialHomeomorph, coePartialEquiv_target]
@[simp] lemma invCoeOpenPartialHomeomorph_target : invCoeOpenPartialHomeomorph.target = {0}ᶜ := by
  ext z; simp only [invCoeOpenPartialHomeomorph, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    invHomeomorph_symm, coeOpenPartialHomeomorph_target, preimage_compl, univ_inter, mem_compl_iff,
    mem_preimage, invHomeomorph_apply, mem_singleton_iff, inv_eq_inf]
@[simp] public lemma coePartialEquiv_apply (z : ℂ) : coePartialEquiv z = ↑z := by rfl
@[simp] public lemma coePartialEquiv_symm_apply (z : 𝕊) : coePartialEquiv.symm z = z.toComplex := by
  rfl
@[simp] public lemma invCoeOpenPartialHomeomorph_apply (z : ℂ) :
    invCoeOpenPartialHomeomorph z = (z : 𝕊)⁻¹ := by rfl
@[simp] public lemma invCoeOpenPartialHomeomorph_symm_apply (z : 𝕊) :
    invCoeOpenPartialHomeomorph.symm z = (z⁻¹).toComplex := by rfl

/-- Chart structure for `𝕊` -/
public instance : ChartedSpace ℂ 𝕊 where
  atlas := {e | e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm}
  chartAt z := z.rec invCoeOpenPartialHomeomorph.symm (fun _ ↦ coeOpenPartialHomeomorph.symm)
  mem_chart_source := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        invCoeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, inf_ne_zero,
        not_false_eq_true]
    · simp only [rec_coe, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        coeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty,
        not_false_eq_true]
  chart_mem_atlas := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, mem_ofPred_eq, or_true]
    · simp only [rec_coe, mem_ofPred_eq, true_or]

/-- There are just two charts on `𝕊` -/
theorem two_charts {e : OpenPartialHomeomorph 𝕊 ℂ} (m : e ∈ atlas ℂ 𝕊) :
    e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm := m

-- Chart simplification lemmas
@[simp] public lemma chartAt_coe {z : ℂ} : chartAt ℂ (z : 𝕊) = coeOpenPartialHomeomorph.symm := rfl
@[simp] public lemma chartAt_inf : @chartAt ℂ _ 𝕊 _ _ ∞ = invCoeOpenPartialHomeomorph.symm := rfl
public theorem extChartAt_coe {z : ℂ} : extChartAt I (z : 𝕊) = coePartialEquiv.symm := by
  simp only [coeOpenPartialHomeomorph, extChartAt, OpenPartialHomeomorph.extend, chartAt_coe,
    OpenPartialHomeomorph.symm_toPartialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
theorem extChartAt_zero : extChartAt I (0 : 𝕊) = coePartialEquiv.symm := by
  simp only [← coe_zero, extChartAt_coe]
public theorem extChartAt_inf :
    extChartAt I (∞ : 𝕊) = invEquiv.toPartialEquiv.trans coePartialEquiv.symm := by
  apply PartialEquiv.ext
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.coe_trans_symm,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, Function.comp_apply]
    show coePartialEquiv.symm (invEquiv.symm z) = coePartialEquiv.symm (invEquiv z)
    rw [invEquiv_symm]
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      invEquiv, OpenPartialHomeomorph.extend, chartAt_inf,
      OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.symm_symm,
      PartialEquiv.coe_trans, OpenPartialHomeomorph.coe_toPartialEquiv,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
      PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply, Equiv.coe_fn_symm_mk]
  · simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.symm_source, PartialEquiv.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.trans_source, Equiv.toPartialEquiv_source,
      Equiv.toPartialEquiv_apply]
    show univ ∩ ⇑invEquiv.symm ⁻¹' coePartialEquiv.target
      = univ ∩ ⇑invEquiv ⁻¹' coePartialEquiv.target
    rw [invEquiv_symm]
public theorem extChartAt_inf_apply {x : 𝕊} : extChartAt I ∞ x = x⁻¹.toComplex := by
  simp only [extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
    Equiv.toPartialEquiv_apply, invEquiv_apply]

/-- `𝕊`'s charts have analytic groupoid structure -/
instance : HasGroupoid 𝕊 (contDiffGroupoid ⊤ I) where
  compatible := by
    have e0 : ((fun z : ℂ ↦ (z : 𝕊)) ⁻¹' {0})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, coe_eq_zero]
    have e1 : ((fun z : ℂ ↦ (z : 𝕊)⁻¹) ⁻¹' {∞})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, inv_eq_inf, coe_eq_zero]
    have a : AnalyticOnNhd ℂ (fun z : ℂ ↦ OnePoint.toComplex (z : 𝕊)⁻¹) {0}ᶜ := by
      apply AnalyticOnNhd.congr (f := fun z ↦ z⁻¹)
      · exact isOpen_compl_singleton
      · apply analyticOnNhd_inv
      · intro z z0; simp only [mem_compl_iff, mem_singleton_iff] at z0
        simp only [inv_coe z0, toComplex_coe]
    intro f g fa ga
    simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid, mfld_simps]
    refine ⟨AnalyticOnNhd.contDiffOn ?_ ?_, AnalyticOnNhd.contDiffOn ?_ ?_⟩
    all_goals cases' two_charts fa with fh fh
    all_goals cases' two_charts ga with gh gh
    all_goals try simp [fh, gh, coeOpenPartialHomeomorph, invCoeOpenPartialHomeomorph,
      coePartialEquiv, coeOpenPartialHomeomorph, invHomeomorph, invEquiv, Function.comp_def,
      analyticOnNhd_id, e0, e1, a, uniqueDiffOn_univ]
    all_goals try exact isOpen_compl_singleton.uniqueDiffOn
    all_goals apply IsOpen.uniqueDiffOn
    all_goals convert isOpen_univ
    all_goals aesop

/-- `𝕊` is an analytic manifold -/
public instance : IsManifold I ⊤ 𝕊 where


end RiemannSphere

namespace FunctionTheory

/-- The reused two-chart atlas makes the one-point compactification a complex manifold. -/
public theorem riemannSphere_isManifold :
    IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ (OnePoint ℂ) := inferInstance

end FunctionTheory
