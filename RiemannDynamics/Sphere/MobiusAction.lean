/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import RiemannDynamics.Sphere.Basic

/-!
# Möbius transformations of the Riemann sphere

Mathlib provides the set-theoretic action of `GL (Fin 2) ℂ` on
`ℂ̂ = OnePoint ℂ` (via the identification with `ℙ¹(ℂ)`), together with the
explicit Möbius formulas `OnePoint.smul_some_eq_ite` and
`OnePoint.smul_infty_eq_ite`. This file supplies the topological layer that
Mathlib leaves open.

## Main definitions

* `inversionGL` — the inversion `z ↦ 1/z` as an element of `GL (Fin 2) ℂ`,
  which interchanges the two standard charts of `ℂ̂`.
* `mobiusApply` — the Möbius transformation `g • ·` packaged as a map `ℂ̂ → ℂ̂`.

## Main results

* `continuous_gl_smul` — every Möbius transformation `g • ·` is continuous on
  `ℂ̂` (hence a homeomorphism, its inverse being the action of `g⁻¹`).
* `exists_gl_smul_eq_zero_one_infty` — the action is transitive on ordered triples
  of distinct points: every such triple can be sent to `(0, 1, ∞)`.
-/

open OnePoint Matrix Filter Topology

namespace RiemannDynamics

/-- The inversion `z ↦ 1/z` (swapping `0 ↔ ∞`) as an element of
`GL (Fin 2) ℂ`. -/
noncomputable def inversionGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0]
    (by norm_num [Matrix.det_fin_two_of])

/-- The inversion acts on finite points by `z ↦ 1/z`, sending `0 ↦ ∞`. -/
theorem inversionGL_smul_coe (z : ℂ) :
    inversionGL • (z : ℂ̂) = if z = 0 then ∞ else ((z⁻¹ : ℂ) : ℂ̂) := by
  have hmat : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
  rw [OnePoint.smul_some_eq_ite, hmat]
  simp [one_div]

/-- The inversion sends `∞ ↦ 0`. -/
theorem inversionGL_smul_infty : inversionGL • (∞ : ℂ̂) = ((0 : ℂ) : ℂ̂) := by
  have hmat : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
  rw [OnePoint.smul_infty_eq_ite, hmat]
  norm_num

/-- On the source of the infinity chart, the inversion recovers a sphere point
from its `chartInftyMap` coordinate. -/
theorem inversionGL_smul_coe_chartInftyMap {z : ℂ̂} (hz : z ≠ ((0 : ℂ) : ℂ̂)) :
    inversionGL • ((chartInftyMap z : ℂ) : ℂ̂) = z := by
  cases z with
  | infty =>
    have hval : chartInftyMap (∞ : ℂ̂) = 0 := rfl
    rw [hval, inversionGL_smul_coe, ite_eq_left rfl]
  | coe w =>
    have hw : w ≠ 0 := fun h => hz (OnePoint.coe_eq_coe.mpr h)
    have hval : chartInftyMap ((w : ℂ) : ℂ̂) = w⁻¹ := rfl
    rw [hval, inversionGL_smul_coe, ite_eq_right (inv_ne_zero hw), inv_inv]

/-- **Möbius transformations are continuous** on the Riemann sphere. Since the
inverse transformation is the action of `g⁻¹`, every `g • ·` is in fact a
homeomorphism of `ℂ̂`. -/
theorem continuous_gl_smul (g : GL (Fin 2) ℂ) : Continuous (fun z : ℂ̂ => g • z) := by
  -- The coercion `ℂ → ℂ̂` tends to `∞` along the cocompact filter.
  have hcoe_inf : Filter.Tendsto ((↑) : ℂ → ℂ̂) (Filter.cocompact ℂ) (nhds (∞ : ℂ̂)) := by
    rw [← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  -- Step (A): every "affine" element (lower-left entry zero) acts continuously.
  have haff : ∀ u : GL (Fin 2) ℂ, (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 →
      Continuous (fun z : ℂ̂ => u • z) := by
    intro u h10
    have hdet := u.det_ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have ha : (u : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hd : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hval_coe : ∀ x : ℂ,
        u • (x : ℂ̂) = (((u 0 0 * x + u 0 1) / u 1 1 : ℂ) : ℂ̂) := by
      intro x
      rw [OnePoint.smul_some_eq_ite, h10, zero_mul, zero_add, ite_eq_right hd]
    have hval_infty : u • (∞ : ℂ̂) = ∞ := by
      rw [OnePoint.smul_infty_eq_ite, ite_eq_left h10]
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · -- the affine map sends the cocompact filter to itself, hence `∞ ↦ ∞`.
      have hphi : Filter.Tendsto (fun x : ℂ => (u 0 0 * x + u 0 1) / u 1 1)
          (Filter.cocompact ℂ) (Filter.cocompact ℂ) := by
        rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
        have ha' : (0 : ℝ) < ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ := norm_pos_iff.mpr ha
        have hd' : (0 : ℝ) < ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ := norm_pos_iff.mpr hd
        have hnum : Filter.Tendsto (fun x : ℂ => ‖u 0 0 * x + u 0 1‖)
            (Bornology.cobounded ℂ) Filter.atTop := by
          have hlow : Filter.Tendsto (fun x : ℂ => ‖u 0 0‖ * ‖x‖ + -‖u 0 1‖)
              (Bornology.cobounded ℂ) Filter.atTop :=
            Filter.tendsto_atTop_add_const_right _ _
              (Filter.Tendsto.const_mul_atTop ha' tendsto_norm_cobounded_atTop)
          refine Filter.tendsto_atTop_mono (fun x => ?_) hlow
          have h := norm_sub_norm_le (u 0 0 * x) (-(u 0 1))
          rw [norm_neg, sub_neg_eq_add, norm_mul] at h
          linarith
        exact (hnum.atTop_div_const hd').congr fun x => (norm_div _ _).symm
      have key : Filter.Tendsto (fun x : ℂ => u • (↑x : ℂ̂)) (Filter.coclosedCompact ℂ)
          (nhds (u • (∞ : ℂ̂))) := by
        rw [hval_infty, Filter.coclosedCompact_eq_cocompact]
        exact (hcoe_inf.comp hphi).congr fun x => (hval_coe x).symm
      exact key
    · have key : Continuous (fun x : ℂ => u • (↑x : ℂ̂)) := by
        have hcont : Continuous (fun x : ℂ => (u 0 0 * x + u 0 1) / u 1 1) :=
          ((continuous_const.mul continuous_id).add continuous_const).div_const _
        exact (OnePoint.continuous_coe.comp hcont).congr fun x => (hval_coe x).symm
      exact key
  -- Step (B): the inversion acts continuously.
  have hinvcont : Continuous (fun z : ℂ̂ => inversionGL • z) := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · have key : Filter.Tendsto (fun x : ℂ => inversionGL • (↑x : ℂ̂))
          (Filter.coclosedCompact ℂ) (nhds (inversionGL • (∞ : ℂ̂))) := by
        rw [inversionGL_smul_infty, Filter.coclosedCompact_eq_cocompact]
        have hi : Filter.Tendsto (fun x : ℂ => x⁻¹) (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact Filter.tendsto_inv₀_cobounded
        have hbase : Filter.Tendsto (fun x : ℂ => ((x⁻¹ : ℂ) : ℂ̂)) (Filter.cocompact ℂ)
            (nhds (((0 : ℂ) : ℂ̂))) := (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hi
        refine hbase.congr' ?_
        have h0ne : ∀ᶠ x : ℂ in Filter.cocompact ℂ, x ≠ 0 := by
          filter_upwards [(isCompact_singleton :
            IsCompact ({0} : Set ℂ)).compl_mem_cocompact] with x hx
          simpa using hx
        filter_upwards [h0ne] with x hx
        rw [inversionGL_smul_coe, ite_eq_right hx]
      exact key
    · have key : Continuous (fun x : ℂ => inversionGL • (↑x : ℂ̂)) := by
        rw [continuous_iff_continuousAt]
        intro x₀
        by_cases hx₀ : x₀ = 0
        · subst hx₀
          have hv0 : inversionGL • ((0 : ℂ) : ℂ̂) = ∞ := by
            rw [inversionGL_smul_coe, ite_eq_left rfl]
          have hT : Filter.Tendsto (fun x : ℂ => inversionGL • (↑x : ℂ̂)) (nhds 0)
              (nhds (inversionGL • ((0 : ℂ) : ℂ̂))) := by
            rw [hv0]
            rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
            rintro K ⟨-, hKc⟩
            obtain ⟨M, hM_pos, hM⟩ := hKc.isBounded.exists_pos_norm_le
            have hev : ∀ᶠ x : ℂ in nhds 0, ‖x‖ < M⁻¹ := by
              have hn := continuous_norm.tendsto (0 : ℂ)
              rw [norm_zero] at hn
              exact hn.eventually (eventually_lt_nhds (by positivity))
            filter_upwards [hev] with x hx
            by_cases hx0 : x = 0
            · refine Set.mem_union_right _ ?_
              rw [inversionGL_smul_coe, ite_eq_left hx0]
              exact Set.mem_singleton _
            · refine Set.mem_union_left _ ?_
              rw [inversionGL_smul_coe, ite_eq_right hx0]
              refine ⟨x⁻¹, ?_, rfl⟩
              simp only [Set.mem_compl_iff]
              intro hmem
              have h1 : ‖x⁻¹‖ ≤ M := hM _ hmem
              rw [norm_inv] at h1
              have h2 : M⁻¹ ≤ ‖x‖ := inv_le_of_inv_le₀ (norm_pos_iff.mpr hx0) h1
              linarith
          exact hT
        · have hbase : ContinuousAt (fun x : ℂ => ((x⁻¹ : ℂ) : ℂ̂)) x₀ :=
            OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hx₀)
          refine hbase.congr ?_
          filter_upwards [eventually_ne_nhds hx₀] with x hx
          rw [inversionGL_smul_coe, ite_eq_right hx]
      exact key
  -- Step (C): factor a general element through the two special cases.
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · exact haff g hc
  · obtain ⟨a, b, c, d, hg⟩ : ∃ a b c d : ℂ,
        (g : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    rw [hg] at hc
    have hc' : c ≠ 0 := by simpa using hc
    have hdet := g.det_ne_zero
    rw [hg, Matrix.det_fin_two_of] at hdet
    have hbcad : b * c - a * d ≠ 0 := by
      intro h0
      apply hdet
      linear_combination -h0
    have h1det : (!![(b * c - a * d) / c, a / c; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
      exact div_ne_zero hbcad hc'
    have h2det : (!![c, d; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
      exact hc'
    obtain ⟨A1, hA1⟩ : ∃ A1 : GL (Fin 2) ℂ,
        (A1 : Matrix (Fin 2) (Fin 2) ℂ) = !![(b * c - a * d) / c, a / c; 0, 1] :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h1det, rfl⟩
    obtain ⟨A2, hA2⟩ : ∃ A2 : GL (Fin 2) ℂ,
        (A2 : Matrix (Fin 2) (Fin 2) ℂ) = !![c, d; 0, 1] :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ h2det, rfl⟩
    have hmatJ : (inversionGL : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] := rfl
    have hfact : g = A1 * inversionGL * A2 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hA1, hA2, hmatJ, hg,
        Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp
      ring
    have h1lower : (A1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA1]; simp
    have h2lower : (A2 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [hA2]; simp
    have hcomp : Continuous (fun z : ℂ̂ => A1 • (inversionGL • (A2 • z))) :=
      (haff A1 h1lower).comp (hinvcont.comp (haff A2 h2lower))
    have heq : ∀ z : ℂ̂, A1 • (inversionGL • (A2 • z)) = g • z := by
      intro z
      rw [hfact, SemigroupAction.mul_smul, SemigroupAction.mul_smul]
    exact hcomp.congr heq

/-- **Triple transitivity**: any three distinct points of `ℂ̂` can be sent to
`(0, 1, ∞)` by a Möbius transformation. -/
theorem exists_gl_smul_eq_zero_one_infty {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℂ, g • a = ((0 : ℂ) : ℂ̂) ∧ g • b = ((1 : ℂ) : ℂ̂) ∧ g • c = ∞ := by
  -- Step 1: a transformation `g₁` sending `c` to `∞`.
  obtain ⟨g₁, hg₁c⟩ : ∃ g₁ : GL (Fin 2) ℂ, g₁ • c = ∞ := by
    by_cases hc : c = ∞
    · exact ⟨1, by rw [one_smul, hc]⟩
    · obtain ⟨γ, hγ⟩ := OnePoint.ne_infty_iff_exists.mp hc
      have hdet : (!![(0 : ℂ), 1; 1, -γ]).det ≠ 0 := by
        norm_num [Matrix.det_fin_two_of]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
      have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = !![(0 : ℂ), 1; 1, -γ] := rfl
      rw [← hγ, OnePoint.smul_some_eq_ite, hcoe]
      have hcond : !![(0 : ℂ), 1; 1, -γ] 1 0 * γ + !![(0 : ℂ), 1; 1, -γ] 1 1 = 0 := by
        simp
      rw [ite_eq_left hcond]
  -- Step 2: the images of `a` and `b` under `g₁` are finite and distinct.
  have ha' : g₁ • a ≠ ∞ := fun h => hac (MulAction.injective g₁ (h.trans hg₁c.symm))
  have hb' : g₁ • b ≠ ∞ := fun h => hbc (MulAction.injective g₁ (h.trans hg₁c.symm))
  obtain ⟨α, hα⟩ := OnePoint.ne_infty_iff_exists.mp ha'
  obtain ⟨β, hβ⟩ := OnePoint.ne_infty_iff_exists.mp hb'
  have hβα : β - α ≠ 0 :=
    sub_ne_zero.mpr fun h =>
      hab (MulAction.injective g₁ (hα.symm.trans ((OnePoint.coe_eq_coe.mpr h.symm).trans hβ)))
  -- Step 3: the affine map `z ↦ (z - α) / (β - α)` as a group element `g₂`.
  have hdet₂ : (!![(1 : ℂ), -α; 0, β - α]).det ≠ 0 := by
    simpa [Matrix.det_fin_two_of] using hβα
  have hcoe₂ : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₂ : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![(1 : ℂ), -α; 0, β - α] := rfl
  set g₂ : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₂ with hg₂
  -- Step 4: `g := g₂ * g₁` does the job.
  refine ⟨g₂ * g₁, ?_, ?_, ?_⟩
  · -- `a ↦ α ↦ 0`
    rw [SemigroupAction.mul_smul, ← hα, OnePoint.smul_some_eq_ite, hcoe₂]
    have hcond : ¬(!![(1 : ℂ), -α; 0, β - α] 1 0 * α + !![(1 : ℂ), -α; 0, β - α] 1 1 = 0) := by
      simpa using hβα
    rw [ite_eq_right hcond, OnePoint.coe_eq_coe]
    simp
  · -- `b ↦ β ↦ 1`
    rw [SemigroupAction.mul_smul, ← hβ, OnePoint.smul_some_eq_ite, hcoe₂]
    have hcond : ¬(!![(1 : ℂ), -α; 0, β - α] 1 0 * β + !![(1 : ℂ), -α; 0, β - α] 1 1 = 0) := by
      simpa using hβα
    rw [ite_eq_right hcond, OnePoint.coe_eq_coe]
    have : !![(1 : ℂ), -α; 0, β - α] 1 0 * β + !![(1 : ℂ), -α; 0, β - α] 1 1 = β - α := by
      simp [sub_eq_add_neg]
    rw [this]
    have : !![(1 : ℂ), -α; 0, β - α] 0 0 * β + !![(1 : ℂ), -α; 0, β - α] 0 1 = β - α := by
      simp [sub_eq_add_neg]
    rw [this, div_self hβα]
  · -- `c ↦ ∞ ↦ ∞`
    rw [SemigroupAction.mul_smul, hg₁c, OnePoint.smul_infty_eq_ite]
    have hcond : ((g₂ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 : ℂ) = 0 := by
      rw [hg₂, hcoe₂]; simp
    rw [ite_eq_left hcond]

/-- A Möbius transformation with explicit coefficients, as a total map on
the sphere: `x ↦ (a·x + b)/(c·x + d)` with poles sent to `∞` and
`∞ ↦ a/c` (or `∞` when `c = 0`). Used with variable coefficients, where
the bundled group action is unavailable. -/
noncomputable def mobiusApply (a b c d : ℂ) : ℂ̂ → ℂ̂ := fun w =>
  match w with
  | (x : ℂ) =>
      if c * x + d = 0 then ∞ else (((a * x + b) / (c * x + d) : ℂ) : ℂ̂)
  | ∞ => if c = 0 then ∞ else ((a / c : ℂ) : ℂ̂)

/-- The value of `mobiusApply` at a finite point: `(a·x + b)/(c·x + d)`, with a
pole sent to `∞`. -/
theorem mobiusApply_coe (a b c d x : ℂ) :
    mobiusApply a b c d ((x : ℂ̂))
      = if c * x + d = 0 then ∞
        else (((a * x + b) / (c * x + d) : ℂ) : ℂ̂) := by
  rfl

/-- The value of `mobiusApply` at `∞`: `a/c`, or `∞` when `c = 0`. -/
theorem mobiusApply_infty (a b c d : ℂ) :
    mobiusApply a b c d (∞ : ℂ̂)
      = if c = 0 then ∞ else ((a / c : ℂ) : ℂ̂) := by
  rfl

/-- **Joint continuity of the Möbius application** in the coefficients and
the argument, on the locus of invertible coefficient matrices. The
`∞`-valued and `∞`-argument configurations reduce to the finite one through
the row-swap identity `mobiusApply a b c d = inversionGL • mobiusApply c d a b`
and the inversion parameterization of neighborhoods of `∞`. -/
theorem continuousOn_mobiusApply :
    ContinuousOn (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      {q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ |
        q.1.1 * q.1.2.2.2 - q.1.2.1 * q.1.2.2.1 ≠ 0} := by
  -- Definitional value lemmas.
  have hcoe_val : ∀ a b c d x : ℂ, mobiusApply a b c d ((x : ℂ̂))
      = if c * x + d = 0 then ∞ else (((a * x + b) / (c * x + d) : ℂ) : ℂ̂) :=
    fun _ _ _ _ _ => rfl
  have hinfty_val : ∀ a b c d : ℂ, mobiusApply a b c d (∞ : ℂ̂)
      = if c = 0 then ∞ else ((a / c : ℂ) : ℂ̂) := fun _ _ _ _ => rfl
  have hinv0 : inversionGL • ((0 : ℂ) : ℂ̂) = (∞ : ℂ̂) := by
    rw [inversionGL_smul_coe, ite_eq_left rfl]
  -- (I) Row swap: on the determinant locus,
  -- `mobiusApply a b c d = inversionGL • mobiusApply c d a b`.
  have hrow : ∀ a b c d : ℂ, a * d - b * c ≠ 0 → ∀ w : ℂ̂,
      mobiusApply a b c d w = inversionGL • mobiusApply c d a b w := by
    intro a b c d hdet w
    cases w with
    | coe x =>
      rw [hcoe_val, hcoe_val]
      by_cases hcd : c * x + d = 0
      · have hab : a * x + b ≠ 0 := fun h => hdet (by linear_combination a * hcd - c * h)
        rw [ite_eq_left hcd, ite_eq_right hab, inversionGL_smul_coe, hcd, zero_div, ite_eq_left rfl]
      · by_cases hab : a * x + b = 0
        · rw [ite_eq_right hcd, ite_eq_left hab, inversionGL_smul_infty, hab, zero_div]
        · rw [ite_eq_right hcd, ite_eq_right hab, inversionGL_smul_coe,
            ite_eq_right (div_ne_zero hcd hab), inv_div]
    | infty =>
      rw [hinfty_val, hinfty_val]
      by_cases hc : c = 0
      · have ha : a ≠ 0 := fun h => hdet (by rw [h, hc]; ring)
        rw [ite_eq_left hc, ite_eq_right ha, inversionGL_smul_coe, hc, zero_div, ite_eq_left rfl]
      · by_cases ha : a = 0
        · rw [ite_eq_right hc, ite_eq_left ha, inversionGL_smul_infty, ha, zero_div]
        · rw [ite_eq_right hc, ite_eq_right ha, inversionGL_smul_coe,
            ite_eq_right (div_ne_zero hc ha), inv_div]
  -- (II) Column swap through the inversion parameterization of `∞`.
  have hcol : ∀ a b c d t : ℂ,
      mobiusApply a b c d (inversionGL • (t : ℂ̂)) = mobiusApply b a d c ((t : ℂ̂)) := by
    intro a b c d t
    by_cases ht : t = 0
    · subst ht
      rw [hinv0, hinfty_val, hcoe_val]
      norm_num
    · rw [inversionGL_smul_coe, ite_eq_right ht, hcoe_val, hcoe_val]
      by_cases hdc : d * t + c = 0
      · have h1 : c * t⁻¹ + d = 0 := by
          field_simp
          linear_combination hdc
        rw [ite_eq_left h1, ite_eq_left hdc]
      · have h1 : c * t⁻¹ + d ≠ 0 := by
          intro h
          apply hdc
          field_simp at h
          linear_combination h
        rw [ite_eq_right h1, ite_eq_right hdc, OnePoint.coe_eq_coe, div_eq_div_iff h1 hdc]
        field_simp
        ring
  -- Neighborhood transport along the finite-chart parameterization.
  have hφmap : ∀ (p : ℂ × ℂ × ℂ × ℂ) (x : ℂ),
      Filter.map (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => (q.1, (q.2 : ℂ̂))) (𝓝 (p, x))
        = 𝓝 (p, (x : ℂ̂)) :=
    fun p x => (IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe).map_nhds_eq (p, x)
  -- The inversion parameterization `t ↦ inversionGL • ↑t` is an open embedding.
  have hoeψ : IsOpenEmbedding (fun t : ℂ => inversionGL • (t : ℂ̂)) := by
    have hJJ : inversionGL * inversionGL = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [inversionGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.mul_apply, Fin.sum_univ_two]
    have hinvol : ∀ z : ℂ̂, inversionGL • inversionGL • z = z := by
      intro z
      rw [← SemigroupAction.mul_smul, hJJ, one_smul]
    exact (Homeomorph.isOpenEmbedding
      ⟨⟨fun z => inversionGL • z, fun z => inversionGL • z, hinvol, hinvol⟩,
        continuous_gl_smul _, continuous_gl_smul _⟩).comp OnePoint.isOpenEmbedding_coe
  -- Neighborhood transport onto `𝓝 (p, ∞)` along the inversion parameterization.
  have hΘ : ∀ p : ℂ × ℂ × ℂ × ℂ,
      Filter.map (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => (q.1, inversionGL • (q.2 : ℂ̂)))
        (𝓝 (p, (0 : ℂ))) = 𝓝 (p, (∞ : ℂ̂)) := by
    intro p
    have h2 : (p, inversionGL • ((0 : ℂ) : ℂ̂)) = (p, (∞ : ℂ̂)) := by rw [hinv0]
    exact ((IsOpenEmbedding.id.prodMap hoeψ).map_nhds_eq (p, (0 : ℂ))).trans
      (congrArg nhds h2)
  -- Base case: joint continuity at a finite argument with nonvanishing denominator.
  have hbase : ∀ (p : ℂ × ℂ × ℂ × ℂ) (x : ℂ), p.2.2.1 * x + p.2.2.2 ≠ 0 →
      ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (p, (x : ℂ̂)) := by
    intro p x hden
    have hcnum : Continuous (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ => q.1.1 * q.2 + q.1.2.1) :=
      (continuous_fst.fst.mul continuous_snd).add continuous_fst.snd.fst
    have hcden : Continuous (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        q.1.2.2.1 * q.2 + q.1.2.2.2) :=
      (continuous_fst.snd.snd.fst.mul continuous_snd).add continuous_fst.snd.snd.snd
    have hev : ∀ᶠ q : (ℂ × ℂ × ℂ × ℂ) × ℂ in 𝓝 (p, x),
        q.1.2.2.1 * q.2 + q.1.2.2.2 ≠ 0 := hcden.continuousAt.eventually_ne hden
    have hg : ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        (((q.1.1 * q.2 + q.1.2.1) / (q.1.2.2.1 * q.2 + q.1.2.2.2) : ℂ) : ℂ̂)) (p, x) :=
      OnePoint.continuous_coe.continuousAt.comp
        (hcnum.continuousAt.div hcden.continuousAt hden)
    have key : Filter.Tendsto (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 ((q.2 : ℂ̂))) (𝓝 (p, x))
        (𝓝 (mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 ((x : ℂ̂)))) := by
      have hvx : mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 ((x : ℂ̂))
          = (((p.1 * x + p.2.1) / (p.2.2.1 * x + p.2.2.2) : ℂ) : ℂ̂) := by
        rw [hcoe_val, ite_eq_right hden]
      rw [hvx]
      refine Filter.Tendsto.congr' ?_ hg.tendsto
      filter_upwards [hev] with q hq
      simp only [hcoe_val, ite_eq_right hq]
    have hfin : Filter.Tendsto (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (𝓝 (p, (x : ℂ̂)))
        (𝓝 (mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 ((x : ℂ̂)))) := by
      rw [← hφmap p x, Filter.tendsto_map'_iff]
      exact key
    exact hfin
  -- Continuity at `∞`-argument points whose lower-left coefficient is nonzero.
  have hbaseInf : ∀ p : ℂ × ℂ × ℂ × ℂ, p.2.2.1 ≠ 0 →
      ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (p, (∞ : ℂ̂)) := by
    intro p hc
    have hτ : Continuous (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        (((q.1.2.1, q.1.1, q.1.2.2.2, q.1.2.2.1) : ℂ × ℂ × ℂ × ℂ), (q.2 : ℂ̂))) :=
      (continuous_fst.snd.fst.prodMk (continuous_fst.fst.prodMk
        (continuous_fst.snd.snd.snd.prodMk continuous_fst.snd.snd.fst))).prodMk
        (OnePoint.continuous_coe.comp continuous_snd)
    have hFτ : ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mobiusApply q.1.2.1 q.1.1 q.1.2.2.2 q.1.2.2.1 ((q.2 : ℂ̂))) (p, (0 : ℂ)) :=
      ContinuousAt.comp (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
          (((q.1.2.1, q.1.1, q.1.2.2.2, q.1.2.2.1) : ℂ × ℂ × ℂ × ℂ), (q.2 : ℂ̂)))
        (x := (p, (0 : ℂ)))
        (hbase (p.2.1, p.1, p.2.2.2, p.2.2.1) 0 (by simpa using hc)) hτ.continuousAt
    have hvals : mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 (∞ : ℂ̂)
        = mobiusApply p.2.1 p.1 p.2.2.2 p.2.2.1 (((0 : ℂ) : ℂ̂)) := by
      rw [← hinv0]
      exact hcol p.1 p.2.1 p.2.2.1 p.2.2.2 0
    have key : Filter.Tendsto (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 (inversionGL • (q.2 : ℂ̂)))
        (𝓝 (p, (0 : ℂ))) (𝓝 (mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 (∞ : ℂ̂))) := by
      rw [hvals]
      refine Filter.Tendsto.congr' ?_ hFτ.tendsto
      exact Filter.Eventually.of_forall fun q =>
        (hcol q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2).symm
    have hfin : Filter.Tendsto (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (𝓝 (p, (∞ : ℂ̂)))
        (𝓝 (mobiusApply p.1 p.2.1 p.2.2.1 p.2.2.2 (∞ : ℂ̂))) := by
      rw [← hΘ p, Filter.tendsto_map'_iff]
      exact key
    exact hfin
  -- Reduction along the row swap: within-continuity at a point follows from
  -- continuity of the swapped application at the swapped coefficients.
  have hswap : ∀ (a b c d : ℂ) (w : ℂ̂), a * d - b * c ≠ 0 →
      ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) ((c, d, a, b), w) →
      ContinuousWithinAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
          mobiusApply q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
        {q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ |
          q.1.1 * q.1.2.2.2 - q.1.2.1 * q.1.2.2.1 ≠ 0} ((a, b, c, d), w) := by
    intro a b c d w hdet hcont
    have hσ : Continuous (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        (((q.1.2.2.1, q.1.2.2.2, q.1.1, q.1.2.1) : ℂ × ℂ × ℂ × ℂ), q.2)) :=
      (continuous_fst.snd.snd.fst.prodMk (continuous_fst.snd.snd.snd.prodMk
        (continuous_fst.fst.prodMk continuous_fst.snd.fst))).prodMk continuous_snd
    have hinner : ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        mobiusApply q.1.2.2.1 q.1.2.2.2 q.1.1 q.1.2.1 q.2) ((a, b, c, d), w) :=
      ContinuousAt.comp (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
          (((q.1.2.2.1, q.1.2.2.2, q.1.1, q.1.2.1) : ℂ × ℂ × ℂ × ℂ), q.2))
        (x := ((a, b, c, d), w)) hcont hσ.continuousAt
    have hG : ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ℂ̂ =>
        inversionGL • mobiusApply q.1.2.2.1 q.1.2.2.2 q.1.1 q.1.2.1 q.2)
        ((a, b, c, d), w) :=
      (continuous_gl_smul inversionGL).continuousAt.comp hinner
    refine hG.continuousWithinAt.congr (fun y hy => ?_) ?_
    · exact hrow y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 hy y.2
    · exact hrow a b c d hdet w
  -- Assembly: case analysis on the argument and the relevant coefficient.
  intro q hq
  obtain ⟨⟨a, b, c, d⟩, w⟩ := q
  simp only [Set.mem_ofPred_eq] at hq
  cases w with
  | coe x =>
    by_cases hcd : c * x + d = 0
    · refine hswap a b c d ((x : ℂ̂)) hq (hbase (c, d, a, b) x ?_)
      change a * x + b ≠ 0
      exact fun h => hq (by linear_combination a * hcd - c * h)
    · exact (hbase (a, b, c, d) x hcd).continuousWithinAt
  | infty =>
    by_cases hc : c = 0
    · refine hswap a b c d (∞ : ℂ̂) hq (hbaseInf (c, d, a, b) ?_)
      change a ≠ 0
      exact fun h => hq (by rw [h, hc]; ring)
    · exact (hbaseInf (a, b, c, d) hc).continuousWithinAt

end RiemannDynamics
