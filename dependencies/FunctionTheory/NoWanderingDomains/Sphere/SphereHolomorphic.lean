/- Adaptation: preserved declarations from 0a6497b0cc9ed39a6a705bf013449635894b56d0; explicit Mathlib imports for Lean 4.34. -/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Sphere.Basic
import NoWanderingDomains.Sphere.MobiusAction

/-!
# Sphere-valued holomorphic maps

A map `f : ℂ → ℂ̂` is *sphere-holomorphic* on a set `U ⊆ ℂ` if near every
point of `U` it reads as a holomorphic function in one of the two standard
charts of `ℂ̂`: either `f` avoids `∞` on a neighborhood and its finite-chart
reading `chartFiniteMap ∘ f` is holomorphic there, or `f` avoids `0` and its
infinity-chart reading `chartInftyMap ∘ f` (the chart `z ↦ 1/z`) is
holomorphic there. This is the concrete chart-local notion of a holomorphic
map into the Riemann sphere — equivalently, of a meromorphic function on `U`
with poles read honestly as the value `∞`.

The local neighborhoods are required to be open subsets of `U`, so the
predicate forces `U` to be open (`SphereHolomorphicOn.isOpen`).

## Main definitions

* `SphereHolomorphicOn` — the predicate that a map `f : ℂ → ℂ̂` is
  sphere-holomorphic on a set `U ⊆ ℂ`.

## Main results

* `DifferentiableOn.sphereHolomorphicOn` : coercions of holomorphic functions
  are sphere-holomorphic;
* `SphereHolomorphicOn.continuousOn` : sphere-holomorphic maps are continuous;
* `SphereHolomorphicOn.differentiableOn_chartFiniteMap` : a sphere-holomorphic
  map omitting `∞` is an honest holomorphic function;
* `SphereHolomorphicOn.gl_smul` : sphere-holomorphy is preserved by
  post-composition with Möbius transformations.
-/

open OnePoint Matrix

namespace NoWanderingDomains

/-- A map `f : ℂ → ℂ̂` is *sphere-holomorphic* on `U` if near every point of
`U` it reads as a holomorphic function in one of the two standard charts of
the Riemann sphere. -/
def SphereHolomorphicOn (f : ℂ → ℂ̂) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∃ V, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
    (((∀ w ∈ V, f w ≠ ∞) ∧
        DifferentiableOn ℂ (fun w => chartFiniteMap (f w)) V) ∨
      ((∀ w ∈ V, f w ≠ ((0 : ℂ) : ℂ̂)) ∧
        DifferentiableOn ℂ (fun w => chartInftyMap (f w)) V))

/-- The domain of a sphere-holomorphic map is open. -/
theorem SphereHolomorphicOn.isOpen {f : ℂ → ℂ̂} {U : Set ℂ}
    (hf : SphereHolomorphicOn f U) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨V, hVo, hzV, hVU, -⟩ := hf z hz
  exact ⟨V, hVU, hVo, hzV⟩

/-- Sphere-holomorphy only depends on the restriction of the map to `U`. -/
theorem SphereHolomorphicOn.congr {f₁ f₂ : ℂ → ℂ̂} {U : Set ℂ}
    (hf : SphereHolomorphicOn f₁ U) (h : Set.EqOn f₁ f₂ U) :
    SphereHolomorphicOn f₂ U := by
  intro z hz
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hf z hz
  refine ⟨V, hVo, hzV, hVU, ?_⟩
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · refine Or.inl ⟨fun w hw => ?_, hdiff.congr fun w hw => ?_⟩
    · rw [← h (hVU hw)]
      exact hne w hw
    · exact congrArg chartFiniteMap (h (hVU hw)).symm
  · refine Or.inr ⟨fun w hw => ?_, hdiff.congr fun w hw => ?_⟩
    · rw [← h (hVU hw)]
      exact hne w hw
    · exact congrArg chartInftyMap (h (hVU hw)).symm

/-- The coercion of a holomorphic function to the Riemann sphere is
sphere-holomorphic. -/
theorem DifferentiableOn.sphereHolomorphicOn {h : ℂ → ℂ} {U : Set ℂ}
    (hd : DifferentiableOn ℂ h U) (hU : IsOpen U) :
    SphereHolomorphicOn (fun z => ((h z : ℂ̂))) U := by
  intro z hz
  exact ⟨U, hU, hz, subset_rfl,
    Or.inl ⟨fun w _ => OnePoint.coe_ne_infty _, hd.congr fun x _ => rfl⟩⟩

/-- Sphere-holomorphic maps are continuous. -/
theorem SphereHolomorphicOn.continuousOn {f : ℂ → ℂ̂} {U : Set ℂ}
    (hf : SphereHolomorphicOn f U) : ContinuousOn f U := by
  refine continuousOn_of_forall_continuousAt fun z hz => ?_
  obtain ⟨V, hVo, hzV, -, hcase⟩ := hf z hz
  rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
  · have hco : ContinuousOn (fun w => ((chartFiniteMap (f w) : ℂ) : ℂ̂)) V :=
      OnePoint.continuous_coe.comp_continuousOn hdiff.continuousOn
    have heq : ∀ w ∈ V, f w = ((chartFiniteMap (f w) : ℂ) : ℂ̂) := by
      intro w hw
      cases hfw : f w with
      | infty => exact absurd hfw (hne w hw)
      | coe x => rfl
    exact (hco.congr heq).continuousAt (hVo.mem_nhds hzV)
  · have hco : ContinuousOn (fun w => inversionGL • ((chartInftyMap (f w) : ℂ) : ℂ̂)) V :=
      ((continuous_gl_smul inversionGL).comp OnePoint.continuous_coe).comp_continuousOn
        hdiff.continuousOn
    have heq : ∀ w ∈ V, f w = inversionGL • ((chartInftyMap (f w) : ℂ) : ℂ̂) := fun w hw =>
      (inversionGL_smul_coe_chartInftyMap (hne w hw)).symm
    exact (hco.congr heq).continuousAt (hVo.mem_nhds hzV)

/-- A sphere-holomorphic map omitting `∞` is an honest holomorphic function:
its finite-chart reading is differentiable on all of `U`. -/
theorem SphereHolomorphicOn.differentiableOn_chartFiniteMap {f : ℂ → ℂ̂}
    {U : Set ℂ} (hf : SphereHolomorphicOn f U) (hinf : ∀ z ∈ U, f z ≠ ∞) :
    DifferentiableOn ℂ (fun z => chartFiniteMap (f z)) U := by
  have cf : ∀ x : ℂ, chartFiniteMap (x : ℂ̂) = x := fun _ => rfl
  have ci : ∀ x : ℂ, chartInftyMap (x : ℂ̂) = x⁻¹ := fun _ => rfl
  refine differentiableOn_of_locally_differentiableOn fun z hz => ?_
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hf z hz
  refine ⟨V, hVo, hzV, ?_⟩
  rcases hcase with ⟨-, hdiff⟩ | ⟨hne, hdiff⟩
  · exact hdiff.mono Set.inter_subset_right
  · have hkey : ∀ w ∈ V,
        chartFiniteMap (f w) = (chartInftyMap (f w))⁻¹ ∧ chartInftyMap (f w) ≠ 0 := by
      intro w hw
      cases hfw : f w with
      | infty => exact absurd hfw (hinf w (hVU hw))
      | coe x =>
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hne w hw hfw
        refine ⟨?_, ?_⟩
        · rw [cf, ci, inv_inv]
        · rw [ci]
          exact inv_ne_zero hx0
    have hinv : DifferentiableOn ℂ (fun w => chartInftyMap (f w))⁻¹ V :=
      hdiff.inv fun w hw => (hkey w hw).2
    exact (hinv.mono Set.inter_subset_right).congr fun w hw => (hkey w hw.2).1

/-- Applying a Möbius transformation to the coercion of a holomorphic function
yields a sphere-holomorphic map. This is the chart-level computation behind
`SphereHolomorphicOn.gl_smul`: where `N • (h ·)` is finite it reads in the
finite chart as the quotient `(N₀₀ h + N₀₁) / (N₁₀ h + N₁₁)` with
non-vanishing denominator, and near a pole the infinity chart reads it as the
reciprocal quotient with non-vanishing numerator. -/
theorem sphereHolomorphicOn_gl_smul_coe {h : ℂ → ℂ} {V : Set ℂ}
    (hd : DifferentiableOn ℂ h V) (hV : IsOpen V) (N : GL (Fin 2) ℂ) :
    SphereHolomorphicOn (fun w => N • ((h w : ℂ̂))) V := by
  have cf : ∀ x : ℂ, chartFiniteMap (x : ℂ̂) = x := fun _ => rfl
  have ci : ∀ x : ℂ, chartInftyMap (x : ℂ̂) = x⁻¹ := fun _ => rfl
  have ci0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
  have hnum : DifferentiableOn ℂ
      (fun w => (N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
      V := ((differentiableOn_const _).mul hd).add (differentiableOn_const _)
  have hden : DifferentiableOn ℂ
      (fun w => (N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
      V := ((differentiableOn_const _).mul hd).add (differentiableOn_const _)
  have key : ∀ w : ℂ,
      (N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 →
      (N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0 := by
    intro w h0 h1
    refine N.det_ne_zero ?_
    rw [Matrix.det_fin_two]
    linear_combination (N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h0 -
      (N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h1
  intro z hz
  by_cases hdz :
      (N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h z + (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0
  · -- the denominator vanishes at `z`: read `N • (h ·)` in the infinity chart
    have hnz := key z hdz
    have hcont : ContinuousAt
        (fun w => (N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
        z := (hnum.differentiableAt (hV.mem_nhds hz)).continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hnz)
    refine ⟨V ∩ t, hV.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inr ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [OnePoint.smul_some_eq_ite]
      split_ifs with hdw
      · exact OnePoint.infty_ne_coe 0
      · intro hc
        exact div_ne_zero (ht_ne w hw.2) hdw (OnePoint.coe_eq_coe.mp hc)
    · have hinv : DifferentiableOn ℂ
          (fun w => ((N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w +
            (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1)⁻¹) (V ∩ t) :=
        (hnum.mono Set.inter_subset_left).inv fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => ((N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w +
              (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
            ((N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w +
              (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1)⁻¹) (V ∩ t) :=
        (hden.mono Set.inter_subset_left).mul hinv
      refine hdiv.congr fun w hw => ?_
      simp only [OnePoint.smul_some_eq_ite]
      split_ifs with hdw
      · rw [ci0, hdw, zero_mul]
      · rw [ci, inv_div, div_eq_mul_inv]
  · -- the denominator does not vanish at `z`: read `N • (h ·)` in the finite chart
    have hcont : ContinuousAt
        (fun w => (N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w + (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
        z := (hden.differentiableAt (hV.mem_nhds hz)).continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hdz)
    refine ⟨V ∩ t, hV.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inl ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [OnePoint.smul_some_eq_ite]
      rw [if_neg (ht_ne w hw.2)]
      exact OnePoint.coe_ne_infty _
    · have hinv : DifferentiableOn ℂ
          (fun w => ((N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w +
            (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1)⁻¹) (V ∩ t) :=
        (hden.mono Set.inter_subset_left).inv fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => ((N : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h w +
              (N : Matrix (Fin 2) (Fin 2) ℂ) 0 1) *
            ((N : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h w +
              (N : Matrix (Fin 2) (Fin 2) ℂ) 1 1)⁻¹) (V ∩ t) :=
        (hnum.mono Set.inter_subset_left).mul hinv
      refine hdiv.congr fun w hw => ?_
      simp only [OnePoint.smul_some_eq_ite]
      rw [if_neg (ht_ne w hw.2), cf, div_eq_mul_inv]

/-- Sphere-holomorphy is preserved by post-composition with Möbius
transformations. -/
theorem SphereHolomorphicOn.gl_smul {f : ℂ → ℂ̂} {U : Set ℂ}
    (hf : SphereHolomorphicOn f U) (g : GL (Fin 2) ℂ) :
    SphereHolomorphicOn (fun z => g • f z) U := by
  intro z hz
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hf z hz
  have hVmain : SphereHolomorphicOn (fun w => g • f w) V := by
    rcases hcase with ⟨hne, hdiff⟩ | ⟨hne, hdiff⟩
    · refine (sphereHolomorphicOn_gl_smul_coe hdiff hVo g).congr fun w hw => ?_
      change g • ((chartFiniteMap (f w) : ℂ) : ℂ̂) = g • f w
      cases hfw : f w with
      | infty => exact absurd hfw (hne w hw)
      | coe x => rfl
    · refine (sphereHolomorphicOn_gl_smul_coe hdiff hVo
        (g * inversionGL)).congr fun w hw => ?_
      change (g * inversionGL) • ((chartInftyMap (f w) : ℂ) : ℂ̂) = g • f w
      rw [SemigroupAction.mul_smul, inversionGL_smul_coe_chartInftyMap (hne w hw)]
  obtain ⟨V', hV'o, hzV', hV'V, hdisj⟩ := hVmain z hzV
  exact ⟨V', hV'o, hzV', hV'V.trans hVU, hdisj⟩

end NoWanderingDomains
