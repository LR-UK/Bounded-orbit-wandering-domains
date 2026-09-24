/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniqueness of universal covering spaces

The lifting theorem in Mathlib gives the standard based equivalence between two simply
connected covering spaces of the same base.  This is the topological construction used for
logarithmic transforms.
-/

open Function

namespace EremenkoLyubichConstant

/-- A continuous logarithm of a holomorphic nonvanishing function is holomorphic.

This small analytic upgrade is useful because covering-space lifting naturally produces a
continuous lift.  Locally, the lift is the inverse supplied by the complex inverse function
theorem for `exp`, composed with the original holomorphic function. -/
theorem differentiableAt_of_continuousAt_exp_eq
    {F g : ℂ → ℂ} {z : ℂ}
    (hF : ContinuousAt F z) (hg : DifferentiableAt ℂ g z)
    (heq : ∀ᶠ x in nhds z, Complex.exp (F x) = g x) :
    DifferentiableAt ℂ F z := by
  let he := Complex.hasStrictDerivAt_exp (F z)
  have hne : Complex.exp (F z) ≠ 0 := Complex.exp_ne_zero _
  let L : ℂ → ℂ := he.localInverse Complex.exp (Complex.exp (F z)) (F z) hne
  have hL : DifferentiableAt ℂ L (Complex.exp (F z)) :=
    (he.to_localInverse hne).hasDerivAt.differentiableAt
  let e := (he.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph Complex.exp
  have hsource : ∀ᶠ x in nhds z,
      F x ∈ e.source :=
    hF.eventually
      (e.open_source.mem_nhds
        (he.hasStrictFDerivAt_equiv hne).mem_toOpenPartialHomeomorph_source)
  have heqz : Complex.exp (F z) = g z := heq.self_of_nhds
  have hcomp : DifferentiableAt ℂ (L ∘ g) z := by
    exact (heqz ▸ hL).comp z hg
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [heq, hsource] with x hx hs
  change F x = L (g x)
  rw [← hx]
  exact e.left_inv hs |>.symm

/-- A continuous exponential lift of a holomorphic function on an open set is holomorphic
on that set. -/
theorem differentiableOn_of_continuousOn_exp_eq
    {F g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hg : DifferentiableOn ℂ g U)
    (heq : Set.EqOn (Complex.exp ∘ F) g U) :
    DifferentiableOn ℂ F U := by
  intro z hz
  exact (differentiableAt_of_continuousAt_exp_eq
    (hF.continuousAt (hU.mem_nhds hz))
    (hg.differentiableAt (hU.mem_nhds hz))
    ((hU.eventually_mem hz).mono fun x hx ↦ heq hx)).differentiableWithinAt

/-- Two simply connected covering spaces of the same base are homeomorphic after compatible
basepoints have been selected.  The homeomorphism commutes with the covering projections. -/
theorem exists_homeomorph_of_isCoveringMap
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
    {p : E → X} {q : F → X}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e0 : E) (f0 : F) (hbase : p e0 = q f0) :
    ∃ h : E ≃ₜ F, h e0 = f0 ∧ q ∘ h = p := by
  let pc : C(E, X) := ⟨p, hp.continuous⟩
  let qc : C(F, X) := ⟨q, hq.continuous⟩
  obtain ⟨L, hL, _hLuniq⟩ :=
    hq.existsUnique_continuousMap_lifts pc e0 f0 hbase.symm
  obtain ⟨R, hR, _hRuniq⟩ :=
    hp.existsUnique_continuousMap_lifts qc f0 e0 hbase
  have hRL : R ∘ L = id := by
    refine hp.eq_of_comp_eq (R.continuous.comp L.continuous) continuous_id ?_ e0 ?_
    · funext x
      change p (R (L x)) = p x
      rw [show p (R (L x)) = q (L x) from congr_fun hR.2 (L x),
        show q (L x) = p x from congr_fun hL.2 x]
    · simp [hL.1, hR.1]
  have hLR : L ∘ R = id := by
    refine hq.eq_of_comp_eq (L.continuous.comp R.continuous) continuous_id ?_ f0 ?_
    · funext x
      change q (L (R x)) = q x
      rw [show q (L (R x)) = p (R x) from congr_fun hL.2 (R x),
        show p (R x) = q x from congr_fun hR.2 x]
    · simp [hL.1, hR.1]
  let h : E ≃ₜ F :=
    { toFun := L
      invFun := R
      left_inv := fun x ↦ congr_fun hRL x
      right_inv := fun x ↦ congr_fun hLR x
      continuous_toFun := L.continuous
      continuous_invFun := R.continuous }
  exact ⟨h, hL.1, hL.2⟩

/-- Connected covers with mutually containing fundamental-group images are equivalent.
The two inclusions are written with explicit basepoint transport. -/
theorem exists_homeomorph_of_covering_subgroups
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    {p : E → X} {q : F → X} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e0 : E) (f0 : F) (hbase : p e0 = q f0)
    (hpq : (FundamentalGroup.map ⟨p, hp.continuous⟩ e0).range ≤
      (FundamentalGroup.mapOfEq ⟨q, hq.continuous⟩ hbase.symm).range)
    (hqp : (FundamentalGroup.map ⟨q, hq.continuous⟩ f0).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hbase).range) :
    ∃ h : E ≃ₜ F, h e0 = f0 ∧ q ∘ h = p := by
  obtain ⟨L, hL, _⟩ := hq.existsUnique_continuousMap_lifts_of_range_le hbase.symm hpq
  obtain ⟨R, hR, _⟩ := hp.existsUnique_continuousMap_lifts_of_range_le hbase hqp
  have hRL : R ∘ L = id := by
    refine hp.eq_of_comp_eq (R.continuous.comp L.continuous) continuous_id ?_ e0 ?_
    · funext x
      change p (R (L x)) = p x
      rw [show p (R (L x)) = q (L x) from congr_fun hR.2 (L x),
        show q (L x) = p x from congr_fun hL.2 x]
    · simp [hL.1, hR.1]
  have hLR : L ∘ R = id := by
    refine hq.eq_of_comp_eq (L.continuous.comp R.continuous) continuous_id ?_ f0 ?_
    · funext x
      change q (L (R x)) = q x
      rw [show q (L (R x)) = p (R x) from congr_fun hL.2 (R x),
        show p (R x) = q x from congr_fun hR.2 x]
    · simp [hL.1, hR.1]
  let h : E ≃ₜ F :=
    { toFun := L
      invFun := R
      left_inv := fun x ↦ congr_fun hRL x
      right_inv := fun x ↦ congr_fun hLR x
      continuous_toFun := L.continuous
      continuous_invFun := R.continuous }
  exact ⟨h, hL.1, hL.2⟩

end EremenkoLyubichConstant
