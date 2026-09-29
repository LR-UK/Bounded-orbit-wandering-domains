module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

public import EremenkoLyubichConstant.ExteriorPowerCover

@[expose] public section

open Function Set
open scoped Topology

namespace EremenkoLyubichConstant

/-- A subgroup of an infinite cyclic group is specified by a nonnegative divisibility degree. -/
theorem exists_degree_of_cyclic_subgroup
    {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (H : Subgroup G) :
    ∃ d : ℕ, ∀ γ : G, γ ∈ H ↔ (d : ℤ) ∣ (e γ).toAdd := by
  let S : AddSubgroup ℤ :=
    { carrier := {n | e.symm (Multiplicative.ofAdd n) ∈ H}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change e.symm (Multiplicative.ofAdd a * Multiplicative.ofAdd b) ∈ H
        rw [map_mul]
        exact H.mul_mem ha hb
      neg_mem' := by
        intro a ha
        change e.symm ((Multiplicative.ofAdd a)⁻¹) ∈ H
        rw [map_inv]
        exact H.inv_mem ha }
  have htop : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by ext n; simp
  obtain ⟨a, ha⟩ := AddSubgroup.exists_zmultiples_eq_of_zmultiples_eq_top htop S
  have heq : AddSubgroup.zmultiples (a.natAbs : ℤ) = S := by
    simpa using (Int.zmultiples_natAbs a).trans (by simpa using ha)
  refine ⟨a.natAbs, fun γ ↦ ?_⟩
  have hh : (e γ).toAdd ∈ S ↔ γ ∈ H := by simp [S]
  rw [← hh, ← heq, Int.mem_zmultiples_iff]

/-- Equality of covering subgroups at one common basepoint determines a connected cover. -/
theorem exists_homeomorph_of_covering_subgroups_at
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    {p : E → X} {q : F → X} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e₀ : E) (f₀ : F) {x : X} (he : p e₀ = x) (hf : q f₀ = x)
    (heq : (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range =
      (FundamentalGroup.mapOfEq ⟨q, hq.continuous⟩ hf).range) :
    ∃ h : E ≃ₜ F, h e₀ = f₀ ∧ q ∘ h = p := by
  have hh := congrArg (Subgroup.map (FundamentalGroup.castEquiv he.symm).toMonoidHom) heq
  rw [← MonoidHom.range_comp, ← MonoidHom.range_comp,
    FundamentalGroup.castEquiv_comp_mapOfEq, FundamentalGroup.castEquiv_comp_mapOfEq,
    FundamentalGroup.mapOfEq_rfl] at hh
  apply exists_homeomorph_of_covering_subgroups hp hq e₀ f₀ (he.trans hf.symm) hh.le
  exact (FundamentalGroup.range_mapOfEq_le_iff ⟨p, hp.continuous⟩ ⟨q, hq.continuous⟩
    e₀ f₀ (hf.trans he.symm)).mp hh.ge

open ExteriorFundamentalGroup ExteriorPowerCover

set_option backward.isDefEq.respectTransparency false in
/-- A connected exterior-disk cover has trivial covering subgroup or is a positive power cover.
This is the covering classification needed for the tract theorem. -/
theorem exterior_covering_dichotomy
    {E : Type*} [TopologicalSpace E] [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {ρ : ℝ} {p : E → exponentialExterior ρ} (hp : IsCoveringMap p) (e₀ : E) :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range = ⊥ ∨
      ∃ (d : ℕ) (hd : 0 < d) (h : E ≃ₜ exponentialExterior (ρ / d)),
        powerCover ρ d hd ∘ h = p := by
  obtain ⟨w, hw⟩ := (isAddQuotientCoveringMap_expCover ρ).surjective (p e₀)
  let P := FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hw.symm
  let e := fundamentalGroupEquivInt ρ w
  obtain ⟨d, hd⟩ := exists_degree_of_cyclic_subgroup e P.range
  by_cases hd0 : d = 0
  · left
    apply le_antisymm _ bot_le
    rintro γ ⟨a, rfl⟩
    rw [Subgroup.mem_bot]
    have ha := (hd (P a)).mp (show P a ∈ P.range from ⟨a, rfl⟩)
    simp only [hd0, Nat.cast_zero, zero_dvd_iff] at ha
    have hone : P a = 1 := e.injective (by
      rw [map_one]
      exact congrArg Multiplicative.ofAdd ha)
    have hcast : FundamentalGroup.castEquiv hw (P a) = 1 := by rw [hone, map_one]
    rw [FundamentalGroup.map_apply]
    simpa [P, FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply] using hcast
  · right
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hq := isCoveringMap_powerCover ρ d hdpos
    have hW : IsOpen (exponentialExterior (ρ / d)) := isOpen_lt continuous_const continuous_norm
    let : LocallyPathConnectedSpace (exponentialExterior (ρ / d)) := hW.locallyPathConnectedSpace
    let : ContractibleSpace (rightHalfPlane (ρ / d)) :=
      (show Convex ℝ (rightHalfPlane (ρ / d)) from by
        simpa [rightHalfPlane] using convex_halfSpace_re_gt (ρ / d)).contractibleSpace
          ⟨(ρ / d + 1 : ℝ), by simp [rightHalfPlane]⟩
    let : PathConnectedSpace (exponentialExterior (ρ / d)) := by
      apply pathConnectedSpace_iff_univ.mpr
      rw [← (isAddQuotientCoveringMap_expCover (ρ / d)).surjective.range_eq]
      exact isPathConnected_range (isCoveringMap_exp_rightHalfPlane (ρ / d)).continuous
    obtain ⟨h, _, hh⟩ := exists_homeomorph_of_covering_subgroups_at hp hq e₀
      (expCover (ρ / d) (divideLift ρ d hdpos w)) hw.symm
      (powerCover_basepoint ρ d hdpos w) (by
        ext γ
        exact (hd γ).trans (mem_range_powerCover_iff ρ d hdpos w γ).symm)
    exact ⟨d, hdpos, h, hh⟩

end EremenkoLyubichConstant
