import FunctionTheory.Smooth.CutoffBounds
import FunctionTheory.Smooth.NearIdentitySmooth
import FunctionTheory.Smooth.Cutoff
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff NNReal

namespace FunctionTheory

set_option autoImplicit false

/-- A fixed cutoff turns sufficiently small smooth local displacements into
global smooth diffeomorphisms, with a uniform bound in every order up to m.
The zeroth derivative is included, and m ≥ 1 supplies global invertibility. -/
theorem exists_controlled_cutoff_diffeomorphism
    {U : Set ℂ} (hU : IsOpen U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (m : ℕ) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℂ → ℂ, ContDiffOn ℝ ∞ θ U →
      (∀ n ≤ m, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ n (fun w => θ w - w) z‖ ≤ δ) →
      ∃ e : ℂ ≃ₜ ℂ,
        (∀ z, e z = z + χ z • (θ z - z)) ∧
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        ∀ n ≤ m, ∀ z,
          ‖iteratedFDeriv ℝ n (fun w => e w - w) z‖ < ε := by
  obtain ⟨M, hM, HM⟩ := exists_uniform_cutoff_derivative_bound hU hχ hχc hχU m
  let b : ℝ := min (1 / 2) (ε / 2)
  have hb : 0 < b := lt_min (by norm_num) (half_pos hε)
  let δ := b / M
  have hδ : 0 < δ := div_pos hb hM
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ Hθ
  let g : ℂ → ℂ := fun z => θ z - z
  let u : ℂ → ℂ := fun z => χ z • g z
  have hg : ContDiffOn ℝ ∞ g U := hθ.sub contDiffOn_id
  have hu : ContDiff ℝ ∞ u := contDiff_cutoff_smul hU hχ hχU hg
  have Hb : ∀ n ≤ m, ∀ z, ‖iteratedFDeriv ℝ n u z‖ ≤ b := by
    intro n hn z
    have H := HM g hg δ hδ.le Hθ n hn z
    have hMδ : M * δ = b := by dsimp [δ]; field_simp
    rwa [hMδ] at H
  have Hd : ∀ z, ‖fderiv ℝ u z‖ ≤ (1 / 2 : ℝ≥0) := by
    intro z
    have H := (Hb 1 hm z).trans (min_le_left (1 / 2 : ℝ) (ε / 2))
    simpa only [norm_iteratedFDeriv_one, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat] using H
  obtain ⟨e, he, heSmooth, heInv⟩ :=
    exists_smooth_homeomorph_eq_add_of_derivative_bound hu
      (k := (1 / 2 : ℝ≥0)) (by norm_num) Hd
  refine ⟨e, he, heSmooth, heInv, ?_⟩
  have heDiff : (fun w => e w - w) = u := by
    funext w
    rw [he w]
    abel
  intro n hn z
  rw [heDiff]
  exact (Hb n hn z).trans_lt ((min_le_right (1 / 2 : ℝ) (ε / 2)).trans_lt
    (half_lt_self hε))

/-- A smooth local map sufficiently close to the identity in orders 0,…,m
extends near a compact set to a global smooth diffeomorphism equal to the
identity outside the prescribed open neighbourhood. No separate local
injectivity assumption is needed at this smallness scale. -/
theorem exists_controlled_smooth_extension
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (m : ℕ) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℂ → ℂ, ContDiffOn ℝ ∞ θ U →
      (∀ n ≤ m, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ n (fun w => θ w - w) z‖ ≤ δ) →
      ∃ e : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        (∀ z ∈ K, (e : ℂ → ℂ) =ᶠ[𝓝 z] θ) ∧
        (∀ z ∉ U, e z = z) ∧
        HasCompactSupport (fun z => e z - z) ∧
        tsupport (fun z => e z - z) ⊆ U ∧
        ∀ n ≤ m, ∀ z,
          ‖iteratedFDeriv ℝ n (fun w => e w - w) z‖ < ε := by
  obtain ⟨χ, hχ, hχc, hχU, hχK⟩ := exists_smooth_cutoff K U hK hU hKU
  obtain ⟨δ, hδ, Hδ⟩ := exists_controlled_cutoff_diffeomorphism
    hU hχ hχc hχU m hm hε
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ Hθ
  obtain ⟨e, he, hes, hei, heBound⟩ := Hδ θ hθ Hθ
  have heDiff : (fun w => e w - w) = (fun w => χ w • (θ w - w)) := by
    funext w
    rw [he w]
    abel
  have hsupp : tsupport (fun w => e w - w) ⊆ tsupport χ := by
    rw [heDiff]
    apply closure_mono
    intro z hz
    by_contra h
    have H : χ z = 0 := notMem_support.mp h
    exact hz (by simp [H])
  refine ⟨e, hes, hei, ?_, ?_, ?_, hsupp.trans hχU, heBound⟩
  · intro z hz
    filter_upwards [hχK z hz] with w hw
    rw [he w, hw, one_smul]
    abel
  · intro z hz
    have H : χ z = 0 := notMem_support.mp (fun h => hz (hχU (subset_closure h)))
    simp [he z, H]
  · rw [heDiff]
    exact hχc.smul_right

end FunctionTheory
