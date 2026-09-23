import EremenkosConjecture.AmbientExtension
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Compact conformal charts with ambient extensions

The inverse function supplies a nonzero derivative. Compactness then supplies
a uniform positive lower bound, which persists under small approximation.
The resulting perturbation agrees near the compact set with a homeomorphism
of the plane whose local inverse is holomorphic.
-/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture

theorem deriv_ne_zero_of_holomorphic_inverse (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    {z : ℂ} (hz : z ∈ e.source) : deriv e z ≠ 0 := by
  have h₁ := (he.differentiableAt (e.open_source.mem_nhds hz)).hasDerivAt
  have h₂ := (hei.differentiableAt (e.open_target.mem_nhds (e.map_source hz))).hasDerivAt
  have hinv : e.symm ∘ e =ᶠ[𝓝 z] id := e.eventually_left_inverse hz
  have hcomp := (h₂.comp z h₁).congr_of_eventuallyEq hinv.symm
  have hprod := hcomp.unique (hasDerivAt_id z)
  intro hzero
  simp [hzero] at hprod

theorem exists_pos_derivative_lower_bound (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ e.source) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, η ≤ ‖deriv e z‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, zero_lt_one, by simp⟩
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne
      ((he.deriv e.open_source).continuousOn.norm.mono hKU)
    exact ⟨‖deriv e z‖, norm_pos_iff.mpr
      (deriv_ne_zero_of_holomorphic_inverse e he hei (hKU hz)), hmin⟩

theorem differentiableOn_homeomorph_inverse (H : ℂ ≃ₜ ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hH : DifferentiableOn ℂ H U)
    (hderiv : ∀ z ∈ U, deriv H z ≠ 0) :
    DifferentiableOn ℂ H.symm (H '' U) := by
  rintro w ⟨z, hz, rfl⟩
  have hz' : H.symm (H z) = z := H.symm_apply_apply z
  have hd : HasDerivAt H (deriv H z) (H.symm (H z)) :=
    hz'.symm ▸ (hH.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  exact (HasDerivAt.of_local_left_inverse H.symm.continuous.continuousAt hd
    (hderiv z hz) (Eventually.of_forall H.apply_symm_apply)).differentiableAt.differentiableWithinAt

/-- Small holomorphic perturbations retain an ambient conformal chart on an
open neighbourhood of the compact set. -/
theorem exists_ambient_conformal_approximation_tolerance
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn e H e.source)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f e.source →
      (∀ z ∈ e.source, dist (f z) (e z) ≤ δ) →
      ∃ (G : ℂ ≃ₜ ℂ) (V : Set ℂ), IsOpen V ∧ K ⊆ V ∧ V ⊆ e.source ∧
        EqOn f G V ∧ DifferentiableOn ℂ G V ∧ DifferentiableOn ℂ G.symm (G '' V) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK e.open_source hKU
  obtain ⟨η, hη, hηbound⟩ := exists_pos_derivative_lower_bound e he hei (closure V) hVc hVU
  obtain ⟨δ₁, hδ₁, H₁⟩ := exists_homeomorph_approximation_tolerance e hei H heH
    (closure V) hVc hVU
  obtain ⟨δ₂, hδ₂, H₂⟩ := exists_derivative_approximation_tolerance e.source (closure V)
    e.open_source hVc hVU (η / 2) (half_pos hη)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun f hf hclose => ?_⟩
  obtain ⟨G, hG⟩ := H₁ f hf (fun z hz => (hclose z hz).trans (min_le_left _ _))
  have hderiv := H₂ f e hf he (fun z hz => (hclose z hz).trans (min_le_right _ _))
  have hVU' : V ⊆ e.source := subset_closure.trans hVU
  have hGeq : EqOn f G V := fun z hz => hG (subset_closure hz)
  have hGhol : DifferentiableOn ℂ G V := (hf.mono hVU').congr hGeq.symm
  refine ⟨G, V, hV, hKV, hVU', hGeq, hGhol,
    differentiableOn_homeomorph_inverse G V hV hGhol ?_⟩
  intro z hz
  have hfg : f =ᶠ[𝓝 z] G := Filter.mem_of_superset (hV.mem_nhds hz) hGeq
  have hdG : deriv f z = deriv G z := hfg.deriv_eq
  intro hzero
  have Hη := hderiv z (subset_closure hz)
  rw [hdG, hzero, zero_sub, norm_neg] at Hη
  have Hη' := hηbound z (subset_closure hz)
  linarith

end EremenkosConjecture
