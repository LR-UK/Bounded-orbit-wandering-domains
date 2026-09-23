import FunctionTheory.Conformal.SmoothForwardCoordinate
import FunctionTheory.Analytic.FinitePreimageStability

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- A finite-composition approximation bound supplies a smooth forward
coordinate with a prescribed target support and C^m budget. The original
source collar is the inverse image of that target collar. -/
theorem exists_smooth_forward_prefix_tolerance
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {X V C : Set ℂ} (hX : IsCompact X) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hXV : Θ '' X ⊆ V) (hCX : C ⊆ Θ '' X)
    (e : OpenPartialHomeomorph ℂ ℂ) (hVe : closure V ⊆ e.target)
    (hei : AnalyticOnNhd ℂ e.symm e.target)
    (g : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (N : ℕ)
    (he : (e : ℂ → ℂ)=finiteComposition g N)
    (hU : ∀ k<N, IsOpen (U k)) (hg : ∀ k<N, AnalyticOnNhd ℂ (g k) (U k))
    (horbit : ∀ k<N, MapsTo (finiteComposition g k) (e.symm '' closure V) (U k))
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0, ∀ f : ℕ → ℂ → ℂ,
      (∀ k<N, AnalyticOnNhd ℂ (f k) (U k)) →
      (∀ k<N, ∀ z∈U k, dist (f k z) (g k z)≤δ) →
      (∀ c∈C, finiteComposition f N (e.symm c)=c) →
      ∃ E : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (E : ℂ → ℂ) ∧ ContDiff ℝ ∞ (E.symm : ℂ → ℂ) ∧
        (∀ z∈Θ '' X, (E : ℂ → ℂ) =ᶠ[𝓝 z] (finiteComposition f N ∘ e.symm)) ∧
        EqOn (E : ℂ → ℂ) id C ∧ (∀ z∉V, E z=z) ∧
        HasCompactSupport (fun z => E z-z) ∧ tsupport (fun z => E z-z) ⊆ V ∧
        finiteSmoothNormOn m (fun z => E (Θ z)-Θ z) univ<ENNReal.ofReal ε := by
  obtain ⟨η,hη,Hη⟩ := exists_smooth_forward_coordinate_tolerance Θ m hΘ hX hV hXV hCX e
    (subset_closure.trans hVe) hei hε
  have hL : IsCompact (e.symm '' closure V) :=
    hVc.image_of_continuousOn (e.continuousOn_symm.mono hVe)
  obtain ⟨ρ,hρ,Hρ⟩ := finiteComposition_approximation_on_compact g U (e.symm '' closure V) hL N hU
    (fun k hk => (hg k hk).continuousOn) horbit η hη
  refine ⟨ρ/2,half_pos hρ,?_⟩
  intro f hf hclose hmarks
  obtain ⟨Hdist,Hdom⟩ := Hρ f (fun k hk z hz => (hclose k hk z hz).trans_lt (half_lt_self hρ))
  apply Hη (finiteComposition f N) _ _ hmarks
  · intro z hz
    exact analyticAt_finiteComposition f N
      (fun k hk => hf k hk _ (Hdom k hk (image_mono subset_closure hz)))
  · intro z hz
    rw [he]
    simpa only [dist_eq_norm] using (Hdist N le_rfl z (image_mono subset_closure hz)).le

end FunctionTheory
