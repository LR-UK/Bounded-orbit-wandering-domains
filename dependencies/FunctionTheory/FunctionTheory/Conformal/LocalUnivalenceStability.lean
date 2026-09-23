import FunctionTheory.Conformal.CompactLocalInjectivity
import FunctionTheory.Conformal.UnivalenceStability
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Uniform local univalence persists under sufficiently small holomorphic
perturbations near a compact set free of critical points. -/
theorem exists_uniform_injective_approximation_radius
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U) (hd : ∀ a ∈ K, deriv φ a ≠ 0) :
    ∃ r > 0, ∃ δ > 0,
      (∀ a ∈ K, ball a r ⊆ U ∧ InjOn φ (ball a r)) ∧
      ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
        (∀ z ∈ U, ‖φ z - g z‖ < δ) → ∀ a ∈ K, InjOn g (ball a r) := by
  classical
  obtain ⟨R, hR, HR⟩ := exists_uniform_injective_radius_of_deriv_ne_zero hU hK hKU hφ hd
  have hlocal : ∀ b : K, ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖φ z - g z‖ < δ) → InjOn g (closedBall (b : ℂ) (R / 2)) := by
    intro b
    have hφb := hφ.differentiableOn.mono (HR b b.property).1
    let e := hφb.toOpenPartialHomeomorph isOpen_ball (HR b b.property).2
    have heS : e.source = ball (b : ℂ) R := rfl
    have heval : (e : ℂ → ℂ) = φ := rfl
    have he : DifferentiableOn ℂ e e.source := by simpa only [heS, heval] using hφb
    have hei := TauCeti.OpenPartialHomeomorph.differentiableOn_symm he
    obtain ⟨δ, hδ, H⟩ := exists_injective_approximation_tolerance e hei
      (closedBall (b : ℂ) (R / 2)) (isCompact_closedBall _ _)
      (by simpa only [heS] using closedBall_subset_ball (half_lt_self hR))
    refine ⟨δ, hδ, ?_⟩
    intro g hg hclose
    apply (H g (by simpa only [heS] using hg.differentiableOn.mono (HR b b.property).1) ?_).1
    intro z hz
    have hzU := (HR b b.property).1 (show z ∈ ball (b : ℂ) R from hz)
    simpa only [heval, dist_eq_norm, norm_sub_rev] using (hclose z hzU).le
  choose d hdpos hstable using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b : K => ball (b : ℂ) (R / 4))
    (fun _ => isOpen_ball) (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, mem_ball_self (by positivity)⟩)
  have hsmall : ∃ δ > 0, ∀ b ∈ t, δ < d b := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a t ha ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min δ (d a / 2), lt_min hδ (half_pos (hdpos a)), ?_⟩
      intro b hbmem
      rcases Finset.mem_insert.mp hbmem with rfl | hbmem
      · exact (min_le_right _ _).trans_lt (half_lt_self (hdpos b))
      · exact (min_le_left _ _).trans_lt (hb b hbmem)
  obtain ⟨δ, hδ, hsmall⟩ := hsmall
  refine ⟨R / 4, by positivity, δ, hδ, ?_, ?_⟩
  · intro a ha
    have hsub : ball a (R / 4) ⊆ ball a R := ball_subset_ball (by linarith)
    exact ⟨hsub.trans (HR a ha).1, (HR a ha).2.mono hsub⟩
  · intro g hg hclose a ha
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht ha)
    have hinj := hstable b g hg (fun z hz => (hclose z hz).trans (hsmall b hb))
    apply hinj.mono
    intro z hz
    exact ((dist_triangle z a b).trans_lt (by
      have h₁ := mem_ball.mp hz
      have h₂ := mem_ball.mp hab
      linarith)).le

end FunctionTheory
