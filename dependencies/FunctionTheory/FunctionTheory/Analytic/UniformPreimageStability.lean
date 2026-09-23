import FunctionTheory.Analytic.PreimageStability

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- One tolerance works simultaneously for all base points of a compact set
and all sufficiently nearby target values. -/
theorem exists_uniform_stable_local_image
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖f z - g z‖ < δ) →
      ∀ a ∈ K, ∀ v : ℂ, ‖v - f a‖ < δ →
        ∃ z ∈ U ∩ ball a ε, g z = v := by
  classical
  have hlocal : ∀ a : K, ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖f z - g z‖ < δ) →
      ∀ v : ℂ, ‖v - f a‖ < δ → ∃ z ∈ U ∩ ball (a : ℂ) (ε / 2), g z = v := by
    intro a
    exact exists_stable_local_image hU hf (hKU a.property)
      (hnc a a.property) (half_pos hε)
  choose d hd hstable using hlocal
  have hnear : ∀ a : K, ∃ ρ > 0, ∀ z : ℂ,
      dist z a < ρ → ‖f z - f a‖ < d a / 2 := by
    intro a
    have hevent : ∀ᶠ z in 𝓝 (a : ℂ), ‖f z - f a‖ < d a / 2 := by
      simpa only [mem_ball, dist_eq_norm] using
        (hf a (hKU a.property)).continuousAt.tendsto.eventually
          (ball_mem_nhds (f a) (half_pos (hd a)))
    exact Metric.eventually_nhds_iff.mp hevent
  choose ρ hρ hnear using hnear
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : K => ball (a : ℂ) (min (ε / 2) (ρ a))) (fun _ => isOpen_ball) (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, mem_ball_self (lt_min (half_pos hε) (hρ ⟨a, ha⟩))⟩)
  have hsmall : ∃ δ > 0, ∀ a ∈ t, δ < d a / 2 := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a t ha ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min δ (d a / 4), lt_min hδ (div_pos (hd a) (by norm_num)), ?_⟩
      intro b hbmem
      rcases Finset.mem_insert.mp hbmem with rfl | hbmem
      · exact (min_le_right _ _).trans_lt (by linarith [hd b])
      · exact (min_le_left _ _).trans_lt (hb b hbmem)
  obtain ⟨δ, hδ, hsmall⟩ := hsmall
  refine ⟨δ, hδ, ?_⟩
  intro g hg hclose a ha v hv
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht ha)
  have habε : dist a (b : ℂ) < ε / 2 := (mem_ball.mp hab).trans_le (min_le_left _ _)
  have habρ : dist a (b : ℂ) < ρ b := (mem_ball.mp hab).trans_le (min_le_right _ _)
  have hvb : ‖v - f b‖ < d b :=
    (norm_sub_le_norm_sub_add_norm_sub v (f a) (f b)).trans_lt (by
      have h₁ := hnear b a habρ
      have h₂ := hsmall b hb
      linarith)
  obtain ⟨z, hz, heq⟩ := hstable b g hg
    (fun w hw => (hclose w hw).trans ((hsmall b hb).trans (half_lt_self (hd b)))) v hvb
  refine ⟨z, ⟨hz.1, ?_⟩, heq⟩
  have hba : dist (b : ℂ) a < ε / 2 := by simpa only [dist_comm] using habε
  exact (dist_triangle z b a).trans_lt (by linarith [mem_ball.mp hz.2])

end FunctionTheory
