import FunctionTheory.Conformal.RegularCorrection
import FunctionTheory.Conformal.PowerCoordinatePerturbation
import FunctionTheory.Analytic.PowerQuotient

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- Quantitative conformal correction on a fixed power-coordinate disk.
The perturbation retains the central value and vanishes there to at least
the prescribed local degree. No covering-space or Riemann--Hurwitz theorem
is needed: the perturbation of the unit factor is absorbed into a root branch. -/
theorem exists_conformal_correction_on_power_coordinate_disk
    {φ α u : ℂ → ℂ} {c : ℂ} {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    {n : ℕ} (hn : n ≠ 0)
    (hα : AnalyticOnNhd ℂ α (closedBall c R))
    (hu : AnalyticOnNhd ℂ u (closedBall c R))
    (hu0 : ∀ z ∈ closedBall c R, u z ≠ 0)
    (hα0 : α c = 0) (hαd : ∀ z ∈ closedBall c r, deriv α z ≠ 0)
    (hφpower : ∀ z ∈ closedBall c R, φ z = φ c + α z ^ n)
    (hfactor : ∀ z ∈ closedBall c R, α z ^ n = (z - c) ^ n * u z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) →
      g c = φ c → (n : ℕ∞) ≤ analyticOrderAt (fun z => g z - g c) c →
      (∀ z ∈ closedBall c R, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ (ball c r) ∧ InjOn θ (ball c r) ∧
        MapsTo θ (ball c r) (ball c R) ∧
        DifferentiableOn ℂ (Function.invFunOn θ (ball c r)) (θ '' ball c r) ∧
        (∀ z ∈ ball c r, ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ θ c = c := by
  have hcompact : IsCompact (closure (ball c r)) := by
    simpa only [closure_ball c hr.ne'] using isCompact_closedBall c r
  have hsub : closure (ball c r) ⊆ ball c R := by
    rw [closure_ball c hr.ne']
    exact closedBall_subset_ball hrR
  obtain ⟨τ, hτ, Hregular⟩ := exists_conformal_correction_of_deriv_ne_zero
    isOpen_ball isOpen_ball hcompact hsub (hα.mono ball_subset_closedBall)
      (by simpa only [closure_ball c hr.ne'] using hαd) hε
  obtain ⟨m, hm, hlower⟩ := (isCompact_closedBall c R).exists_forall_le' hu.continuousOn.norm
    (fun z hz => norm_pos_iff.mpr (hu0 z hz))
  obtain ⟨p, hp, hupper⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c, mem_closedBall_self hR.le⟩ hα.continuousOn.norm
  obtain ⟨η, hη, Hunit⟩ := exists_close_power_coordinate_of_close_unit hn hα hu hm
    (norm_nonneg (α p)) hlower hupper hfactor hτ
  have hpow : 0 < R ^ n := pow_pos hR n
  have hquot : η * R ^ n / 2 / R ^ n < η := by
    have heq : η * R ^ n / 2 / R ^ n = η / 2 := by field_simp [hR.ne']
    rw [heq]
    exact half_lt_self hη
  refine ⟨η * R ^ n / 2, half_pos (mul_pos hη hpow), ?_⟩
  intro g hg hvalue horder hclose
  have hgsub : AnalyticOnNhd ℂ (fun z => g z - g c) (closedBall c R) :=
    hg.sub analyticOnNhd_const
  obtain ⟨v, hv, hgv⟩ := exists_analytic_power_quotient hgsub (mem_closedBall_self hR.le) horder
  have hvu : AnalyticOnNhd ℂ (fun z => v z - u z) (closedBall c R) := hv.sub hu
  have herror : ∀ z ∈ sphere c R, ‖(z - c) ^ n * (v z - u z)‖ ≤ η * R ^ n / 2 := by
    intro z hz
    have hzcl := sphere_subset_closedBall hz
    have heq : (z - c) ^ n * (v z - u z) = g z - φ z := by
      rw [mul_sub, ← hgv z, ← hfactor z hzcl, hφpower z hzcl, hvalue]
      ring
    simpa only [heq, norm_sub_rev] using hclose z hzcl
  have hvubound := norm_analytic_power_quotient_le hR hvu (fun _ => rfl) herror
  obtain ⟨β, hβ, hβpair, hβ0⟩ := Hunit v hv
    (fun z hz => (hvubound z hz).trans_lt hquot)
  have hβclose : ∀ z ∈ ball c R, ‖α z - β z‖ ≤ τ := by
    intro z hz
    simpa only [norm_sub_rev] using (hβpair z (ball_subset_closedBall hz)).1.le
  obtain ⟨θ, hθA, hθi, hθU, hθinv, hθpair, hfixed⟩ :=
    Hregular β (hβ.mono ball_subset_closedBall) hβclose
  refine ⟨θ, hθA, hθi, hθU, hθinv, ?_, ?_⟩
  · intro z hz
    refine ⟨(hθpair z hz).1, ?_⟩
    have hθz := ball_subset_closedBall (hθU hz)
    calc
      g (θ z) = g c + β (θ z) ^ n := by
        have h₁ := hgv (θ z)
        have h₂ := (hβpair (θ z) hθz).2
        linear_combination h₁ - h₂
      _ = φ c + α z ^ n := by rw [hvalue, (hθpair z hz).2]
      _ = φ z := (hφpower z (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hz))).symm
  · apply hfixed c (mem_ball_self hr)
    exact (hβ0 hα0).trans hα0.symm

end FunctionTheory
