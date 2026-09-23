import TauCeti.Analysis.Complex.Conformal.LengthArea
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace FunctionTheory

/-- The inner radius can be chosen before the domain and map. This is the
uniform length-area estimate needed for a family of shrinking attachments. -/
theorem exists_uniform_annulus_of_bounded_image
    {B : Set ℂ} (hB : Bornology.IsBounded B) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R, ∀ (U : Set ℂ) (f : ℂ → ℂ) (ζ : ℂ),
      IsOpen U → DifferentiableOn ℂ f U → InjOn f U → MapsTo f U B →
      ∃ ρ ∈ Ioo r R, TauCeti.circleImageLength f U ζ ρ < ENNReal.ofReal ε := by
  have hAtop : ENNReal.ofReal (2 * Real.pi) * volume B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.measure_lt_top.ne
  let A := (ENNReal.ofReal (2 * Real.pi) * volume B).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  let L := (A + 1) / ε ^ 2
  have hL : 0 < L := div_pos (by linarith) (sq_pos_of_pos hε)
  have hεL : ε ^ 2 * L = A + 1 := by dsimp [L]; field_simp
  let r := R * Real.exp (-L)
  have hr : 0 < r := mul_pos hR (Real.exp_pos _)
  have hrR : r < R := by
    have hexp : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [r]
    nlinarith
  have hlog : Real.log (R / r) = L := by
    have heq : R / r = Real.exp L := by dsimp [r]; rw [Real.exp_neg]; field_simp
    rw [heq, Real.log_exp]
  have hbound : ENNReal.ofReal (2 * Real.pi) * volume B <
      ENNReal.ofReal ε ^ 2 * ENNReal.ofReal (Real.log (R / r)) := by
    have hAeq : ENNReal.ofReal (2 * Real.pi) * volume B = ENNReal.ofReal A :=
      (ENNReal.ofReal_toReal hAtop).symm
    rw [hAeq, hlog, ← ENNReal.ofReal_pow hε.le,
      ← ENNReal.ofReal_mul (sq_nonneg ε), hεL]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  refine ⟨r, ⟨hr, hrR⟩, ?_⟩
  intro U f ζ hU hf hinj hmaps
  have harea : volume (f '' U) ≤ volume B := measure_mono hmaps.image_subset
  have harea' : ENNReal.ofReal (2 * Real.pi) * volume (f '' U) ≤
      ENNReal.ofReal (2 * Real.pi) * volume B := by gcongr
  obtain ⟨ρ, hρ, hlen⟩ := TauCeti.exists_circleImageLength_sq_lt_of_volume_image
    hU hf hU.measurableSet subset_rfl hinj ζ hr hrR
    (harea'.trans_lt hbound)
  refine ⟨ρ, hρ, ?_⟩
  by_contra h
  exact (not_le.mpr hlen) (pow_le_pow_left' (not_lt.mp h) 2)

/-- A length bound controls every point of a right semicircular crosscut from
its midpoint. Endpoints on the domain boundary need not be included. -/
theorem dist_image_right_semicircle_lt_of_length_lt
    {U : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ} {ρ ε : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hρ : 0 < ρ)
    (harc : ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2), circleMap ζ ρ θ ∈ U)
    (hlen : TauCeti.circleImageLength f U ζ ρ < ENNReal.ofReal ε)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    dist (f (circleMap ζ ρ θ)) (f (ζ + ρ)) < ε := by
  have hzero : circleMap ζ ρ 0 = ζ + ρ := by simp [circleMap]
  have hchord : ENNReal.ofReal (dist (f (circleMap ζ ρ θ)) (f (circleMap ζ ρ 0))) ≤
      TauCeti.circleImageLength f U ζ ρ := by
    rcases le_total θ 0 with hθ0 | h0θ
    · apply TauCeti.ofReal_dist_le_circleImageLength hU hf ζ hρ hθ0
        (by linarith [hθ.1, Real.pi_pos])
      all_goals intro t ht; apply harc; constructor <;> linarith [ht.1, ht.2, hθ.1, hθ.2, Real.pi_pos]
    · rw [dist_comm]
      apply TauCeti.ofReal_dist_le_circleImageLength hU hf ζ hρ h0θ
        (by linarith [hθ.2, Real.pi_pos])
      all_goals intro t ht; apply harc; constructor <;> linarith [ht.1, ht.2, hθ.1, hθ.2, Real.pi_pos]
  rw [hzero] at hchord
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp (hchord.trans_lt hlen)

end FunctionTheory
