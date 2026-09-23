import FunctionTheory.Conformal.FiniteBlaschke
import TauCeti.Analysis.Complex.Conformal.Moebius

open Set Metric

namespace FunctionTheory

/-- The factor convention agrees exactly with the attributed Tau Ceti API. -/
theorem blaschkeFactor_eq_unitDiscMoebius (a z : Complex.UnitDisc) :
    blaschkeFactor (a : ℂ) (z : ℂ) = (TauCeti.unitDiscMoebius a z : ℂ) := rfl

namespace FiniteBlaschkeProduct

noncomputable def discMap (B : FiniteBlaschkeProduct) (z : ball (0 : ℂ) 1) :
    ball (0 : ℂ) 1 :=
  ⟨B.eval z, mem_ball_zero_iff.mpr (B.norm_eval_lt_one (mem_ball_zero_iff.mp z.property))⟩

@[simp] theorem coe_discMap (B : FiniteBlaschkeProduct) (z : ball (0 : ℂ) 1) :
    (B.discMap z : ℂ) = B.eval z := rfl

theorem surjective_discMap (B : FiniteBlaschkeProduct) : Function.Surjective B.discMap := by
  intro w
  have hw : (w : ℂ) ∈ B.eval '' ball (0 : ℂ) 1 := B.image_ball.symm ▸ w.property
  obtain ⟨z,hz,he⟩ := hw
  exact ⟨⟨z,hz⟩, Subtype.ext he⟩

end FiniteBlaschkeProduct
end FunctionTheory
