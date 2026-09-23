import FunctionTheory.Conformal.BlochDerivativeBound
import FunctionTheory.Conformal.NormalizedCosineLift
import FunctionTheory.Conformal.SchottkyGrid
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric
namespace FunctionTheory
set_option autoImplicit false

/-- An entire function whose image contains no disc of a fixed radius is
constant. This is the whole-plane consequence of Bloch's theorem. -/
theorem eq_const_of_no_image_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} (hM : 0≤M) (hno : ∀ b : ℂ, ¬ ball b M ⊆ range f) :
    ∀ z : ℂ, f z=f 0 := by
  have hd : ∀ c, deriv f c=0 := by
    intro c
    by_contra hne
    have hA : 0<‖deriv f c‖ := norm_pos_iff.mpr hne
    let r := 256*M/‖deriv f c‖+1
    have hr : 0<r := by dsimp [r]; positivity
    have H := norm_deriv_le_of_no_image_ball hr hM
      (fun z (_ : z∈(univ : Set ℂ)) => hf.analyticAt z) (subset_univ (closedBall c r))
      (fun b => by simpa only [image_univ] using hno b)
    have H' := (le_div_iff₀ hr).mp H
    have heq : ‖deriv f c‖*r=256*M+‖deriv f c‖ := by
      dsimp [r]
      field_simp
    rw [heq] at H'
    linarith
  exact fun z => is_const_of_deriv_eq_zero hf hd z 0

/-- Little Picard in the normalization used by the double-cosine proof.
The proof uses the whole-plane consequence of Bloch, not Schottky's estimate. -/
theorem eq_const_of_omits_one_neg_one {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hplus : ∀ z, f z≠1) (hminus : ∀ z, f z≠-1) : ∀ z, f z=f 0 := by
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    let : ContractibleSpace (univ : Set ℂ) := (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace ⟨0,mem_univ 0⟩
    change SimplyConnectedSpace (univ : Set ℂ)
    infer_instance
  obtain ⟨h,hh,_,hhcos⟩ := exists_normalized_scaled_cosine_lift isOpen_univ hsc
    (fun z _ => hf.analyticAt z) (fun z _ => hplus z) (fun z _ => hminus z) (mem_univ 0)
  have hhplus : ∀ z∈(univ : Set ℂ), h z≠1 := by
    intro z hz H
    have H' := hhcos z hz
    rw [H,mul_one,Complex.cos_pi] at H'
    exact hminus z H'.symm
  have hhminus : ∀ z∈(univ : Set ℂ), h z≠-1 := by
    intro z hz H
    have H' := hhcos z hz
    rw [H,mul_neg_one,Complex.cos_neg,Complex.cos_pi] at H'
    exact hminus z H'.symm
  obtain ⟨g,hg,_,hgcos⟩ := exists_normalized_scaled_cosine_lift isOpen_univ hsc hh hhplus hhminus (mem_univ 0)
  have hdouble : ∀ z∈(univ : Set ℂ), Complex.cos (Real.pi*Complex.cos (Real.pi*g z))=f z := by
    intro z hz
    rw [hgcos z hz,hhcos z hz]
  have hno := no_ball_subset_double_cosine_lift_image (fun z _ => hplus z) (fun z _ => hminus z) hdouble
  have hc := eq_const_of_no_image_ball (fun z => (hg z (mem_univ z)).differentiableAt)
    (by norm_num : (0:ℝ)≤3) (fun b => by simpa only [image_univ] using hno b)
  intro z
  rw [← hdouble z (mem_univ z),← hdouble 0 (mem_univ 0),hc z]

/-- Little Picard: an entire function omitting two distinct finite values
is constant. Its hypotheses and conclusion align with ProjectVD's public
`Differentiable.exists_eq_const_of_forall_ne`; the proof here uses Bloch
and holomorphic cosine lifts instead of value-distribution theory. -/
theorem exists_eq_const_of_two_omitted_values {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℂ} (hab : a≠b) (ha : ∀ z, f z≠a) (hb : ∀ z, f z≠b) :
    ∃ c, f=fun _ => c := by
  have hba : b-a≠0 := sub_ne_zero.mpr hab.symm
  let F := fun z => (2:ℂ)*(f z-a)/(b-a)-1
  have hF : Differentiable ℂ F :=
    (((differentiable_const (2:ℂ)).mul (hf.sub_const a)).div_const (b-a)).sub_const 1
  have hp : ∀ z, F z≠1 := by
    intro z H
    apply hb z
    dsimp [F] at H
    have H' : 2*(f z-a)=2*(b-a) := (div_eq_iff hba).mp (by linear_combination H)
    linear_combination H'/2
  have hm : ∀ z, F z≠-1 := by
    intro z H
    apply ha z
    dsimp [F] at H
    have H' : 2*(f z-a)=0 := (div_eq_zero_iff.mp (by linear_combination H)).resolve_right hba
    linear_combination H'/2
  have hc := eq_const_of_omits_one_neg_one hF hp hm
  refine ⟨f 0,funext fun z => ?_⟩
  have H := hc z
  dsimp [F] at H
  have H' : 2*(f z-a)=2*(f 0-a) := (div_left_inj' hba).mp (sub_left_inj.mp H)
  linear_combination H'/2

end FunctionTheory
