import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import FunctionTheory.Holomorphic

open Set Metric Filter
open scoped Topology ComplexConjugate BigOperators

namespace FunctionTheory

set_option autoImplicit false

/-- A finite Blaschke product of positive degree. Repeated zeros encode
multiplicity. The unimodular factor is arbitrary. -/
structure FiniteBlaschkeProduct where
  degreePred : ℕ
  zero : Fin (degreePred + 1) → ℂ
  zero_lt_one : ∀ i, ‖zero i‖ < 1
  phase : ℂ
  norm_phase : ‖phase‖ = 1

noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  (z - a) / (1 - conj a * z)

/-- The elementary identity controlling both the disc and its boundary. -/
theorem blaschke_norm_difference (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem blaschke_denominator_ne_zero {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : 1 - conj a * z ≠ 0 := by
  have h : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < 1 := by simpa using ha
  intro he
  have : conj a * z = 1 := (sub_eq_zero.mp he).symm
  simpa only [this, norm_one, lt_self_iff_false] using h

theorem norm_blaschkeFactor_lt_one {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖blaschkeFactor a z‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hd := blaschke_norm_difference a z
  have hn : ‖z - a‖ < ‖1 - conj a * z‖ := by
    nlinarith [mul_pos ha2 hz2, norm_nonneg (z-a), norm_nonneg (1-conj a*z)]
  rw [blaschkeFactor, norm_div, div_lt_one (norm_pos_iff.mpr
    (blaschke_denominator_ne_zero ha hz.le))]
  exact hn

theorem norm_blaschkeFactor_eq_one {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) : ‖blaschkeFactor a z‖ = 1 := by
  have hd := blaschke_norm_difference a z
  have hn : ‖z - a‖ = ‖1 - conj a * z‖ := by
    rw [hz] at hd
    nlinarith [norm_nonneg (z-a), norm_nonneg (1-conj a*z)]
  rw [blaschkeFactor, norm_div, hn, div_self]
  exact norm_ne_zero_iff.mpr (blaschke_denominator_ne_zero ha hz.le)

namespace FiniteBlaschkeProduct

noncomputable def eval (B : FiniteBlaschkeProduct) (z : ℂ) : ℂ :=
  B.phase * ∏ i, blaschkeFactor (B.zero i) z

theorem analyticOnNhd_closedBall (B : FiniteBlaschkeProduct) :
    AnalyticOnNhd ℂ B.eval (closedBall 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  unfold blaschkeFactor
  exact (analyticAt_id.sub analyticAt_const).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (blaschke_denominator_ne_zero (B.zero_lt_one i) hz')

theorem norm_eval_sphere (B : FiniteBlaschkeProduct) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖B.eval z‖ = 1 := by
  simp only [eval, norm_mul, B.norm_phase, one_mul, norm_prod]
  have h : ∀ i : Fin (B.degreePred + 1), ‖blaschkeFactor (B.zero i) z‖ = 1 :=
    fun i => norm_blaschkeFactor_eq_one (B.zero_lt_one i) hz
  simp only [h, Finset.prod_const_one]

theorem eval_zero (B : FiniteBlaschkeProduct) (i : Fin (B.degreePred + 1)) :
    B.eval (B.zero i) = 0 := by
  unfold eval
  have h : ∏ j, blaschkeFactor (B.zero j) (B.zero i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [blaschkeFactor]
  rw [h, mul_zero]

theorem norm_eval_lt_one (B : FiniteBlaschkeProduct) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖B.eval z‖ < 1 := by
  simp only [eval, norm_mul, B.norm_phase, one_mul, norm_prod]
  have H : ∏ i, ‖blaschkeFactor (B.zero i) z‖ ≤
      ∏ i ∈ ({0} : Finset (Fin (B.degreePred + 1))), ‖blaschkeFactor (B.zero i) z‖ :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (by simp)
      (fun i _ => norm_nonneg _)
      (fun i _ _ => (norm_blaschkeFactor_lt_one (B.zero_lt_one i) hz).le)
  have H' : ∏ i, ‖blaschkeFactor (B.zero i) z‖ ≤ ‖blaschkeFactor (B.zero 0) z‖ := by
    simpa using H
  exact H'.trans_lt (norm_blaschkeFactor_lt_one (B.zero_lt_one 0) hz)


theorem mapsTo_closedBall (B : FiniteBlaschkeProduct) :
    MapsTo B.eval (closedBall 0 1) (closedBall 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hn : ‖B.eval z‖ ≤ 1 := by
    rcases hz'.lt_or_eq with h | h
    · exact (B.norm_eval_lt_one h).le
    · exact (B.norm_eval_sphere h).le
  simpa using hn


/-- A positive-degree Blaschke product is an open holomorphic map on a
slightly larger disc. Thus it meets the actual-domain model hypotheses,
including at every point of the unit circle. -/
theorem exists_open_holomorphic_neighborhood (B : FiniteBlaschkeProduct) :
    ∃ r : ℝ, 1 < r ∧ AnalyticOnNhd ℂ B.eval (ball 0 r) ∧
      IsOpenMap (fun z : ball (0 : ℂ) r => B.eval z) := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
    (isOpen_analyticAt ℂ B.eval) B.analyticOnNhd_closedBall
  rw [thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1)] at hsub
  have hr : 1 < δ + 1 := by linarith
  have han : AnalyticOnNhd ℂ B.eval (ball 0 (δ+1)) := hsub
  refine ⟨δ+1, hr, han, ?_⟩
  rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) (δ+1)).isPreconnected with hc | ho
  · obtain ⟨c, hc⟩ := hc
    have ha : B.zero 0 ∈ ball (0 : ℂ) (δ+1) := by
      simpa using (B.zero_lt_one 0).trans hr
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (δ+1) := by simpa using hr
    have hc0 : c = 0 := (hc _ ha).symm.trans (B.eval_zero 0)
    have hn := B.norm_eval_sphere (z := 1) (by simp)
    rw [hc 1 h1, hc0, norm_zero] at hn
    norm_num at hn
  · intro s hs
    have ht := isOpen_ball.isOpenMap_subtype_val s hs
    have him := ho (Subtype.val '' s) (by rintro z ⟨z,hz,rfl⟩; exact z.property) ht
    simpa only [image_image, Function.comp_def] using him


/-- The disc map is onto, as required for an orbit of wandering domains,
not merely an orbit of invariant subsets. -/
theorem image_ball (B : FiniteBlaschkeProduct) :
    B.eval '' ball (0 : ℂ) 1 = ball 0 1 := by
  have hmaps : MapsTo B.eval (ball (0 : ℂ) 1) (ball 0 1) := by
    intro z hz
    simpa using B.norm_eval_lt_one (by simpa using hz)
  have hc : IsClosed (B.eval '' closedBall (0 : ℂ) 1) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      B.analyticOnNhd_closedBall.continuousOn).isClosed
  obtain ⟨r, hr, han, ho⟩ := B.exists_open_holomorphic_neighborhood
  have hi : IsOpen (B.eval '' ball (0 : ℂ) 1) := by
    have H := ho ((Subtype.val : ball (0 : ℂ) r → ℂ) ⁻¹' ball 0 1)
      (isOpen_ball.preimage continuous_subtype_val)
    have heq : (fun z : ball (0 : ℂ) r => B.eval z) ''
        ((Subtype.val : ball (0 : ℂ) r → ℂ) ⁻¹' ball 0 1) =
        B.eval '' ball (0 : ℂ) 1 := by
      ext w
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨z,hz,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨z, ball_subset_ball hr.le hz⟩, hz, rfl⟩
    exact heq ▸ H
  have hsub : ball (0 : ℂ) 1 ⊆
      (B.eval '' ball (0 : ℂ) 1) ∪ (B.eval '' closedBall (0 : ℂ) 1)ᶜ := by
    intro w hw
    by_cases h : w ∈ B.eval '' closedBall (0 : ℂ) 1
    · obtain ⟨z,hz,rfl⟩ := h
      left
      refine ⟨z, ?_, rfl⟩
      have hz' : ‖z‖ ≤ 1 := by simpa using hz
      have hw' : ‖B.eval z‖ < 1 := by simpa using hw
      rcases hz'.lt_or_eq with hlt | heq
      · simpa using hlt
      · exact ((B.norm_eval_sphere heq).not_lt hw').elim
    · exact Or.inr h
  have hdis : Disjoint (B.eval '' ball (0 : ℂ) 1)
      (B.eval '' closedBall (0 : ℂ) 1)ᶜ :=
    disjoint_compl_right.mono_left (image_mono ball_subset_closedBall)
  have hne : ((ball (0 : ℂ) 1) ∩ (B.eval '' ball (0 : ℂ) 1)).Nonempty := by
    refine ⟨0, by simp, B.zero 0, ?_, B.eval_zero 0⟩
    simpa using B.zero_lt_one 0
  exact Subset.antisymm (image_subset_iff.mpr hmaps)
    ((convex_ball (0 : ℂ) 1).isPreconnected.subset_left_of_subset_union
      hi hc.isOpen_compl hdis hsub hne)

end FiniteBlaschkeProduct
end FunctionTheory

