import ComplexApproximation.Topology.HomeomorphicTail
import ComplexApproximation.BiLipschitzExtension
import FunctionTheory.Conformal.StripProper

open Set Metric Filter Asymptotics
open scoped Topology NNReal

namespace ComplexApproximation

/-- A holomorphic map whose derivative tends to one has an ambient extension
on a sufficiently far straight tail. No extension on the bounded decoration
of its domain is asserted. -/
theorem exists_homeomorph_on_straight_tail_of_derivative_limit
    {U : Set ℂ} {f : ℂ → ℂ} {R M : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (htail : ∀ z : ℂ, R < z.re → |z.im| ≤ M → z ∈ U)
    (hlim : Tendsto (fun z => deriv f z - 1)
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0)) :
    ∃ T : ℝ, ∃ H : ℂ ≃ₜ ℂ,
      EqOn f H {z : ℂ | T ≤ z.re ∧ |z.im| ≤ M} := by
  let C : ℝ≥0 := lipschitzExtensionConstant ℂ
  have hC : 0 < C := lipschitzExtensionConstant_pos ℂ
  let q : ℝ≥0 := (2 * C)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmall : lipschitzExtensionConstant ℂ * q < 1 := by
    change C * (2 * C)⁻¹ < 1
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
    norm_num
  have hev : ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 U, ‖deriv f z - 1‖ < (q : ℝ) := by
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    filter_upwards [hlim.eventually (ball_mem_nhds (0 : ℂ) hqR)] with z hz
    exact mem_ball_zero_iff.mp hz
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (eventually_comap.mp (eventually_inf_principal.mp hev))
  let T := max A R + 1
  let S : Set ℂ := {z | T ≤ z.re ∧ |z.im| ≤ M}
  have hSU : S ⊆ U := by
    intro z hz
    apply htail z _ hz.2
    have hTR : R < T := by dsimp [T]; linarith [le_max_right A R]
    exact hTR.trans_le hz.1
  have hconv : Convex ℝ S := by
    have heq : S = {z : ℂ | T ≤ z.re} ∩
        ({z : ℂ | -M ≤ z.im} ∩ {z : ℂ | z.im ≤ M}) := by
      ext z
      exact and_congr_right fun _ => abs_le
    rw [heq]
    exact (convex_halfSpace_re_ge T).inter
      ((convex_halfSpace_im_ge (-M)).inter (convex_halfSpace_im_le M))
  have hLip : LipschitzOnWith q (fun z => f z - z) S := by
    apply hconv.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (hf.differentiableAt (hU.mem_nhds (hSU hz))).sub differentiableAt_id)
    intro z hz
    have hd := ((hf.differentiableAt (hU.mem_nhds (hSU hz))).hasDerivAt.sub
      (hasDerivAt_id z)).deriv
    change deriv (fun w => f w - w) z = deriv f z - 1 at hd
    change ‖deriv (fun w => f w - w) z‖ ≤ (q : ℝ)
    rw [hd]
    apply (hA z.re _ z rfl (hSU hz)).le
    have hAT : A ≤ T := by dsimp [T]; linarith [le_max_left A R]
    exact hAT.trans hz.1
  obtain ⟨H, heH, _⟩ := exists_bilipschitz_extension_of_small_error hsmall hLip
  exact ⟨T, H, heH⟩

/-- On a closed inset, the straight-tail extension supplies the invariant
needed for transporting every later approximation subset. -/
theorem hasHomeomorphicTailOn_of_strip_derivative_limit
    {E U : Set ℂ} {f : ℂ → ℂ} (hE : IsClosed E)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {L M R : ℝ}
    (hleft : ∀ z ∈ E, L ≤ z.re) (him : ∀ z ∈ E, |z.im| ≤ M)
    (htail : ∀ z : ℂ, R < z.re → |z.im| ≤ M → z ∈ U)
    (hd : Tendsto (fun z => deriv f z - 1)
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0)) : HasHomeomorphicTailOn f E := by
  obtain ⟨T, H, heH⟩ := exists_homeomorph_on_straight_tail_of_derivative_limit
    hU hf htail hd
  have hK := FunctionTheory.isCompact_left_truncation_of_strip_bounds
    (R := T) hE hleft him
  refine ⟨_, hK, H, ?_⟩
  intro z hz
  apply heH
  refine ⟨?_, him z hz.1⟩
  exact (lt_of_not_ge (fun h => hz.2 ⟨hz.1, h⟩)).le

/-- Arakelian sets with bounded left truncations remain Arakelian under a
conformal chart whose derivative tends to one on its straight end. -/
theorem IsArakelian.image_conformal_of_strip_derivative_limit
    {E : Set ℂ} (hE : IsArakelian E)
    (e : OpenPartialHomeomorph ℂ ℂ) (hU : IsConnected e.source)
    (he : DifferentiableOn ℂ e e.source) (hEU : E ⊆ e.source)
    {L M R : ℝ}
    (hleft : ∀ z ∈ E, L ≤ z.re) (him : ∀ z ∈ E, |z.im| ≤ M)
    (htail : ∀ z : ℂ, R < z.re → |z.im| ≤ M → z ∈ e.source)
    (hd : Tendsto (fun z => deriv e z - 1)
      (comap Complex.re atTop ⊓ 𝓟 e.source) (𝓝 0)) : IsArakelian (e '' E) := by
  exact hE.image_openPartialHomeomorph_of_homeomorphic_tail e hU hEU
    (hasHomeomorphicTailOn_of_strip_derivative_limit hE.isClosed
      e.open_source he hleft him htail hd)

end ComplexApproximation
