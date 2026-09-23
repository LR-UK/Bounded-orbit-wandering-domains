import EremenkosConjecture.ScaffoldingReturnMap
import EremenkosConjecture.QuantitativeGeometry
import ComplexApproximation.HalfStripNormalisation

/-! # The explicit return channel for the ray construction -/

open Set Function
open scoped NNReal

noncomputable section

namespace EremenkosConjecture

open Scaffolding
open ComplexApproximation.HalfStrip

structure RayReturnChannel (f : ℂ → ℂ) (j : ℕ) (a b : ℝ) where
  η : ℝ
  η_pos : 0 < η
  η_small : η < a
  ψ : ℂ → ℂ
  holomorphic : ∀ k ≤ j + 1, DifferentiableOn ℂ (fun z => (f^[k]) (ψ z))
    (openHalfStrip rayBase η (Real.pi / 2))
  extensions : ∀ k ≤ j + 1, HasQuantitativeExtensionOn (fun z => (f^[k]) (ψ z))
    (closedHalfStrip rayBase (η / 2) (b / 4))
  orbit : ∀ k < j + 1, MapsTo (fun z => (f^[k]) (ψ z))
    (openHalfStrip rayBase η (Real.pi / 2)) (insetSourceStrip k)
  target : ∀ z ∈ openHalfStrip rayBase η (Real.pi / 2),
    (height (j + 1) + 7) / 4 + 1 / 4 ≤ ((f^[j + 1]) (ψ z)).im ∧
    ((f^[j + 1]) (ψ z)).im ≤ (height (j + 1) + 11) / 4 - 1 / 4
  boundedReturn : ∀ x : ℝ, 1 / ((j : ℝ) + 1) ≤ x → x ≤ (j : ℝ) + 1 →
    |(ψ (rayBase + x)).re| < 1 / 2
  endpoint : ∀ k ≤ j + 1, (j : ℝ) + 2 ≤ |((f^[k]) (ψ rayBase)).re|

theorem exists_rayReturnChannel {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (j : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hbsmall : b ≤ 1 / 16) :
    Nonempty (RayReturnChannel f j a b) := by
  obtain ⟨ρ, hρ, hρsmall, hcompress⟩ := exists_compression
    (a := 1 / ((j : ℝ) + 1)) (b := (j : ℝ) + 1) (r := 1 / 8)
    (by positivity) (by norm_num)
  obtain ⟨η, hη, hηsmall, hfar⟩ := exists_small_shift_far_left hρ
    (lt_min ha zero_lt_one) (-(6 : ℝ) ^ (j + 1) * ((j : ℝ) + 3))
  have hηa : η < a := hηsmall.trans_le (min_le_left _ _)
  have hη1 : η < 1 := hηsmall.trans_le (min_le_right _ _)
  let U := openHalfStrip rayBase η (Real.pi / 2)
  let C := closedHalfStrip rayBase (η / 2) (b / 4)
  let c := (height (j + 1) + 9) / 4
  let φ := fun z : ℂ => normalizedMap c ρ η (z - rayBase)
  have hdomain : ∀ z ∈ U, z - rayBase + (η : ℂ) ∈ domain := by
    intro z hz
    constructor
    · change 0 < z.re - rayBase.re + η
      linarith [hz.1]
    · simpa only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, add_zero] using hz.2
  have hφ : DifferentiableOn ℂ φ U := by
    intro z hz
    exact ((hasDerivAt_normalizedMap (hdomain z hz)).differentiableAt.comp z
      (differentiableAt_id.sub_const rayBase)).differentiableWithinAt
  have him : ∀ z ∈ U, |(φ z).im - c| < 1 / 8 := fun z hz =>
    normalizedMap_im_bound hρ hρsmall (hdomain z hz)
  have hφT : MapsTo φ U (targetStrip (j + 1)) := by
    intro z hz
    have hi := abs_lt.mp (him z hz)
    constructor <;> dsimp [c] at hi <;> linarith [hi.1, hi.2]
  have hCU : C ⊆ U := by
    intro z hz
    exact ⟨by linarith [hz.1], hz.2.trans_lt (by linarith [Real.two_le_pi])⟩
  obtain ⟨P, hP, L, L', hL, hL'⟩ := exists_bilipschitz_normalized_extension
    (c := c) (η := η) (ρ := ρ) (a := -η / 2) (b := b / 4) (by linarith) (by positivity)
    (by linarith [Real.two_le_pi]) hρ
  have hφext : HasQuantitativeExtensionOn φ C := by
    refine ⟨(translation rayBase).symm.trans P, ?_, L * 1, 1 * L',
      hL.comp (lipschitz_translation_symm rayBase),
      (lipschitz_translation rayBase).comp hL'⟩
    intro z hz
    apply hP
    exact ⟨by change -η / 2 ≤ z.re - rayBase.re; linarith [hz.1], hz.2⟩
  obtain ⟨ψ, hψ, hfinal, horbit, hext⟩ := exists_return_map hf hclose
    (Nat.succ_pos j) hφ hφT hCU hφext
  have hray (x : ℝ) (hx : 0 ≤ x) : rayBase + (x : ℂ) ∈ U := by
    constructor
    · change rayBase.re - η < rayBase.re + x
      linarith
    · simp only [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]
      positivity
  have hreal (x : ℝ) (hx : 0 ≤ x) :
      φ (rayBase + x) = (ρ * realProfile (x + η) : ℝ) + (c : ℂ) * Complex.I := by
    dsimp only [φ]
    rw [add_sub_cancel_left]
    exact normalizedMap_ofReal (by linarith)
  refine ⟨{
    η := η
    η_pos := hη
    η_small := hηa
    ψ := ψ
    holomorphic := hψ
    extensions := hext
    orbit := horbit
    target := ?_
    boundedReturn := ?_
    endpoint := ?_ }⟩
  · intro z hz
    have he : (f^[j + 1]) (ψ z) = φ z := hfinal hz
    rw [he]
    have hi := abs_lt.mp (him z hz)
    constructor <;> dsimp [c] at hi <;> linarith [hi.1, hi.2]
  · intro x hxmin hxmax
    have hx : 0 ≤ x := (by positivity : 0 < 1 / ((j : ℝ) + 1)).le.trans hxmin
    apply return_map_small_real_part hclose horbit hfinal (hray x hx)
    rw [hreal x hx]
    simpa using hcompress x ⟨hxmin, hxmax⟩ η ⟨hη.le, hη1.le⟩
  · apply return_map_large_real_parts hclose horbit hfinal
      (by linarith [Nat.cast_nonneg (α := ℝ) j] : (1 / 2 : ℝ) ≤ (j : ℝ) + 2)
      (by simpa using hray 0 le_rfl)
    have he := hreal 0 le_rfl
    simp only [Complex.ofReal_zero, add_zero, zero_add] at he
    rw [he]
    simpa [show (j : ℝ) + 2 + 1 = (j : ℝ) + 3 by ring] using hfar

end EremenkosConjecture
