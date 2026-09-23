import EremenkosConjecture.RayStage
import ComplexApproximation.HalfStripMargins

/-! # Uniform tubes and quantitative changes of coordinates -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

theorem HasQuantitativeExtensionOn.mono {f : ℂ → ℂ} {A B : Set ℂ}
    (h : HasQuantitativeExtensionOn f A) (hBA : B ⊆ A) :
    HasQuantitativeExtensionOn f B := by
  obtain ⟨H, heq, L, L', hL, hL'⟩ := h
  exact ⟨H, heq.mono hBA, L, L', hL, hL'⟩

theorem HasQuantitativeExtensionOn.comp {f g : ℂ → ℂ} {A B : Set ℂ}
    (hf : HasQuantitativeExtensionOn f B) (hg : HasQuantitativeExtensionOn g A)
    (hAB : MapsTo g A B) : HasQuantitativeExtensionOn (f ∘ g) A := by
  obtain ⟨F, hF, L, L', hL, hL'⟩ := hf
  obtain ⟨G, hG, M, M', hM, hM'⟩ := hg
  refine ⟨G.trans F, fun z hz => ?_, L * M, M' * L', hL.comp hM, hM'.comp hL'⟩
  change f (g z) = F (G z)
  rw [hF (hAB hz), hG hz]

theorem HasUniformTube.mono {A B U V : Set ℂ} (h : HasUniformTube A U)
    (hBA : B ⊆ A) (hUV : U ⊆ V) : HasUniformTube B V := by
  obtain ⟨r, hr, htube⟩ := h
  exact ⟨r, hr, fun z hz => (htube z (hBA hz)).trans hUV⟩

theorem HasUniformTube.image {A U : Set ℂ} (h : HasUniformTube A U)
    (H : ℂ ≃ₜ ℂ) {L : ℝ≥0} (hL : LipschitzWith L H.symm) :
    HasUniformTube (H '' A) (H '' U) := by
  obtain ⟨r, hr, htube⟩ := h
  exact exists_uniform_image_tube H hL hr htube

theorem HasUniformTube.subset {A U : Set ℂ} (h : HasUniformTube A U) : A ⊆ U := by
  obtain ⟨r, hr, htube⟩ := h
  exact fun z hz => htube z hz (mem_ball_self hr)

theorem HasUniformTube.interior_right {A U : Set ℂ} (h : HasUniformTube A U) :
    HasUniformTube A (interior U) := by
  obtain ⟨r, hr, htube⟩ := h
  exact ⟨r, hr, fun z hz => interior_maximal (htube z hz) isOpen_ball⟩

theorem hasUniformTube_halfStrip {ζ : ℂ} {a b a' b' : ℝ}
    (ha : a < a') (hb : b < b') :
    HasUniformTube (closedHalfStrip ζ a b) (closedHalfStrip ζ a' b') := by
  let r := min (a' - a) (b' - b)
  have hr : 0 < r := lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
  refine ⟨r, hr, fun z hz w hw => ?_⟩
  have hd : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hRe := abs_lt.mp ((Complex.abs_re_le_norm (w - z)).trans_lt hd)
  have hIm := (Complex.abs_im_le_norm (w - z)).trans_lt hd
  simp only [Complex.sub_re, Complex.sub_im] at hRe hIm
  have hrA : r ≤ a' - a := min_le_left _ _
  have hrB : r ≤ b' - b := min_le_right _ _
  refine ⟨by linarith [hz.1, hRe.1], ?_⟩
  have ht := abs_add_le (w.im - z.im) (z.im - ζ.im)
  rw [sub_add_sub_cancel] at ht
  linarith [hz.2]

noncomputable def translation (ζ : ℂ) : ℂ ≃ₜ ℂ := Homeomorph.addRight ζ

@[simp] theorem translation_apply (ζ z : ℂ) : translation ζ z = z + ζ := rfl
@[simp] theorem translation_symm_apply (ζ z : ℂ) : (translation ζ).symm z = z - ζ := rfl

theorem lipschitz_translation (ζ : ℂ) : LipschitzWith 1 (translation ζ) :=
  (isometry_add_right ζ).lipschitzWith

theorem lipschitz_translation_symm (ζ : ℂ) : LipschitzWith 1 (translation ζ).symm := by
  change LipschitzWith 1 (fun z : ℂ => z - ζ)
  simpa only [sub_eq_add_neg] using (isometry_add_right (-ζ)).lipschitzWith

def openHalfStrip (ζ : ℂ) (a b : ℝ) : Set ℂ :=
  {z | ζ.re - a < z.re ∧ |z.im - ζ.im| < b}

theorem isOpen_openHalfStrip (ζ : ℂ) (a b : ℝ) : IsOpen (openHalfStrip ζ a b) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const)

theorem openHalfStrip_subset_closed (ζ : ℂ) (a b : ℝ) :
    openHalfStrip ζ a b ⊆ closedHalfStrip ζ a b := fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem hasUniformTube_closed_openHalfStrip {ζ : ℂ} {a b a' b' : ℝ}
    (ha : a < a') (hb : b < b') :
    HasUniformTube (closedHalfStrip ζ a b) (openHalfStrip ζ a' b') := by
  obtain ⟨r, hr, htube⟩ := hasUniformTube_halfStrip (ζ := ζ)
    (show a < (a + a') / 2 by linarith) (show b < (b + b') / 2 by linarith)
  refine ⟨r, hr, fun z hz w hw => ?_⟩
  have hm := htube z hz hw
  exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

theorem translation_image_halfStrip (ζ : ℂ) (a b : ℝ) :
    translation ζ '' ComplexApproximation.closedRightHalfStrip (-a) b = closedHalfStrip ζ a b := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    constructor
    · change ζ.re - a ≤ w.re + ζ.re
      linarith [hw.1]
    · simpa only [translation_apply, Complex.add_im, add_sub_cancel_right] using hw.2
  · intro hz
    refine ⟨z - ζ, ⟨?_, ?_⟩, sub_add_cancel _ _⟩
    · change -a ≤ z.re - ζ.re
      linarith [hz.1]
    · exact hz.2

end EremenkosConjecture
