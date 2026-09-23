import EremenkosConjecture.ContinuumAttachmentMap
import EremenkosConjecture.ContinuumStripChart
import EremenkosConjecture.ContinuumChartCoordinates
import EremenkosConjecture.QuantitativeGeometry

open Set Metric Function Complex FunctionTheory
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

/-- One conformal map with simultaneous continuum escape, compact-ray
compression, and all the local chart estimates needed for approximation. -/
structure ContinuumTargetMap (X : Set ℂ) (ζ : ℂ) (j : ℕ) where
  domain : Set ℂ
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  contains : X ∪ horizontalRay ζ ⊆ domain
  tail : ∃ R : ℝ, ∀ z : ℂ, R < z.re → |z.im - ζ.im| < Real.pi / 2 → z ∈ domain
  φ : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ φ domain
  target : ∀ z ∈ domain, |(φ z).im - (height (j + 1) + 9) / 4| < 1 / 8
  compact_ray : ∀ x : ℝ, 1 / ((j : ℝ) + 1) ≤ x → x ≤ (j : ℝ) + 1 →
    |(φ (ζ + x)).re| < 1 / 2
  far_left : ∀ z ∈ X, (φ z).re < -(6 : ℝ) ^ (j + 1) * ((j : ℝ) + 3)
  charts : ∀ P : Set ℂ, IsClosed P → P ⊆ domain →
    (∀ z ∈ P, ζ.re - 1 / 16 ≤ z.re ∧ |z.im - ζ.im| ≤ 1 / 16) →
    ∃ D : LocalIterateChart φ 1 P, D.chart.source = domain

theorem exists_continuumTargetMap {X : Set ℂ} {ζ : ℂ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hmax : ∀ z ∈ X, z.re ≤ ζ.re)
    (hball : X ⊆ ball ζ (1 / 16)) (j : ℕ) :
    Nonempty (ContinuumTargetMap X ζ j) := by
  let T := (translation ζ).symm
  let X₀ := T '' X
  let a : ℝ := 1 / (2 * ((j : ℝ) + 1))
  let K : Set ℂ := Complex.ofReal '' Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1)
  have hX₀ : IsCompact X₀ := hX.image T.continuous
  have hconn₀ : IsConnected X₀ := hconn.image T T.continuous.continuousOn
  have hfull₀ : IsConnected X₀ᶜ := by
    change IsConnected (T '' X)ᶜ
    rw [← T.image_compl]
    exact hfull.image T T.continuous.continuousOn
  have hzero : (0 : ℂ) ∈ X₀ := ⟨ζ, hζ, sub_self ζ⟩
  have hmax₀ : ∀ z ∈ X₀, z.re ≤ (0 : ℝ) := by
    rintro z ⟨w, hw, rfl⟩
    change w.re - ζ.re ≤ 0
    linarith [hmax w hw]
  have hstrip : X₀ ⊆ standardHorizontalStrip := by
    rintro z ⟨w, hw, rfl⟩
    have hb : ‖w - ζ‖ < 1 / 16 := mem_ball_iff_norm.mp (hball hw)
    exact ((abs_im_le_norm (w - ζ)).trans_lt hb).trans
      (by linarith [Real.two_le_pi])
  have ha : 0 < a := by dsimp [a]; positivity
  have haK : a < 1 / ((j : ℝ) + 1) := by
    have hp : 0 < 1 / ((j : ℝ) + 1) := by positivity
    calc
      a = (1 / ((j : ℝ) + 1)) / 2 := by
        dsimp [a]
        rw [mul_comm (2 : ℝ), div_mul_eq_div_div]
      _ < 1 / ((j : ℝ) + 1) := half_lt_self hp
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKV : K ⊆ {z : ℂ | a < z.re ∧ |z.im| < Real.pi / 2} := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨haK.trans_le hx.1, by simp; positivity⟩
  obtain ⟨C, η, c, ρ, φ₀, hC, hCi, hXC, _, hη, _, hU₀o, hU₀sc,
      hXU₀, _, hφ₀, hbij, _, hOd, hOv, hc, hcsmall, hcompact, hleft⟩ :=
    exists_continuum_attachment_map hX₀ hconn₀ hfull₀ hzero hmax₀ hstrip ha
      isOpen_univ (subset_univ X₀) (by norm_num : (0 : ℝ) < 1)
      (half_pos Real.pi_pos) le_rfl hK hKV (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (0 : ℝ) < 1 / 2) (-(6 : ℝ) ^ (j + 1) * ((j : ℝ) + 3))
  let U₀ := filledAttachmentDomain C (0 : ℂ) (a : ℂ) 1 η (Real.pi / 2)
  have htail₀ : ∀ z : ℂ, a < z.re → |z.im| < Real.pi / 2 → z ∈ U₀ := by
    intro z hz hi
    apply straight_tail_subset_filledAttachmentDomain (a := (a : ℂ)) hCi (hXC hzero)
      (by norm_num : (0 : ℝ) < 1) hη (half_pos Real.pi_pos) (by simp)
    exact ⟨by simpa using hz, by simpa using hi⟩
  let U := T ⁻¹' U₀
  have hUeq : U = T.symm '' U₀ := by
    ext z
    constructor
    · intro hz
      exact ⟨T z, hz, T.symm_apply_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      change T (T.symm w) ∈ U₀
      simpa using hw
  have hUo : IsOpen U := hU₀o.preimage T.continuous
  have hUc : IsConnected U := by
    rw [hUeq]
    exact hU₀sc.isPathConnected.isConnected.image T.symm T.symm.continuous.continuousOn
  have hXU : X ∪ horizontalRay ζ ⊆ U := by
    rintro z (hz | hz)
    · exact hXU₀ (Or.inl (mem_image_of_mem T hz))
    · apply hXU₀ (Or.inr ?_)
      change (0 : ℝ) ≤ z.re - ζ.re ∧ z.im - ζ.im = 0
      exact ⟨sub_nonneg.mpr hz.1, sub_eq_zero.mpr hz.2⟩
  have htail : ∀ z : ℂ, a + ζ.re < z.re → |z.im - ζ.im| < Real.pi / 2 → z ∈ U := by
    intro z hz hi
    exact htail₀ (T z) (by change a < z.re - ζ.re; linarith) hi
  let b : ℝ := (height (j + 1) + 9) / 4
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  let H : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (c : ℂ) hcne).trans
    (translation ((b : ℂ) * I))
  let φ : ℂ → ℂ := H ∘ φ₀ ∘ T
  have hφeq (z : ℂ) : φ z = (c : ℂ) * φ₀ (z - ζ) + (b : ℂ) * I := rfl
  have hφ : DifferentiableOn ℂ φ U :=
    ((hφ₀.comp (differentiable_id.sub_const ζ).differentiableOn
      (fun _ hz => hz)).const_mul (c : ℂ)).add_const ((b : ℂ) * I)
  have him : ∀ z ∈ U, |(φ z).im - b| < 1 / 8 := by
    intro z hz
    have hs := hbij.mapsTo hz
    change |(φ₀ (T z)).im| < Real.pi / 2 at hs
    rw [hφeq]
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, zero_add, I_im, I_re,
      mul_one, add_zero, add_sub_cancel_right, abs_mul, abs_of_pos hc]
    exact (mul_lt_mul_of_pos_left hs hc).trans hcsmall
  have hmulUC (d : ℂ) : UniformContinuous (fun z : ℂ => d * z) := by
    have hLip : LipschitzWith ‖d‖₊ (fun z : ℂ => d * z) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simp only [dist_eq_norm, ← mul_sub, norm_mul, coe_nnnorm, le_refl]
    exact hLip.uniformContinuous
  have hHUC : UniformContinuous H := (hmulUC c).add_const _
  have hHiUC : UniformContinuous H.symm :=
    (hmulUC (c : ℂ)⁻¹).comp (uniformContinuous_id.sub_const _)
  have hHih : Differentiable ℂ H.symm :=
    (differentiable_id.sub_const _).const_mul (c : ℂ)⁻¹
  refine ⟨{
    domain := U
    open_domain := hUo
    connected_domain := hUc
    contains := hXU
    tail := ⟨a + ζ.re, htail⟩
    φ := φ
    holomorphic := hφ
    target := him
    compact_ray := ?_
    far_left := ?_
    charts := ?_ }⟩
  · intro x hxmin hxmax
    have hb := hcompact (x : ℂ) ⟨x, ⟨hxmin, hxmax⟩, rfl⟩
    rw [hφeq, add_sub_cancel_left]
    simpa only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using
      (abs_re_le_norm ((c : ℂ) * φ₀ x)).trans_lt hb
  · intro z hz
    have hl := hleft (T z) (mem_image_of_mem T hz)
    change ((c : ℂ) * φ₀ (z - ζ)).re < _ at hl
    rw [hφeq]
    simpa only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hl
  · intro P hP hPU hbound
    let P₀ := T '' P
    have hP₀ : IsClosed P₀ := T.isClosedMap _ hP
    have hP₀U : P₀ ⊆ U₀ := by
      rintro z ⟨w, hw, rfl⟩
      exact hPU hw
    have hPleft : ∀ z ∈ P₀, -(1 / 16 : ℝ) ≤ z.re := by
      rintro z ⟨w, hw, rfl⟩
      change -(1 / 16 : ℝ) ≤ w.re - ζ.re
      linarith [(hbound w hw).1]
    have hPim : ∀ z ∈ P₀, |z.im| ≤ (1 / 16 : ℝ) := by
      rintro z ⟨w, hw, rfl⟩
      exact (hbound w hw).2
    obtain ⟨D₀, hD₀⟩ := exists_localIterateChart_of_strip_asymptotic hU₀o
      hU₀sc.isPathConnected.isConnected hφ₀ hbij.injOn hP₀ hP₀U hPleft hPim
      (fun z hz hi => htail₀ z hz (hi.trans_lt (by linarith [Real.two_le_pi]))) hOd hOv
    obtain ⟨D₁, hD₁⟩ := D₀.precomp_homeomorph T
      (lipschitz_translation_symm ζ).uniformContinuous
      (lipschitz_translation ζ).uniformContinuous (differentiable_id.add_const ζ)
    obtain ⟨D₂, hD₂⟩ := D₁.postcomp_homeomorph H hHUC hHiUC hHih
    have hPpre : T ⁻¹' P₀ = P := T.injective.preimage_image P
    have hDs : D₂.chart.source = U := hD₂.trans (hD₁.trans (congrArg (preimage T) hD₀))
    rw [← hPpre]
    exact ⟨D₂, hDs⟩

end EremenkosConjecture
