import FunctionTheory.Conformal.StripUniformity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness on closed strip insets

An asymptotic translation has bounded displacement on a closed inset with
compact left truncations. Its restriction is proper and has closed image.
These facts use the map on its actual domain only.
-/

open Set Metric Bornology Filter
open scoped Topology

namespace FunctionTheory

theorem exists_norm_bound_of_strip_limit {S : Set ℂ} {q : ℂ → ℂ}
    {c : ℂ} {L M : ℝ} (hS : IsClosed S)
    (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hq : ContinuousOn q S)
    (hlim : Tendsto q (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ S, ‖q z‖ ≤ B := by
  have hevent : ∀ᶠ z in comap Complex.re atTop ⊓ 𝓟 S, ‖q z - c‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hlim.eventually (Metric.ball_mem_nhds c zero_lt_one)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp
    (eventually_inf_principal.mp hevent))
  let K := S ∩ {z : ℂ | z.re ≤ R}
  have hK : IsCompact K := isCompact_left_truncation_of_strip_bounds hS hleft him
  obtain ⟨B, hB, hbound⟩ :=
    (hK.image_of_continuousOn (hq.mono inter_subset_left)).isBounded.exists_pos_norm_le
  refine ⟨max B (1 + ‖c‖), lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro z hz
  by_cases hzR : z.re ≤ R
  · exact (hbound _ (mem_image_of_mem q ⟨hz, hzR⟩)).trans (le_max_left _ _)
  · have hh := hR z.re (le_of_not_ge hzR) z rfl hz
    have hn := norm_add_le (q z - c) c
    rw [sub_add_cancel] at hn
    exact (hn.trans (by linarith)).trans (le_max_right _ _)

theorem isCompact_inter_preimage_of_bounded_displacement
    {S K : Set ℂ} {f : ℂ → ℂ} {B : ℝ}
    (hS : IsClosed S) (hf : ContinuousOn f S)
    (hbound : ∀ z ∈ S, ‖f z - z‖ ≤ B) (hK : IsCompact K) :
    IsCompact (S ∩ f ⁻¹' K) := by
  obtain ⟨V, hV, hpre⟩ := continuousOn_iff_isClosed.mp hf K hK.isClosed
  have hclosed : IsClosed (S ∩ f ⁻¹' K) := by
    rw [inter_comm, hpre]
    exact hV.inter hS
  obtain ⟨C, -, hC⟩ := hK.isBounded.exists_pos_norm_le
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hclosed, isBounded_iff_forall_norm_le.mpr ⟨C + B, ?_⟩⟩
  intro z hz
  have hn := norm_sub_le (f z) (f z - z)
  rw [sub_sub_cancel] at hn
  exact hn.trans (add_le_add (hC _ hz.2) (hbound z hz.1))

theorem isProperMap_restrict_of_bounded_displacement {S : Set ℂ}
    {f : ℂ → ℂ} {B : ℝ} (hS : IsClosed S) (hf : ContinuousOn f S)
    (hbound : ∀ z ∈ S, ‖f z - z‖ ≤ B) : IsProperMap (S.domRestrict f) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf.domRestrict, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  convert isCompact_inter_preimage_of_bounded_displacement hS hf hbound hK using 1
  ext z
  simp only [mem_image, mem_preimage, Set.domRestrict_apply, mem_inter_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hzS, hzK⟩
    exact ⟨⟨z, hzS⟩, hzK, rfl⟩

theorem isProperMap_restrict_of_strip_translation_limit {S : Set ℂ}
    {f : ℂ → ℂ} {c : ℂ} {L M : ℝ} (hS : IsClosed S)
    (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hf : ContinuousOn f S)
    (hlim : Tendsto (fun z => f z - z) (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    IsProperMap (S.domRestrict f) := by
  obtain ⟨B, -, hB⟩ := exists_norm_bound_of_strip_limit hS hleft him
    (hf.sub continuous_id.continuousOn) hlim
  exact isProperMap_restrict_of_bounded_displacement hS hf hB

theorem isClosed_image_of_strip_translation_limit {S : Set ℂ}
    {f : ℂ → ℂ} {c : ℂ} {L M : ℝ} (hS : IsClosed S)
    (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hf : ContinuousOn f S)
    (hlim : Tendsto (fun z => f z - z) (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 c)) :
    IsClosed (f '' S) := by
  simpa only [Set.range_domRestrict] using
    (isProperMap_restrict_of_strip_translation_limit hS hleft him hf hlim).isClosed_range

theorem isProperMap_restrict_of_strip_translation_asymptotic {S : Set ℂ}
    {f : ℂ → ℂ} {c : ℂ} {L M : ℝ} (hS : IsClosed S)
    (hleft : ∀ z ∈ S, L ≤ z.re) (him : ∀ z ∈ S, |z.im| ≤ M)
    (hf : ContinuousOn f S)
    (hO : (fun z => f z - (z + c)) =O[comap Complex.re atTop ⊓ 𝓟 S]
      (fun z => Real.exp (-z.re))) : IsProperMap (S.domRestrict f) := by
  have hre : Tendsto Complex.re (comap Complex.re atTop ⊓ 𝓟 S) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hdecay : Tendsto (fun z : ℂ => Real.exp (-z.re))
      (comap Complex.re atTop ⊓ 𝓟 S) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hre)
  apply isProperMap_restrict_of_strip_translation_limit (c := c) hS hleft him hf
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [sub_add_eq_sub_sub] using hO.trans_tendsto hdecay

end FunctionTheory
