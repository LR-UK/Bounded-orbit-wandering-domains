import FunctionTheory.Conformal.SlitBankLimit
import FunctionTheory.Conformal.StraightBoundaryContinuous

open Set Metric Complex Filter
open scoped Topology

namespace FunctionTheory

theorem re_squared_slit_bank_coordinate {c z : ℂ} (hc : c.re = 0) :
    ((z ^ 2 - c ^ 2) / c).re = 2 * z.re * (z.im * c.im) / (c.im * c.im) := by
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply, hc]
  ring

/-- After unwrapping a straight slit by squaring the right half-disk, a
conformal disk map extends continuously to the closed diameter. Each of the
two slit banks uses its own boundary limit; the free tip uses the local
Caratheodory theorem. No regularity of the remaining boundary is assumed. -/
theorem exists_continuous_extension_on_unwrapped_slit
    {U : Set ℂ} {f : ℂ → ℂ} {R ρ : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ^ 2 < R)
    (hlocal : U ∩ ball (0 : ℂ) R = slitPlane ∩ ball 0 R) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F (ball 0 ρ ∩ {z : ℂ | 0 ≤ z.re}) ∧
      DifferentiableOn ℂ F (ball 0 ρ ∩ {z : ℂ | 0 < z.re}) ∧
      InjOn F (ball 0 ρ ∩ {z : ℂ | 0 < z.re}) ∧
      EqOn F (fun z => f (z ^ 2)) (ball 0 ρ ∩ {z : ℂ | 0 < z.re}) ∧
      MapsTo F (ball 0 ρ ∩ {z : ℂ | 0 < z.re}) (ball 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) ρ, z.re = 0 → F z ∈ sphere (0 : ℂ) 1 := by
  let S : Set ℂ := ball 0 ρ ∩ {z : ℂ | 0 < z.re}
  let B : Set ℂ := ball 0 ρ ∩ {z : ℂ | 0 ≤ z.re}
  have hmem : ∀ z ∈ ball (0 : ℂ) R, z ∈ U ↔ z ∈ slitPlane := by
    intro z hz
    have h := congrArg (fun S : Set ℂ => z ∈ S) hlocal
    simpa only [mem_inter_iff, hz, and_true] using iff_of_eq h
  have hsqball (z : ℂ) (hz : z ∈ ball (0 : ℂ) ρ) : z ^ 2 ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, norm_pow]
    have hz' := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hsqU : MapsTo (fun z : ℂ => z ^ 2) S U := fun z hz =>
    (hmem _ (hsqball z hz.1)).mpr (sq_mem_slitPlane_of_re_pos hz.2)
  have hBS : B ⊆ closure S := fun z hz =>
    mem_closure_right_half_ball (mem_ball_zero_iff.mp hz.1) hz.2
  have hlim (c : ℂ) (hc : c ∈ ball (0 : ℂ) ρ) (hc0 : c.re = 0) :
      ∃ a ∈ sphere (0 : ℂ) 1, Tendsto (fun z => f (z ^ 2)) (𝓝[S] c) (𝓝 a) := by
    by_cases hcZ : c = 0
    · subst c
      obtain ⟨a, ha, hfa⟩ := exists_boundary_limit_at_slit_tip hU hf hbij hR hlocal
      have ht : Tendsto (fun z : ℂ => z ^ 2) (𝓝[S] 0) (𝓝[U] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · simpa using ((continuous_pow 2).continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz using hsqU hz
      exact ⟨a, ha, hfa.comp ht⟩
    · have hcim : c.im ≠ 0 := by
        intro heq
        apply hcZ
        exact Complex.ext hc0 heq
      have hc2re : (c ^ 2).re < 0 := by
        simp only [pow_two, Complex.mul_re, hc0, zero_mul, zero_sub]
        exact neg_neg_of_pos (mul_self_pos.mpr hcim)
      have hc2im : (c ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, hc0]
      obtain ⟨a, ha, hfa⟩ := exists_boundary_limit_at_slit_bank hU hf hbij hlocal
        (hsqball c hc) hc2re hc2im hc0 hcim
      have ht : Tendsto (fun z : ℂ => z ^ 2) (𝓝[S] c)
          (𝓝[U ∩ {z : ℂ | 0 < ((z - c ^ 2) / c).re}] (c ^ 2)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (continuous_pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        · have he : ∀ᶠ z : ℂ in 𝓝 c, 0 < z.im * c.im :=
            (isOpen_lt continuous_const (Complex.continuous_im.mul continuous_const)).mem_nhds
              (mul_self_pos.mpr hcim)
          filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds] with z hz hzi
          refine ⟨hsqU hz, ?_⟩
          change 0 < ((z ^ 2 - c ^ 2) / c).re
          rw [re_squared_slit_bank_coordinate hc0]
          exact div_pos (mul_pos (mul_pos (by norm_num) hz.2) hzi) (mul_self_pos.mpr hcim)
      exact ⟨a, ha, hfa.comp ht⟩
  have hfd : DifferentiableOn ℂ (fun z : ℂ => f (z ^ 2)) S :=
    hf.comp (differentiable_id.pow 2).differentiableOn hsqU
  have hall : ∀ c ∈ B, ∃ a, Tendsto (fun z : ℂ => f (z ^ 2)) (𝓝[S] c) (𝓝 a) := by
    intro c hc
    rcases eq_or_lt_of_le (show 0 ≤ c.re from hc.2) with hc0 | hcpos
    · obtain ⟨a, -, ha⟩ := hlim c hc.1 hc0.symm
      exact ⟨a, ha⟩
    · exact ⟨f (c ^ 2), hfd.continuousOn c ⟨hc.1, hcpos⟩⟩
  let F := extendFrom S (fun z : ℂ => f (z ^ 2))
  have heq : EqOn F (fun z => f (z ^ 2)) S := extendFrom_extends hfd.continuousOn
  refine ⟨F, continuousOn_extendFrom hBS hall, hfd.congr heq, ?_, heq, ?_, ?_⟩
  · intro z hz w hw he
    rw [heq hz, heq hw] at he
    exact injOn_sq_right_halfplane hz.2 hw.2 (hbij.injOn (hsqU hz) (hsqU hw) he)
  · intro z hz
    rw [heq hz]
    exact hbij.mapsTo (hsqU hz)
  · intro z hz hz0
    obtain ⟨a, ha, hfa⟩ := hlim z hz hz0
    change extendFrom S (fun z : ℂ => f (z ^ 2)) z ∈ _
    rwa [extendFrom_eq (hBS ⟨hz, hz0.ge⟩) hfa]

end FunctionTheory
