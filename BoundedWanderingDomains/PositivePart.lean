import BoundedWanderingDomains.PunctureRegularisation

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

theorem smooth_majorant_bound {b s chi : ℂ → ℝ} {M : ℝ}
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi)
    (hchi0 : ∀ x, 0 ≤ chi x)
    (hb : ∀ x ∈ tsupport chi, ContDiffAt ℝ 2 b x)
    (hs : ∀ x ∈ tsupport chi, ContinuousAt s x)
    (hbound : ∀ x ∈ tsupport chi, 0 ≤ b x ∧ b x ≤ M)
    (hmajor : ∀ x ∈ tsupport chi, s x ≤ Δ b x) :
    (∫ x, chi x * s x) ≤ M * ∫ x, |Δ chi x| := by
  have isrc := integrable_mul_of_local hchi.continuous hc hs
  have ilap := integrable_mul_of_local hchi.continuous hc
    (fun x hx => laplacian_continuousAt (hb x hx))
  have hLc : Continuous (Δ chi) := continuous_iff_continuousAt.mpr
    (fun _ => laplacian_continuousAt hchi.contDiffAt)
  have hLk := laplacian_hasCompactSupport hc
  have iL : Integrable (Δ chi) := hLc.integrable_of_hasCompactSupport hLk
  have ibL : Integrable (fun x => b x * Δ chi x) := by
    simpa only [mul_comm] using integrable_mul_of_local hLc hLk
      (fun x hx => (hb x (laplacian_tsupport_subset chi hx)).continuousAt)
  calc
    (∫ x, chi x * s x) ≤ ∫ x, chi x * Δ b x := by
      apply integral_mono isrc ilap
      intro x
      by_cases hx : x ∈ tsupport chi
      · exact mul_le_mul_of_nonneg_left (hmajor x hx) (hchi0 x)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = ∫ x, b x * Δ chi x := green_laplacian hb hchi hc
    _ ≤ ∫ x, M * |Δ chi x| := by
      apply integral_mono ibL (iL.abs.const_mul M)
      intro x
      by_cases hx : x ∈ tsupport chi
      · exact (mul_le_mul_of_nonneg_left (le_abs_self _) (hbound x hx).1).trans
          (mul_le_mul_of_nonneg_right (hbound x hx).2 (abs_nonneg _))
      · have hxL : x ∉ tsupport (Δ chi) := fun h => hx (laplacian_tsupport_subset chi h)
        simp [image_eq_zero_of_notMem_tsupport hxL]
    _ = M * ∫ x, |Δ chi x| := integral_const_mul _ _

/-- Complete cutoff estimate with a finite exceptional set.

The hypotheses concern actual derivatives of `u`, local upper bounds, and the
sign of its Laplacian. No Green identity, regularisation data, distributional
inequality, or removable-singularity theorem is assumed.
-/
theorem positive_part_cutoff
    (F : Finset ℂ) {u chi : ℂ → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M)
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi)
    (hchi0 : ∀ x, 0 ≤ chi x)
    (hu : ∀ x ∈ tsupport chi, x ∉ F → ContDiffAt ℝ 2 u x)
    (hup : ∀ p ∈ tsupport chi, p ∈ F →
      ∃ B : ℝ, ∀ᶠ z in 𝓝 p, z ∉ F → u z ≤ B)
    (hM : ∀ x ∈ tsupport chi, x ∉ F → max (u x) 0 ≤ M)
    (hpos : ∀ x ∈ tsupport chi, x ∉ F → 0 < u x → 0 ≤ Δ u x)
    (hneg : ∀ x ∈ tsupport chi, x ∉ F → u x ≤ 0 → Δ u x ≤ 0) :
    (∫⁻ x, ENNReal.ofReal (chi x * (if x ∈ F then 0 else max (Δ u x) 0))) ≤
      ENNReal.ofReal (M * ∫ x, |Δ chi x|) := by
  obtain ⟨R, _, hR⟩ := hc.isBounded.exists_pos_norm_le
  let L : ℂ → ℝ := logBarrier F (∑ a ∈ F, (R + ‖a‖))
  have hL0 (x) (hx : x ∈ tsupport chi) : L x ≤ 0 := logBarrier_nonpos F (hR x hx)
  have hLh (x) (hx : x ∉ F) : HarmonicAt L x := logBarrier_harmonic F _ hx
  have hLp (x) (hx : x ∈ F) (B : ℝ) : ∀ᶠ z in 𝓝[≠] x, L z ≤ B :=
    logBarrier_eventually_le F _ hx B
  let A : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hA (n) : 0 < A n := by dsimp [A]; positivity
  let b : ℕ → ℂ → ℝ := fun n => puncturedBeta F u L (A n)
  let c : ℕ → ℂ → ℝ := fun n => puncturedSlope F u L (A n)
  let s : ℕ → ℂ → ℝ := fun n x => c n x * Δ u x
  have hb (n) (x) (hx : x ∈ tsupport chi) : ContDiffAt ℝ 2 (b n) x :=
    puncturedBeta_contDiffAt (hA n) (hu x hx) (fun h => (hLh x h).1)
      (hup x hx) (hLp x)
  have hbnd (n) (x) (hx : x ∈ tsupport chi) : 0 ≤ b n x ∧ b n x ≤ M := by
    by_cases hxf : x ∈ F
    · simpa [b, puncturedBeta, hxf] using hM0
    · have hh := puncturedBeta_bounds (F := F) (u := u) (hA n) (hL0 x hx)
      exact ⟨hh.1, hh.2.trans (hM x hx hxf)⟩
  have hs (n) (x) (hx : x ∈ tsupport chi) : ContinuousAt (s n) x := by
    by_cases hxf : x ∈ F
    · have hz := puncturedSlope_eventually_zero (hA n) hxf (hup x hx hxf) (hLp x hxf)
      apply (show ContinuousAt (fun _ : ℂ => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      simp [s, c, hz]
    · have hcnear : c n =ᶠ[𝓝 x] (fun z => Real.smoothTransition (A n * u z + L z)) := by
        filter_upwards [eventually_not_mem_finset F hxf] with z hz
        simp [c, puncturedSlope, hz]
      have hcc : ContinuousAt (c n) x :=
        (Real.smoothTransition.continuousAt.comp
          ((continuousAt_const.mul (hu x hx hxf).continuousAt).add
            (hLh x hxf).1.continuousAt)).congr_of_eventuallyEq hcnear
      exact hcc.mul (laplacian_continuousAt (hu x hx hxf))
  have hmajor (n) (x) (hx : x ∈ tsupport chi) : s n x ≤ Δ (b n) x := by
    by_cases hxf : x ∈ F
    · have hz := puncturedBeta_eventually_zero (hA n) hxf (hup x hx hxf) (hLp x hxf)
      have hzb : Δ (b n) x = 0 := by
        simpa [b, Pi.zero_def] using (laplacian_congr_nhds hz).eq_of_nhds
      simp [s, c, puncturedSlope, hxf, hzb]
    · exact puncturedBeta_laplacian_ge (hA n) hxf (hu x hx hxf) (hLh x hxf)
  have hsnn (n) (x) (hx : x ∈ tsupport chi) : 0 ≤ s n x := by
    by_cases hxf : x ∈ F
    · simp [s, c, puncturedSlope, hxf]
    · by_cases hux : 0 < u x
      · exact mul_nonneg (by simp [c, puncturedSlope, hxf, Real.smoothTransition.nonneg])
          (hpos x hx hxf hux)
      · have hw : A n * u x + L x ≤ 0 :=
          add_nonpos (mul_nonpos_of_nonneg_of_nonpos (hA n).le (le_of_not_gt hux)) (hL0 x hx)
        simp [s, c, puncturedSlope, hxf, Real.smoothTransition.zero_of_nonpos hw]
  apply AreaDeficitCore.fatou_uniform_bound
    (F := fun n x => chi x * s n x)
    (fun n => integrable_mul_of_local hchi.continuous hc (hs n))
  · intro n x
    by_cases hx : x ∈ tsupport chi
    · exact mul_nonneg (hchi0 x) (hsnn n x hx)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · intro x
    by_cases hx : x ∈ tsupport chi
    · by_cases hxf : x ∈ F
      · simp [s, c, puncturedSlope, hxf]
      · have hclim : Tendsto (fun n => c n x) atTop (𝓝 (if 0 < u x then 1 else 0)) := by
          simpa [c, puncturedSlope, hxf, A] using transition_scaled_add_tendsto (u x) (L x) (hL0 x hx)
        simpa only [ite_eq_right hxf] using
          (AreaDeficitCore.regularized_source_tendsto (hpos x hx hxf) (hneg x hx hxf) hclim).const_mul (chi x)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · intro n
    exact smooth_majorant_bound hchi hc hchi0 (hb n) (hs n) (hbnd n) (hmajor n)

end AreaDeficit
