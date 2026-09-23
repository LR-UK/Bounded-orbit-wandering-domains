import ComplexApproximation.CauchyRiemannGluing

/-! # Smooth localization with pointwise control -/

open Set Function Filter Complex Runge
open scoped Topology ContDiff

namespace ComplexApproximation

/-- A compactly supported smooth cutoff with values in `[0,1]`, equal to one
on a neighbourhood of the given compact set. -/
theorem exists_smooth_cutoff_controlled (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ U ∧ (∀ x, φ x ∈ Icc 0 1) ∧
      ∀ x ∈ K, φ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hW, hKW, hWV, _⟩ :=
    exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨φ, hφ, hrφ, hsφ, h1φ⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV isClosed_closure hWV
  refine ⟨φ, hφ, ?_, ?_, (fun x => hrφ (mem_range_self x)), ?_⟩
  · simpa only [HasCompactSupport, tsupport, hsφ] using hVc
  · simpa only [tsupport, hsφ] using hVU
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (h1φ y).mp (subset_closure hy)

theorem contDiff_cauchyRiemannDefect {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cauchyRiemannDefect g) := by
  have h := hg.contDiff_fderiv_apply (m := ∞) (by simp)
  exact (contDiff_const.mul (h.comp (contDiff_id.prodMk contDiff_const))).sub
    (h.comp (contDiff_id.prodMk contDiff_const))

theorem tsupport_cauchyRiemannDefect_subset (g : ℂ → ℂ) :
    tsupport (cauchyRiemannDefect g) ⊆ tsupport g := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  exact hz (by simp [cauchyRiemannDefect, hd])

/-- Multiplying a function smooth near a cutoff's support gives a globally
smooth function, regardless of the extension chosen outside that neighbourhood. -/
theorem contDiff_cutoff_mul {φ : ℂ → ℝ} {g : ℂ → ℂ} {U : Set ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ContDiff ℝ ∞ (fun x => (φ x : ℂ) * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact (Complex.ofRealCLM.contDiff.comp hφ).contDiffAt.mul (hg x (hs hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

theorem support_cutoff_mul_subset {φ : ℂ → ℝ} {g : ℂ → ℂ} :
    support (fun x => (φ x : ℂ) * g x) ⊆ tsupport φ := by
  intro x hx
  apply subset_tsupport φ
  intro hz
  exact hx (by simp [hz])

theorem hasCompactSupport_cutoff_mul {φ : ℂ → ℝ} (hc : HasCompactSupport φ)
    (g : ℂ → ℂ) : HasCompactSupport (fun x => (φ x : ℂ) * g x) := by
  exact hc.mono' support_cutoff_mul_subset

/-- Local smallness on the support of a controlled cutoff becomes global
smallness of the localized function. -/
theorem norm_cutoff_mul_le {φ : ℂ → ℝ} {g : ℂ → ℂ} {U : Set ℂ} {M : ℝ}
    (hφ : ∀ x, φ x ∈ Icc 0 1) (hs : tsupport φ ⊆ U)
    (hM : 0 ≤ M) (hg : ∀ x ∈ U, ‖g x‖ ≤ M) (x : ℂ) :
    ‖(φ x : ℂ) * g x‖ ≤ M := by
  by_cases hx : x ∈ tsupport φ
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφ x).2).trans (hg x (hs hx))
  · have hz : φ x = 0 := notMem_tsupport_iff_eventuallyEq.mp hx |>.self_of_nhds
    simpa only [hz, Complex.ofReal_zero, zero_mul, norm_zero] using hM

end ComplexApproximation
