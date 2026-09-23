import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Complex.Basic

/-!
# A smooth compactly supported extension near a compact set

Moved without changing the proofs from ComplexApproximation/Runge/SmoothCutoff.lean
on 21 September 2026, for reuse by smooth conformal corrections. The original
Runge names remain available as compatibility exports.

Multiplication by a smooth cutoff preserves the holomorphic function near `K`
and gives a globally smooth function with compact support. This is the input
for the Cauchy–Green representation.
-/

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

theorem exists_smooth_cutoff (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ U ∧ ∀ x ∈ K, φ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hW, hKW, hWV, _⟩ :=
    exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨φ, hφ, _, hsφ, h1φ⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV isClosed_closure hWV
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  · simpa only [HasCompactSupport, tsupport, hsφ] using hVc
  · simpa only [tsupport, hsφ] using hVU
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (h1φ y).mp (subset_closure hy)

/-- There is a globally smooth function of compact support agreeing with the
given analytic function on a neighbourhood of every point of `K`. -/
theorem exists_smooth_compact_extension (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨φ, hφ, hcφ, hsφ, h1φ⟩ := exists_smooth_cutoff K U hK hU hKU
  refine ⟨fun x => φ x • f x, ?_, hcφ.smul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact hφ.contDiffAt.smul ((hf x (hsφ hx)).contDiffAt.restrict_scalars ℝ)
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy]
  · intro x hx
    filter_upwards [h1φ x hx] with y hy
    simp [hy]

end FunctionTheory
