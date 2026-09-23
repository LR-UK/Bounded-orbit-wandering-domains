import FunctionTheory.Smooth.ControlledExtension
import FunctionTheory.Smooth.ComplexDerivativeBounds
import FunctionTheory.Smooth.CompactCompositionBounds
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Uniform holomorphic approximation to the identity near the image of a
compact set gives a global smooth extension whose composition with a fixed
C^m change of coordinates is uniformly small in every order through m.
The conclusion includes a smooth inverse, neighbourhood agreement, and
identity outside the prescribed open neighbourhood. -/
theorem exists_holomorphic_smooth_extension_comp
    (Θ : ℂ ≃ₜ ℂ) (m : ℕ) (hΘ : ContDiff ℝ m (Θ : ℂ → ℂ))
    {X V : Set ℂ} (hX : IsCompact X) (hV : IsOpen V) (hXV : Θ '' X ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V →
      (∀ z ∈ V, ‖θ z - z‖ ≤ η) →
      ∃ e : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
        (∀ z ∈ Θ '' X, (e : ℂ → ℂ) =ᶠ[𝓝 z] θ) ∧
        (∀ z ∉ V, e z = z) ∧
        HasCompactSupport (fun z => e z - z) ∧
        tsupport (fun z => e z - z) ⊆ V ∧
        ∀ n ≤ m, ∀ z,
          ‖iteratedFDeriv ℝ n (fun w => e (Θ w) - Θ w) z‖ < ε := by
  have hK : IsCompact (Θ '' X) := hX.image Θ.continuous
  obtain ⟨W, hW, hKW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hV hXV
  obtain ⟨M, hM, HM⟩ := exists_uniform_comp_derivative_bound Θ m hΘ hWc
  let q := max m 1
  have hmq : m ≤ q := le_max_left m 1
  have h1q : 1 ≤ q := le_max_right m 1
  let ε' := ε / (2 * M)
  have hε' : 0 < ε' := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨δ, hδ, Hδ⟩ := exists_controlled_smooth_extension hK hW hKW q h1q hε'
  obtain ⟨A, hA, HA⟩ := exists_uniform_real_derivative_bound_on_compact hV hWc hWV q
  let η := δ / A
  have hη : 0 < η := div_pos hδ hA
  refine ⟨η, hη, ?_⟩
  intro θ hθ Hθ
  have hθW : ContDiffOn ℝ ∞ θ W := by
    intro z hz
    exact ((hθ z (hWV (subset_closure hz))).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  let g : ℂ → ℂ := fun z => θ z - z
  have hg : AnalyticOnNhd ℂ g V := hθ.sub analyticOnNhd_id
  have Hder : ∀ n ≤ q, ∀ z ∈ W, ‖iteratedFDeriv ℝ n g z‖ ≤ δ := by
    intro n hn z hz
    have H := HA g hg η hη.le Hθ n hn z (subset_closure hz)
    have hAη : A * η = δ := by dsimp [η]; field_simp
    rwa [hAη] at H
  obtain ⟨e, hes, hei, heK, heW, hec, heSupp, heBound⟩ := Hδ θ hθW Hder
  refine ⟨e, hes, hei, heK, ?_, hec, heSupp.trans (subset_closure.trans hWV), ?_⟩
  · intro z hz
    exact heW z (fun hw => hz (hWV (subset_closure hw)))
  · let u : ℂ → ℂ := fun z => e z - z
    have hu : ContDiff ℝ m u := (hes.sub contDiff_id).of_le (by simp)
    have huL : tsupport u ⊆ closure W := heSupp.trans subset_closure
    have Hu : ∀ n ≤ m, ∀ z, ‖iteratedFDeriv ℝ n u z‖ ≤ ε' :=
      fun n hn z => (heBound n (hn.trans hmq) z).le
    intro n hn z
    have H := HM u hu huL ε' hε'.le Hu n hn z
    have hval : M * ε' = ε / 2 := by dsimp [ε']; field_simp
    rw [hval] at H
    exact H.trans_lt (half_lt_self hε)

end FunctionTheory
