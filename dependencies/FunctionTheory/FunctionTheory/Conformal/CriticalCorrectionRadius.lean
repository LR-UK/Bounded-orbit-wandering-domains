import FunctionTheory.Conformal.PowerCoordinateDisk
import FunctionTheory.Conformal.CriticalCorrectionLocal

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A fixed disk around a nonconstant holomorphic germ supports arbitrarily
small conformal corrections of sufficiently close perturbations preserving
the central value and at least the reference local degree. -/
theorem exists_correction_disk_at_locally_nonconstant
    {φ : ℂ → ℂ} {c : ℂ} (hφ : AnalyticAt ℂ φ c)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, φ z = φ c)
    {U : Set ℂ} (hU : IsOpen U) (hc : c ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, R ≤ η ∧ closedBall c R ⊆ U ∧
      ∀ ε > 0, ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) →
        g c = φ c →
        analyticOrderAt (fun z => φ z - φ c) c ≤
          analyticOrderAt (fun z => g z - g c) c →
        (∀ z ∈ closedBall c R, ‖φ z - g z‖ ≤ δ) →
        ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ (ball c (R / 2)) ∧
          InjOn θ (ball c (R / 2)) ∧ MapsTo θ (ball c (R / 2)) (ball c R) ∧
          DifferentiableOn ℂ (Function.invFunOn θ (ball c (R / 2)))
            (θ '' ball c (R / 2)) ∧
          (∀ z ∈ ball c (R / 2), ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ θ c = c := by
  have hfinite : analyticOrderAt (fun z => φ z - φ c) c ≠ ⊤ := by
    intro htop
    apply hnc
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    exact sub_eq_zero.mp hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hn0 : n ≠ 0 := by
    intro heq
    have hF : AnalyticAt ℂ (fun z => φ z - φ c) c := hφ.sub analyticAt_const
    have hz := hF.analyticOrderAt_ne_zero.mpr (sub_self (φ c))
    exact hz (by simpa [heq] using hn.symm)
  obtain ⟨R, hR, hRη, hRU, α, u, hα, hu, hu0, hα0, hαd, hp, hf⟩ :=
    exists_power_coordinate_disk hφ hn0 hn.symm hU hc hη
  refine ⟨R, hR, hRη, hRU, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := exists_conformal_correction_on_power_coordinate_disk
    hR (half_pos hR) (half_lt_self hR) hn0 hα hu hu0 hα0
    (fun z hz => hαd z (closedBall_subset_closedBall (half_le_self hR.le) hz))
    hp (fun z _ => hf z) hε
  refine ⟨δ, hδ, ?_⟩
  intro g hg hvalue horder hclose
  exact H g hg hvalue (by simpa only [← hn] using horder) hclose

end FunctionTheory
