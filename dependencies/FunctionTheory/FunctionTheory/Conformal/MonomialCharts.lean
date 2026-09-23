import FunctionTheory.Conformal.BlaschkeMonomial
import FunctionTheory.Conformal.LocalConjugacyCritical
import FunctionTheory.Conformal.InjectiveImageChart

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A monomial conjugacy maps the first chart image into the second. -/
theorem mapsTo_of_monomial_chart (f σ τ : ℂ → ℂ)
    (k : ℕ) (a : ℂ) (ha : ‖a‖=1)
    (hconj : ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (a*z^(k+1))) :
    MapsTo f (σ '' ball (0:ℂ) 1) (τ '' ball (0:ℂ) 1) := by
  rintro w ⟨z,hz,rfl⟩
  have hB := (FiniteBlaschkeProduct.monomial k a ha).norm_eval_lt_one
    (mem_ball_zero_iff.mp hz)
  refine ⟨a*z^(k+1),?_,(hconj z hz).symm⟩
  simpa only [FiniteBlaschkeProduct.eval_monomial,mem_ball_zero_iff] using hB

/-- The distinguished centre maps to the next centre. -/
theorem map_centre_of_monomial_chart (f σ τ : ℂ → ℂ)
    (k : ℕ) (a : ℂ)
    (hconj : ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (a*z^(k+1))) :
    f (σ 0)=τ 0 := by
  simpa using hconj 0 (mem_ball_self (by norm_num : (0:ℝ)<1))

/-- The next distinguished centre has exactly one preimage in the source
chart image. No critical-point classification theorem is needed here. -/
theorem eq_centre_iff_of_monomial_chart (f σ τ : ℂ → ℂ)
    (k : ℕ) (a : ℂ) (ha : ‖a‖=1)
    (hτ : InjOn τ (ball (0:ℂ) 1))
    (hconj : ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (a*z^(k+1)))
    {w : ℂ} (hw : w∈σ '' ball (0:ℂ) 1) :
    f w=τ 0 ↔ w=σ 0 := by
  obtain ⟨z,hz,rfl⟩ := hw
  constructor
  · intro h
    have hB : a*z^(k+1)∈ball (0:ℂ) 1 := by
      simpa only [FiniteBlaschkeProduct.eval_monomial,mem_ball_zero_iff] using
        (FiniteBlaschkeProduct.monomial k a ha).norm_eval_lt_one (mem_ball_zero_iff.mp hz)
    have heq := hτ hB (mem_ball_self (by norm_num : (0:ℝ)<1)) ((hconj z hz).symm.trans h)
    have hz0 := (FiniteBlaschkeProduct.monomial_eval_eq_zero_iff k a ha z).mp
      (by simpa only [FiniteBlaschkeProduct.eval_monomial] using heq)
    exact congrArg σ hz0
  · intro h
    rw [h]
    exact map_centre_of_monomial_chart f σ τ k a hconj

/-- Conformal source and target charts transport the unique critical point
of a monomial to the source centre. -/
theorem deriv_eq_zero_iff_of_monomial_chart (f σ τ : ℂ → ℂ)
    {k : ℕ} (hk : 0<k) (a : ℂ) (ha : ‖a‖=1)
    (hσ : DifferentiableOn ℂ σ (ball (0:ℂ) 1))
    (hτ : DifferentiableOn ℂ τ (ball (0:ℂ) 1))
    (hiσ : InjOn σ (ball (0:ℂ) 1)) (hiτ : InjOn τ (ball (0:ℂ) 1))
    (hf : DifferentiableOn ℂ f (σ '' ball (0:ℂ) 1))
    (hconj : ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (a*z^(k+1)))
    {w : ℂ} (hw : w∈σ '' ball (0:ℂ) 1) :
    deriv f w=0 ↔ w=σ 0 := by
  obtain ⟨z,hz,rfl⟩ := hw
  let B := FiniteBlaschkeProduct.monomial k a ha
  have hBz : B.eval z∈ball (0:ℂ) 1 :=
    mem_ball_zero_iff.mpr (B.norm_eval_lt_one (mem_ball_zero_iff.mp hz))
  have hopen : IsOpen (σ '' ball (0:ℂ) 1) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hσ hiσ
  have heq : (fun x => f (σ x)) =ᶠ[𝓝 z] (fun x => τ (B.eval x)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    simpa only [B,FiniteBlaschkeProduct.eval_monomial] using hconj x hx
  have H := deriv_eq_zero_iff_of_local_conjugacy
    (B.analyticOnNhd_closedBall z (ball_subset_closedBall hz)).differentiableAt
    (hf.differentiableAt (hopen.mem_nhds (mem_image_of_mem σ hz)))
    (hσ.differentiableAt (isOpen_ball.mem_nhds hz))
    (hτ.differentiableAt (isOpen_ball.mem_nhds hBz))
    (TauCeti.deriv_ne_zero_of_injOn hσ isOpen_ball hiσ hz)
    (TauCeti.deriv_ne_zero_of_injOn hτ isOpen_ball hiτ hBz) heq
  rw [H,FiniteBlaschkeProduct.deriv_monomial_eq_zero_iff hk a ha]
  exact ⟨fun h => congrArg σ h,fun h => hiσ hz (mem_ball_self (by norm_num)) h⟩

end FunctionTheory
