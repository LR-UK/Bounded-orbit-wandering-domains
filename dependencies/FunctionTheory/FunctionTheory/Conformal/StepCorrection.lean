import FunctionTheory.Conformal.ClosedCriticalCorrection
import FunctionTheory.Conformal.InversePerturbation
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- One backward step in a finite conjugacy chain. A sufficiently small
correction of the target can be pulled back through a sufficiently close
perturbation of the source map, retaining the finite marked points. -/
theorem exists_backward_conformal_correction_tolerance
    {U V Ω C : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    (hC : C.Finite) (hCV : C ⊆ V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hcritical : ∀ z ∈ closure V, deriv φ z = 0 → z ∈ C)
    (himage : MapsTo φ (closure V) Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g χ : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      AnalyticOnNhd ℂ χ Ω → InjOn χ Ω →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      (∀ w ∈ Ω, ‖χ w - w‖ < δ) →
      (∀ c ∈ C, g c = φ c) → (∀ c ∈ C, χ (φ c) = φ c) →
      (∀ c ∈ C, analyticOrderAt (fun z => φ z - φ c) c ≤
        analyticOrderAt (fun z => g z - g c) c) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ z ∈ V, ‖θ z - z‖ < ε ∧ g (θ z) = χ (φ z)) ∧
        ∀ c ∈ C, θ c = c := by
  have hP : IsOpen (U ∩ φ ⁻¹' Ω) := hφ.continuousOn.isOpen_inter_preimage hU hΩ
  obtain ⟨W, hW, hKW, hWP, hWc⟩ := exists_open_between_and_isCompact_closure hK hP
    (fun z hz => ⟨hKU hz, himage hz⟩)
  have hWU : closure W ⊆ U := fun z hz => (hWP hz).1
  have hWU' : W ⊆ U := subset_closure.trans hWU
  have hφW : AnalyticOnNhd ℂ φ W := hφ.mono hWU'
  obtain ⟨τ, hτ, Hhead⟩ := exists_conformal_correction_of_critical_control_on_closure_order_le
    hW hV hK hKW hC hCV hφW hcritical hε
  have himageCompact : IsCompact (φ '' closure W) :=
    hWc.image_of_continuousOn (hφ.continuousOn.mono hWU)
  have himageΩ : φ '' closure W ⊆ Ω := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hWP hz).2
  obtain ⟨d, hd, Hinv⟩ := exists_uniform_inverse_tolerance_near_compact
    hΩ himageCompact himageΩ (half_pos hτ)
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro g χ hg hχ hχi hgclose hχclose hgvalue hχvalue horder
  let e := hχ.differentiableOn.toOpenPartialHomeomorph hΩ hχi
  have heS : e.source = Ω := rfl
  have heT : e.target = χ '' Ω := rfl
  have heval : (e : ℂ → ℂ) = χ := rfl
  have heinv : (e.symm : ℂ → ℂ) = Function.invFunOn χ Ω := rfl
  have heD : DifferentiableOn ℂ e e.source := hχ.differentiableOn
  have heI : DifferentiableOn ℂ e.symm e.target :=
    TauCeti.OpenPartialHomeomorph.differentiableOn_symm heD
  have Hnear : ∀ z ∈ W, g z ∈ e.target ∧ dist (e.symm (g z)) (φ z) < τ / 2 := by
    intro z hz
    apply Hinv χ hχ hχi
      (fun w hw => (hχclose w hw).trans (half_lt_self hd))
      (φ z) (mem_image_of_mem φ (subset_closure hz)) (g z)
    simpa only [norm_sub_rev] using (hgclose z (hWU' hz)).trans_lt (half_lt_self hd)
  let ψ : ℂ → ℂ := fun z => e.symm (g z)
  have hψ : AnalyticOnNhd ℂ ψ W :=
    (heI.analyticOnNhd e.open_target).comp (hg.mono hWU') (fun z hz => (Hnear z hz).1)
  have hcW : ∀ c ∈ C, c ∈ W := fun c hc => hKW (subset_closure (hCV hc))
  have hψvalue : ∀ c ∈ C, ψ c = φ c := by
    intro c hc
    have hcΩ : φ c ∈ e.source := himage (subset_closure (hCV hc))
    calc
      ψ c = e.symm (e (φ c)) := by
        change e.symm (g c) = e.symm (χ (φ c))
        rw [hgvalue c hc, hχvalue c hc]
      _ = φ c := e.left_inv hcΩ
  have hψorder : ∀ c ∈ C, analyticOrderAt (fun z => φ z - φ c) c ≤
      analyticOrderAt (fun z => ψ z - ψ c) c := by
    intro c hc
    have hgc : g c ∈ e.target := (Hnear c (hcW c hc)).1
    have hpost := analyticOrderAt_centered_postcomp_of_deriv_ne_zero
      (hg c (hWU' (hcW c hc))) (heI.analyticOnNhd e.open_target (g c) hgc)
      (TauCeti.deriv_ne_zero_of_injOn heI e.open_target e.symm.injOn hgc)
    rw [show analyticOrderAt (fun z => ψ z - ψ c) c =
      analyticOrderAt (fun z => g z - g c) c from hpost]
    exact horder c hc
  have hψclose : ∀ z ∈ W, ‖φ z - ψ z‖ ≤ τ := by
    intro z hz
    simpa only [ψ, dist_eq_norm, norm_sub_rev] using
      ((Hnear z hz).2.trans (half_lt_self hτ)).le
  obtain ⟨θ, hθA, hθi, hθW, hθinv, hθpair, hfixed⟩ :=
    Hhead ψ hψ hψvalue hψorder hψclose
  refine ⟨θ, hθA, hθi, hθW.mono_right hWU', hθinv, ?_, hfixed⟩
  intro z hz
  refine ⟨(hθpair z hz).1, ?_⟩
  calc
    g (θ z) = e (ψ (θ z)) := (e.right_inv (Hnear (θ z) (hθW hz)).1).symm
    _ = χ (φ z) := by rw [(hθpair z hz).2]; rfl

end FunctionTheory
