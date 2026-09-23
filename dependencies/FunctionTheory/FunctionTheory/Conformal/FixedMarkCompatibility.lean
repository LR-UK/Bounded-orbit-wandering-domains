import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Set Metric

namespace FunctionTheory

set_option autoImplicit false

/-- An adaptive tolerance can exclude a reference coordinate that moves a
required mark. The tolerance may depend on the already chosen coordinate.
This is used for inadmissible finite histories in the univalent triangle. -/
theorem exists_tolerance_forces_fixed_marks
    (θ : ℂ ≃ₜ ℂ) {U C : Set ℂ} {g : ℂ → ℂ}
    (hi : InjOn g U) (hCU : C ⊆ U) (hCiU : MapsTo θ.symm C U) :
    ∃ δ>0, ∀ f : ℂ → ℂ, EqOn f g C →
      (∀ c∈C, dist (f c) (g (θ.symm c))<δ) → EqOn (θ : ℂ → ℂ) id C := by
  classical
  by_cases hfix : EqOn (θ : ℂ → ℂ) id C
  · exact ⟨1,one_pos,fun _ _ _ => hfix⟩
  · obtain ⟨c,hc,hcne⟩ : ∃ c∈C, θ c≠c := by
      simpa only [EqOn,id_eq,not_forall,exists_prop] using hfix
    have hne : g c≠g (θ.symm c) := by
      intro h
      have hci := hi (hCU hc) (hCiU hc) h
      have H := congrArg θ hci
      simp only [θ.apply_symm_apply] at H
      exact hcne H
    have hd : 0<dist (g c) (g (θ.symm c)) := dist_pos.mpr hne
    refine ⟨dist (g c) (g (θ.symm c))/2,half_pos hd,?_⟩
    intro f hf hclose
    have H := hclose c hc
    rw [hf hc] at H
    linarith

/-- Fixed terminal marks propagate backwards along an injective
conjugacy step, provided the maps agree at the source marks. -/
theorem fixes_marks_of_injective_conjugacy
    {X : Type*} {f g α β : X → X} {C D U : Set X}
    (hi : InjOn f U) (hCU : C ⊆ U) (hαU : MapsTo α C U)
    (hmarks : MapsTo g C D) (hβ : EqOn β id D)
    (hfg : EqOn f g C) (hconj : EqOn (f ∘ α) (β ∘ g) C) : EqOn α id C := by
  intro c hc
  apply hi (hαU hc) (hCU hc)
  exact (hconj hc).trans ((hβ (hmarks hc)).trans (hfg hc).symm)

end FunctionTheory
