import FunctionTheory.Smooth.ExtensionNorm

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

/-- Extend finitely many small holomorphic coordinate changes smoothly,
keeping the initial coordinate exactly the identity. All support
neighbourhoods are inputs before the smallness thresholds are selected. -/
theorem exists_smooth_finite_forward_extensions
    (N : ℕ) (X V C : ℕ → Set ℂ) (Θ : ℕ → ℂ ≃ₜ ℂ) (m : ℕ → ℕ) (ε : ℕ → ℝ)
    (hX : ∀ n≤N, IsCompact (X n)) (hV : ∀ n≤N, IsOpen (V n))
    (hXV : ∀ n≤N, Θ n '' X n ⊆ V n) (hCX : ∀ n≤N, C n ⊆ Θ n '' X n)
    (hΘ : ∀ n≤N, ContDiff ℝ (m n) (Θ n : ℂ → ℂ)) (hε : ∀ n≤N, 0<ε n) :
    ∃ η : ℕ → ℝ, (∀ n≤N, 0<η n) ∧
      ∀ θ : ℕ → ℂ → ℂ,
        (∀ n≤N, AnalyticOnNhd ℂ (θ n) (V n)) →
        (∀ n≤N, ∀ z∈V n, ‖θ n z-z‖≤η n) →
        (∀ n≤N, EqOn (θ n) id (C n)) → EqOn (θ 0) id (V 0) →
        ∃ E : ℕ → ℂ ≃ₜ ℂ, E 0=Homeomorph.refl ℂ ∧
          ∀ n≤N,
            ContDiff ℝ ∞ (E n : ℂ → ℂ) ∧ ContDiff ℝ ∞ ((E n).symm : ℂ → ℂ) ∧
            (∀ z∈Θ n '' X n, (E n : ℂ → ℂ) =ᶠ[𝓝 z] θ n) ∧
            EqOn (E n : ℂ → ℂ) id (C n) ∧
            (∀ z∉V n, E n z=z) ∧ HasCompactSupport (fun z => E n z-z) ∧
            tsupport (fun z => E n z-z) ⊆ V n ∧
            finiteSmoothNormOn (m n) (fun z => E n (Θ n z)-Θ n z) univ<ENNReal.ofReal (ε n) := by
  classical
  have H := fun i : Fin (N+1) => exists_holomorphic_extension_comp_in_Cm_norm
    (Θ i) (m i) (hΘ i (by omega)) (hX i (by omega)) (hV i (by omega))
    (hXV i (by omega)) (hε i (by omega))
  choose b hb Hb using H
  let η := fun n => if hn : n≤N then b ⟨n,by omega⟩ else 1
  refine ⟨η,?_,?_⟩
  · intro n hn
    simpa only [η,dif_pos hn] using hb ⟨n,by omega⟩
  · intro θ hθ hclose hmarks hzero
    have Hext := fun i : Fin (N+1) => Hb i (θ i) (hθ i (by omega))
      (fun z hz => by simpa only [η,dif_pos (show (i : ℕ)≤N by omega)] using hclose i (by omega) z hz)
    choose e hes hei heq heout hecomp hesupp henorm using Hext
    let E := fun n => if n=0 then Homeomorph.refl ℂ else
      if hn : n≤N then e ⟨n,by omega⟩ else Homeomorph.refl ℂ
    refine ⟨E,by simp [E],?_⟩
    intro n hn
    by_cases hn0 : n=0
    · subst n
      have hE : E 0=Homeomorph.refl ℂ := by simp [E]
      rw [hE]
      refine ⟨contDiff_id,contDiff_id,?_,fun _ _ => rfl,fun _ _ => rfl,?_,?_,?_⟩
      · intro z hz
        filter_upwards [(hV 0 (by omega)).mem_nhds (hXV 0 (by omega) hz)] with w hw
        exact (hzero hw).symm
      · simp [HasCompactSupport]
      · simp
      · have hfzero : (fun z : ℂ => (Homeomorph.refl ℂ) (Θ 0 z)-Θ 0 z)=(0 : ℂ → ℂ) := by
          funext z
          exact sub_self _
        rw [hfzero]
        apply finiteSmoothNormOn_lt_of_uniform_margin (hε 0 (by omega))
        intro k hk z hz
        rw [iteratedFDeriv_zero]
        simp only [Pi.zero_apply,norm_zero]
        exact div_nonneg (hε 0 (by omega)).le (by positivity)
    · have hE : E n=e ⟨n,by omega⟩ := by simp [E,hn0,hn]
      rw [hE]
      let i : Fin (N+1) := ⟨n,by omega⟩
      exact ⟨hes i,hei i,heq i,fun c hc => (heq i c (hCX n hn hc)).eq_of_nhds.trans (hmarks n hn hc),
        heout i,hecomp i,hesupp i,henorm i⟩

end FunctionTheory
