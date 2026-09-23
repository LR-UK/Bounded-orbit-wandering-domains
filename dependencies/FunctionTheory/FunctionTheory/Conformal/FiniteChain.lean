import FunctionTheory.Conformal.StepCorrection

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- Finite conjugacy chains with explicit control of critical points on the
closed working sets. All interpolated points are fixed. The last map is
corrected directly; preceding maps are corrected relative to the next chart. -/
theorem exists_finite_conformal_chain_order_le
    (N : ℕ) (U V C : ℕ → Set ℂ) (φ : ℕ → ℂ → ℂ)
    (hU : ∀ n ≤ N, IsOpen (U n)) (hV : ∀ n ≤ N, IsOpen (V n))
    (hK : ∀ n ≤ N, IsCompact (closure (V n)))
    (hKU : ∀ n ≤ N, closure (V n) ⊆ U n)
    (hC : ∀ n ≤ N, (C n).Finite) (hCV : ∀ n ≤ N, C n ⊆ V n)
    (hφ : ∀ n ≤ N, AnalyticOnNhd ℂ (φ n) (U n))
    (hcritical : ∀ n ≤ N, ∀ z ∈ closure (V n), deriv (φ n) z = 0 → z ∈ C n)
    (himage : ∀ n < N, MapsTo (φ n) (closure (V n)) (V (n + 1)))
    (hmark : ∀ n < N, MapsTo (φ n) (C n) (C (n + 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℕ → ℂ → ℂ,
      (∀ n ≤ N, AnalyticOnNhd ℂ (f n) (U n)) →
      (∀ n ≤ N, ∀ c ∈ C n, f n c = φ n c) →
      (∀ n ≤ N, ∀ c ∈ C n,
        analyticOrderAt (fun z => φ n z - φ n c) c ≤
          analyticOrderAt (fun z => f n z - f n c) c) →
      (∀ n ≤ N, ∀ z ∈ U n, ‖φ n z - f n z‖ ≤ δ) →
      ∃ θ : ℕ → ℂ → ℂ,
        (∀ n ≤ N, AnalyticOnNhd ℂ (θ n) (V n) ∧ InjOn (θ n) (V n) ∧
          MapsTo (θ n) (V n) (U n) ∧
          DifferentiableOn ℂ (Function.invFunOn (θ n) (V n)) (θ n '' V n) ∧
          (∀ z ∈ V n, ‖θ n z - z‖ < ε) ∧ ∀ c ∈ C n, θ n c = c) ∧
        (∀ n < N, ∀ z ∈ V n, f n (θ n z) = θ (n + 1) (φ n z)) ∧
        ∀ z ∈ V N, f N (θ N z) = φ N z := by
  induction N generalizing U V C φ ε with
  | zero =>
    obtain ⟨δ, hδ, H⟩ := exists_conformal_correction_of_critical_control_on_closure_order_le
      (hU 0 le_rfl) (hV 0 le_rfl) (hK 0 le_rfl) (hKU 0 le_rfl)
      (hC 0 le_rfl) (hCV 0 le_rfl) (hφ 0 le_rfl) (hcritical 0 le_rfl) hε
    refine ⟨δ, hδ, ?_⟩
    intro f hf hvalue horder hclose
    obtain ⟨θ₀, hθA, hθi, hθU, hθinv, hθpair, hfixed⟩ :=
      H (f 0) (hf 0 le_rfl) (hvalue 0 le_rfl) (horder 0 le_rfl) (hclose 0 le_rfl)
    refine ⟨fun _ => θ₀, ?_, ?_, fun z hz => (hθpair z hz).2⟩
    · intro n hn
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      exact ⟨hθA, hθi, hθU, hθinv, fun z hz => (hθpair z hz).1, hfixed⟩
    · intro n hn
      exact (Nat.not_lt_zero n hn).elim
  | succ N ih =>
    have hzero : 0 ≤ N + 1 := Nat.zero_le _
    have hone : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    have hzeroLt : 0 < N + 1 := Nat.zero_lt_succ N
    obtain ⟨d₀, hd₀, Hhead⟩ := exists_backward_conformal_correction_tolerance
      (hU 0 hzero) (hV 0 hzero) (hV 1 hone)
      (hK 0 hzero) (hKU 0 hzero) (hC 0 hzero) (hCV 0 hzero)
      (hφ 0 hzero) (hcritical 0 hzero) (himage 0 hzeroLt) hε
    let η := min ε (d₀ / 2)
    have hη : 0 < η := lt_min hε (half_pos hd₀)
    obtain ⟨dT, hdT, Htail⟩ := ih
      (U := fun n => U (n + 1)) (V := fun n => V (n + 1))
      (C := fun n => C (n + 1)) (φ := fun n => φ (n + 1)) (ε := η)
      (fun n hn => hU (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hV (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hK (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hKU (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hC (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hCV (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hφ (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hcritical (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => himage (n + 1) (Nat.succ_lt_succ hn))
      (fun n hn => hmark (n + 1) (Nat.succ_lt_succ hn)) hη
    refine ⟨min d₀ dT, lt_min hd₀ hdT, ?_⟩
    intro f hf hvalue horder hclose
    obtain ⟨θT, hT, hTconj, hTlast⟩ := Htail (fun n => f (n + 1))
      (fun n hn => hf (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => hvalue (n + 1) (Nat.succ_le_succ hn))
      (fun n hn => horder (n + 1) (Nat.succ_le_succ hn))
      (fun n hn z hz => (hclose (n + 1) (Nat.succ_le_succ hn) z hz).trans (min_le_right _ _))
    obtain ⟨hχA, hχi, _, _, hχnear, hχfixed⟩ := hT 0 (Nat.zero_le N)
    have hχclose : ∀ w ∈ V 1, ‖θT 0 w - w‖ < d₀ := by
      intro w hw
      exact ((hχnear w hw).trans_le (min_le_right _ _)).trans (half_lt_self hd₀)
    obtain ⟨θ₀, hθA, hθi, hθU, hθinv, hθpair, hfixed⟩ :=
      Hhead (f 0) (θT 0) (hf 0 hzero) hχA hχi
        (fun z hz => (hclose 0 hzero z hz).trans (min_le_left _ _))
        hχclose (hvalue 0 hzero)
        (fun c hc => hχfixed (φ 0 c) (hmark 0 hzeroLt hc))
        (horder 0 hzero)
    let θ : ℕ → ℂ → ℂ
      | 0 => θ₀
      | n + 1 => θT n
    refine ⟨θ, ?_, ?_, ?_⟩
    · intro n hn
      cases n with
      | zero =>
        exact ⟨hθA, hθi, hθU, hθinv, fun z hz => (hθpair z hz).1, hfixed⟩
      | succ n =>
        obtain ⟨ha, hi, hu, hinv, hnear, hfix⟩ := hT n (Nat.succ_le_succ_iff.mp hn)
        exact ⟨ha, hi, hu, hinv,
          fun z hz => (hnear z hz).trans_le (min_le_left _ _), hfix⟩
    · intro n hn z hz
      cases n with
      | zero => exact (hθpair z hz).2
      | succ n => exact hTconj n (Nat.succ_lt_succ_iff.mp hn) z hz
    · exact hTlast

/-- The finite-chain theorem in the manuscript’s critical-multiplicity convention,
with the required closed-source critical control stated explicitly. -/
theorem exists_finite_conformal_chain
    (N : ℕ) (U V C : ℕ → Set ℂ) (φ : ℕ → ℂ → ℂ)
    (hU : ∀ n ≤ N, IsOpen (U n)) (hV : ∀ n ≤ N, IsOpen (V n))
    (hK : ∀ n ≤ N, IsCompact (closure (V n)))
    (hKU : ∀ n ≤ N, closure (V n) ⊆ U n)
    (hC : ∀ n ≤ N, (C n).Finite) (hCV : ∀ n ≤ N, C n ⊆ V n)
    (hφ : ∀ n ≤ N, AnalyticOnNhd ℂ (φ n) (U n))
    (hcritical : ∀ n ≤ N, ∀ z ∈ closure (V n), deriv (φ n) z = 0 → z ∈ C n)
    (himage : ∀ n < N, MapsTo (φ n) (closure (V n)) (V (n + 1)))
    (hmark : ∀ n < N, MapsTo (φ n) (C n) (C (n + 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℕ → ℂ → ℂ,
      (∀ n ≤ N, AnalyticOnNhd ℂ (f n) (U n)) →
      (∀ n ≤ N, ∀ c ∈ C n, f n c = φ n c) →
      (∀ n ≤ N, ∀ c ∈ V n, deriv (φ n) c = 0 →
        analyticOrderAt (deriv (f n)) c = analyticOrderAt (deriv (φ n)) c) →
      (∀ n ≤ N, ∀ z ∈ U n, ‖φ n z - f n z‖ ≤ δ) →
      ∃ θ : ℕ → ℂ → ℂ,
        (∀ n ≤ N, AnalyticOnNhd ℂ (θ n) (V n) ∧ InjOn (θ n) (V n) ∧
          MapsTo (θ n) (V n) (U n) ∧
          DifferentiableOn ℂ (Function.invFunOn (θ n) (V n)) (θ n '' V n) ∧
          (∀ z ∈ V n, ‖θ n z - z‖ < ε) ∧ ∀ c ∈ C n, θ n c = c) ∧
        (∀ n < N, ∀ z ∈ V n, f n (θ n z) = θ (n + 1) (φ n z)) ∧
        ∀ z ∈ V N, f N (θ N z) = φ N z := by
  obtain ⟨δ, hδ, H⟩ := exists_finite_conformal_chain_order_le N U V C φ
    hU hV hK hKU hC hCV hφ hcritical himage hmark hε
  refine ⟨δ, hδ, ?_⟩
  intro f hf hvalue hmult hclose
  apply H f hf hvalue _ hclose
  intro n hn c hc
  have hcU := hKU n hn (subset_closure (hCV n hn hc))
  by_cases hd : deriv (φ n) c = 0
  · exact (analyticOrderAt_sub_eq_of_deriv_order_eq (hφ n hn c hcU) (hf n hn c hcU)
      (hmult n hn c (hCV n hn hc) hd).symm).le
  · rw [(hφ n hn c hcU).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd]
    have hF : AnalyticAt ℂ (fun z => f n z - f n c) c := (hf n hn c hcU).sub analyticAt_const
    exact Order.one_le_iff_ne_zero.mpr (hF.analyticOrderAt_ne_zero.mpr (sub_self (f n c)))

end FunctionTheory
