import FunctionTheory.Conformal.FiniteChain
import FunctionTheory.Conformal.CriticalNeighborhoodChain
import FunctionTheory.Smooth.ExtensionNorm
import Mathlib.Tactic

open Set Function Filter
open scoped Topology ContDiff

namespace FunctionTheory

set_option autoImplicit false

private theorem exists_pos_le_initial_segment (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ n ≤ N, 0 < b n) :
    ∃ c > 0, ∀ n ≤ N, c ≤ b n := by
  induction N with
  | zero =>
    refine ⟨b 0, hb 0 le_rfl, ?_⟩
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    exact le_rfl
  | succ N ih =>
    obtain ⟨c, hc, Hc⟩ := ih (fun n hn => hb n (hn.trans (Nat.le_succ N)))
    refine ⟨min c (b (N + 1)), lt_min hc (hb (N + 1) le_rfl), ?_⟩
    intro n hn
    by_cases h : n ≤ N
    · exact (min_le_left _ _).trans (Hc n h)
    · have hnN : n = N + 1 := by omega
      subst n
      exact min_le_right _ _

/-- A finite row of compact holomorphic models can be corrected by global
smooth changes of coordinates. The changes preserve the marked points,
are conformal near the current compact sets, and have arbitrarily small
C^m error after composition with the given preceding coordinates.
All row conjugacies hold on neighbourhoods of the compact sets. -/
theorem exists_smooth_finite_conformal_chain
    (N : ℕ) (K U C : ℕ → Set ℂ) (g : ℕ → ℂ → ℂ)
    (Θ : ℕ → ℂ ≃ₜ ℂ) (m : ℕ → ℕ) (ε : ℕ → ℝ)
    (hK : ∀ n ≤ N, IsCompact (K n)) (hU : ∀ n ≤ N, IsOpen (U n))
    (hYU : ∀ n ≤ N, Θ n '' K n ⊆ U n)
    (hC : ∀ n ≤ N, (C n).Finite) (hCY : ∀ n ≤ N, C n ⊆ Θ n '' K n)
    (hg : ∀ n ≤ N, AnalyticOnNhd ℂ (g n) (U n))
    (hnc : ∀ n ≤ N, ∀ a ∈ Θ n '' K n, ¬ ∀ᶠ z in 𝓝 a, g n z = g n a)
    (hcritical : ∀ n ≤ N, ∀ a ∈ Θ n '' K n, deriv (g n) a = 0 → a ∈ C n)
    (himage : ∀ n < N, MapsTo (g n) (Θ n '' K n) (Θ (n + 1) '' K (n + 1)))
    (hmark : ∀ n < N, MapsTo (g n) (C n) (C (n + 1)))
    (hΘ : ∀ n ≤ N, ContDiff ℝ (m n) (Θ n : ℂ → ℂ))
    (hε : ∀ n ≤ N, 0 < ε n) :
    ∃ δ > 0, ∀ f : ℕ → ℂ → ℂ,
      (∀ n ≤ N, AnalyticOnNhd ℂ (f n) (U n)) →
      (∀ n ≤ N, ∀ c ∈ C n, f n c = g n c) →
      (∀ n ≤ N, ∀ c ∈ C n,
        analyticOrderAt (fun z => g n z - g n c) c ≤
          analyticOrderAt (fun z => f n z - f n c) c) →
      (∀ n ≤ N, ∀ z ∈ U n, ‖g n z - f n z‖ ≤ δ) →
      ∃ E : ℕ → ℂ ≃ₜ ℂ,
        (∀ n ≤ N,
          ContDiff ℝ ∞ (E n : ℂ → ℂ) ∧ ContDiff ℝ ∞ ((E n).symm : ℂ → ℂ) ∧
          AnalyticOnNhd ℂ (E n : ℂ → ℂ) (Θ n '' K n) ∧
          (∀ a ∈ Θ n '' K n, deriv (E n : ℂ → ℂ) a ≠ 0) ∧
          (∀ c ∈ C n, E n c = c) ∧
          (∀ z ∉ U n, E n z = z) ∧
          HasCompactSupport (fun z => E n z - z) ∧
          tsupport (fun z => E n z - z) ⊆ U n ∧
          finiteSmoothNormOn (m n) (fun z => E n (Θ n z) - Θ n z) univ <
            ENNReal.ofReal (ε n)) ∧
        (∀ n < N, ∀ a ∈ Θ n '' K n,
          (fun z => f n (E n z)) =ᶠ[𝓝 a] (fun z => E (n + 1) (g n z))) ∧
        ∀ a ∈ Θ N '' K N, (fun z => f N (E N z)) =ᶠ[𝓝 a] g N := by
  classical
  let Y : ℕ → Set ℂ := fun n => Θ n '' K n
  have hY : ∀ n ≤ N, IsCompact (Y n) :=
    fun n hn => (hK n hn).image (Θ n).continuous
  obtain ⟨V, HV, HVmap⟩ := exists_finite_critical_neighborhood_chain
    N Y U C g hY hU hYU hg hnc hcritical himage
  have Hext := fun n : Fin (N + 1) =>
    exists_holomorphic_extension_comp_in_Cm_norm
      (Θ n) (m n) (hΘ n (Nat.le_of_lt_succ n.isLt))
      (hK n (Nat.le_of_lt_succ n.isLt))
      (HV n (Nat.le_of_lt_succ n.isLt)).1
      (HV n (Nat.le_of_lt_succ n.isLt)).2.1
      (hε n (Nat.le_of_lt_succ n.isLt))
  choose η hη Hη using Hext
  let B : ℕ → ℝ := fun n => if hn : n ≤ N then η ⟨n, Nat.lt_succ_of_le hn⟩ else 1
  have hB : ∀ n ≤ N, 0 < B n := by
    intro n hn
    simpa only [B, dif_pos hn] using hη ⟨n, Nat.lt_succ_of_le hn⟩
  obtain ⟨η₀, hη₀, Hη₀⟩ := exists_pos_le_initial_segment N B hB
  have hηle : ∀ n (hn : n ≤ N), η₀ ≤ η ⟨n, Nat.lt_succ_of_le hn⟩ := by
    intro n hn
    simpa only [B, dif_pos hn] using Hη₀ n hn
  obtain ⟨δ, hδ, Hδ⟩ := exists_finite_conformal_chain_order_le N U V C g
    hU (fun n hn => (HV n hn).1) (fun n hn => (HV n hn).2.2.2.1)
    (fun n hn => (HV n hn).2.2.1) hC
    (fun n hn => (hCY n hn).trans (HV n hn).2.1) hg
    (fun n hn => (HV n hn).2.2.2.2) HVmap hmark hη₀
  refine ⟨δ, hδ, ?_⟩
  intro f hf hvalue horder hclose
  obtain ⟨θ, Hθ, Hchain, Hterminal⟩ := Hδ f hf hvalue horder hclose
  have HE := fun n : Fin (N + 1) =>
    Hη n (θ n) (Hθ n (Nat.le_of_lt_succ n.isLt)).1
      (fun z hz => ((Hθ n (Nat.le_of_lt_succ n.isLt)).2.2.2.2.1 z hz).le.trans
        (hηle n (Nat.le_of_lt_succ n.isLt)))
  choose e hes hei heq heout hec hesupp henorm using HE
  let E : ℕ → ℂ ≃ₜ ℂ := fun n =>
    if hn : n ≤ N then e ⟨n, Nat.lt_succ_of_le hn⟩ else Homeomorph.refl ℂ
  have hE : ∀ n (hn : n ≤ N), E n = e ⟨n, Nat.lt_succ_of_le hn⟩ := by
    intro n hn
    simp only [E, dif_pos hn]
  have HEeq : ∀ n ≤ N, ∀ a ∈ Y n,
      (E n : ℂ → ℂ) =ᶠ[𝓝 a] θ n := by
    intro n hn a ha
    rw [hE n hn]
    exact heq ⟨n, Nat.lt_succ_of_le hn⟩ a ha
  refine ⟨E, ?_, ?_, ?_⟩
  · intro n hn
    let i : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    obtain ⟨hθA, hθi, _, _, hθclose, hθfixed⟩ := Hθ n hn
    rw [hE n hn]
    refine ⟨hes i, hei i, ?_, ?_, ?_, ?_, hec i, ?_, henorm i⟩
    · intro a ha
      exact (hθA a ((HV n hn).2.1 ha)).congr (heq i a ha).symm
    · intro a ha
      rw [(heq i a ha).deriv_eq]
      exact TauCeti.deriv_ne_zero_of_injOn hθA.differentiableOn
        (HV n hn).1 hθi ((HV n hn).2.1 ha)
    · intro c hc
      exact (heq i c (hCY n hn hc)).eq_of_nhds.trans (hθfixed c hc)
    · intro z hz
      exact heout i z (fun hzV => hz ((HV n hn).2.2.1 (subset_closure hzV)))
    · exact (hesupp i).trans (subset_closure.trans (HV n hn).2.2.1)
  · intro n hn a ha
    have hnle : n ≤ N := Nat.le_of_lt hn
    have hnext : n + 1 ≤ N := Nat.succ_le_of_lt hn
    have Hnext : ∀ᶠ z in 𝓝 a, E (n + 1) (g n z) = θ (n + 1) (g n z) :=
      (hg n hnle a (hYU n hnle ha)).continuousAt.eventually
        (HEeq (n + 1) hnext (g n a) (himage n hn ha))
    filter_upwards [HEeq n hnle a ha, Hnext,
      (HV n hnle).1.mem_nhds ((HV n hnle).2.1 ha)] with z hz hnextz hzV
    rw [hz, hnextz]
    exact Hchain n hn z hzV
  · intro a ha
    filter_upwards [HEeq N le_rfl a ha,
      (HV N le_rfl).1.mem_nhds ((HV N le_rfl).2.1 ha)] with z hz hzV
    rw [hz]
    exact Hterminal z hzV

end FunctionTheory
