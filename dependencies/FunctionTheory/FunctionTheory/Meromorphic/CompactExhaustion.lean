import FunctionTheory.Meromorphic.SequenceLimit
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Meromorphic approximation on compact exhaustions preserves analytic
errors on the entire compact pieces, including their boundaries. The
exhaustion is required to be cofinal in interiors. -/
theorem exists_meromorphic_limit_on_compact_exhaustion
    (A : ℕ → Set ℂ) (hA : ∀ n, IsCompact (A n)) (hmono : Monotone A)
    (hcofinal : ∀ P : Set ℂ, IsCompact P → ∃ N, P ⊆ interior (A N))
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, MeromorphicOn (F n) univ)
    (herror : ∀ n, AnalyticOnNhd ℂ (fun z => F (n + 1) z - F n z) (A n))
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n z, z ∈ A n → ‖F (n + 1) z - F n z‖ ≤ b n) :
    ∃ f : ℂ → ℂ,
      MeromorphicOn f univ ∧
      (∀ n, TendstoUniformlyOn F f atTop (A n)) ∧
      (∀ n, AnalyticOnNhd ℂ (fun z => f z - F n z) (A n)) ∧
      (∀ n z, z ∈ A n → AnalyticAt ℂ (F n) z → AnalyticAt ℂ f z) ∧
      ∀ n z, z ∈ A n → ‖f z - F n z‖ ≤ ∑' i, b (n + i) := by
  have hcover : ∀ z : ℂ, ∃ n, z ∈ interior (A n) := by
    intro z
    obtain ⟨n, hn⟩ := hcofinal {z} isCompact_singleton
    exact ⟨n, hn (mem_singleton z)⟩
  obtain ⟨f, hfm, hflim, hfdiff, _, _⟩ :=
    exists_meromorphic_limit_of_summable_analytic_errors
      (fun n => interior (A n)) (fun _ => isOpen_interior)
      (fun n m hnm => interior_mono (hmono hnm)) hcover F hF
      (fun n => (herror n).mono interior_subset) b hb
      (fun n z hz => hbound n z (interior_subset hz))
  have hlimit : ∀ n, TendstoUniformlyOn F f atTop (A n) := by
    intro n
    obtain ⟨N, hN⟩ := hcofinal (A n) (hA n)
    exact (hflim N).mono hN
  have hpoint : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
    intro z
    obtain ⟨n, hn⟩ := hcover z
    exact (hflim n).tendsto_at hn
  have hfinite : ∀ n i, AnalyticOnNhd ℂ (fun z => F (n + i) z - F n z) (A n) := by
    intro n i
    induction i with
    | zero => simpa only [Nat.add_zero, sub_self] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (A n))
    | succ i ih =>
      have H := ((herror (n + i)).mono (hmono (Nat.le_add_right n i))).add ih
      change AnalyticOnNhd ℂ
        (fun z => (F (n + i + 1) z - F (n + i) z) + (F (n + i) z - F n z)) (A n) at H
      convert H using 1
      funext z
      simp only [Nat.add_assoc]
      abel
  have hdiff : ∀ n, AnalyticOnNhd ℂ (fun z => f z - F n z) (A n) := by
    intro n a ha
    obtain ⟨m, hm⟩ := hcover a
    let N := max n m
    have hNa : a ∈ interior (A N) := interior_mono (hmono (le_max_right n m)) hm
    have Hfin := hfinite n (N - n) a ha
    have hN : n + (N - n) = N := Nat.add_sub_of_le (le_max_left n m)
    rw [hN] at Hfin
    have H := (hfdiff N a hNa).add Hfin
    change AnalyticAt ℂ (fun z => (f z - F N z) + (F N z - F n z)) a at H
    convert H using 1
    funext z
    abel
  refine ⟨f, hfm, hlimit, hdiff, ?_, ?_⟩
  · intro n z hz hFn
    have H := (hdiff n z hz).add hFn
    change AnalyticAt ℂ (fun w => (f w - F n w) + F n w) z at H
    simpa only [sub_add_cancel] using H
  · intro n z hz
    have Hstep : ∀ i, dist (F (n + i) z) (F (n + (i + 1)) z) ≤ b (n + i) := by
      intro i
      simpa only [dist_eq_norm, Nat.add_assoc, norm_sub_rev] using
        hbound (n + i) z (hmono (Nat.le_add_right n i) hz)
    have Ht : Tendsto (fun i => F (n + i) z) atTop (𝓝 (f z)) := by
      simpa only [Function.comp_def, Nat.add_comm n] using
        (hpoint z).comp (tendsto_add_atTop_nat n)
    have H := dist_le_tsum_of_dist_le_of_tendsto₀ (fun i => b (n + i)) Hstep
      (hb.comp_injective (fun i j hij => by omega)) Ht
    simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using H

end FunctionTheory
