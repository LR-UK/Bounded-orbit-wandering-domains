import FunctionTheory.Analytic.SequenceLimit
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Meromorphic maps with summably bounded analytic errors on an increasing
open exhaustion have a meromorphic limit. The error from any fixed stage
extends analytically throughout that stage's domain, including its poles. -/
theorem exists_meromorphic_limit_of_summable_analytic_errors
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : ∀ z : ℂ, ∃ n, z ∈ U n)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, MeromorphicOn (F n) univ)
    (herror : ∀ n, AnalyticOnNhd ℂ (fun z => F (n + 1) z - F n z) (U n))
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n z, z ∈ U n → ‖F (n + 1) z - F n z‖ ≤ b n) :
    ∃ f : ℂ → ℂ,
      MeromorphicOn f univ ∧
      (∀ n, TendstoUniformlyOn F f atTop (U n)) ∧
      (∀ n, AnalyticOnNhd ℂ (fun z => f z - F n z) (U n)) ∧
      (∀ n z, z ∈ U n → AnalyticAt ℂ (F n) z → AnalyticAt ℂ f z) ∧
      ∀ n z, z ∈ U n → ‖f z - F n z‖ ≤ ∑' i, b (n + i) := by
  classical
  let G : ℕ → ℕ → ℂ → ℂ := fun N i z => F (N + i) z - F N z
  have hG : ∀ N i, AnalyticOnNhd ℂ (G N i) (U N) := by
    intro N i
    induction i with
    | zero => simpa only [G, Nat.add_zero, sub_self] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (U N))
    | succ i ih =>
      have H := ((herror (N + i)).mono (hmono (Nat.le_add_right N i))).add ih
      have Heq : (fun z => (F (N + i + 1) z - F (N + i) z) + G N i z) =
          G N (i + 1) := by
        funext z
        dsimp only [G]
        rw [Nat.add_assoc]
        abel
      change AnalyticOnNhd ℂ
        (fun z => (F (N + i + 1) z - F (N + i) z) + G N i z) (U N) at H
      rwa [Heq] at H
  have hGb : ∀ N i z, z ∈ U N →
      ‖G N (i + 1) z - G N i z‖ ≤ b (N + i) := by
    intro N i z hz
    have Heq : G N (i + 1) z - G N i z = F (N + i + 1) z - F (N + i) z := by
      dsimp only [G]
      rw [Nat.add_assoc]
      abel
    rw [Heq]
    exact hbound (N + i) z (hmono (Nat.le_add_right N i) hz)
  have Hlocal : ∀ N, ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (U N) ∧ TendstoUniformlyOn (G N) g atTop (U N) := by
    intro N
    exact exists_analytic_uniform_limit_of_summable_increments (hU N)
      (G N) (hG N) (fun i => b (N + i))
      (hb.comp_injective (fun i j hij => by omega)) (hGb N)
  choose g hg hglim using Hlocal
  have Hlim : ∀ N, TendstoUniformlyOn F (fun z => F N z + g N z) atTop (U N) := by
    intro N
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨I, hI⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp (hglim N) ε hε)
    apply eventually_atTop.mpr
    refine ⟨N + I, ?_⟩
    intro j hj z hz
    have H := hI (j - N) (by omega) z hz
    have Heq : G N (j - N) z = F j z - F N z := by
      dsimp only [G]
      rw [Nat.add_sub_of_le (by omega : N ≤ j)]
    rw [Heq] at H
    have Hd : dist (F N z + g N z) (F j z) = dist (g N z) (F j z - F N z) := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rwa [Hd]
  have Hex : ∀ z : ℂ, ∃ v : ℂ, Tendsto (fun i => F i z) atTop (𝓝 v) := by
    intro z
    obtain ⟨N, hz⟩ := hcover z
    exact ⟨F N z + g N z, (Hlim N).tendsto_at hz⟩
  choose f hf using Hex
  have hagree : ∀ N, EqOn f (fun z => F N z + g N z) (U N) := by
    intro N z hz
    exact tendsto_nhds_unique (hf z) ((Hlim N).tendsto_at hz)
  have hlocalEq : ∀ N a, a ∈ U N →
      f =ᶠ[𝓝 a] (fun z => F N z + g N z) := by
    intro N a ha
    filter_upwards [(hU N).mem_nhds ha] with z hz using hagree N hz
  have hmero : MeromorphicOn f univ := by
    intro a _
    obtain ⟨N, ha⟩ := hcover a
    exact ((hF N a (mem_univ a)).add ((hg N a ha).meromorphicAt)).congr
      ((hlocalEq N a ha).symm.filter_mono nhdsWithin_le_nhds)
  refine ⟨f, hmero, ?_, ?_, ?_, ?_⟩
  · intro N
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (Hlim N) ε hε] with i hi
    intro z hz
    rw [hagree N hz]
    exact hi z hz
  · intro N a ha
    have H : g N =ᶠ[𝓝 a] (fun z => f z - F N z) := by
      filter_upwards [hlocalEq N a ha] with z hz
      rw [hz]
      abel
    exact (hg N a ha).congr H
  · intro N a ha hFa
    exact (hFa.add (hg N a ha)).congr (hlocalEq N a ha).symm
  · intro N z hz
    have Hstep : ∀ i, dist (F (N + i) z) (F (N + (i + 1)) z) ≤ b (N + i) := by
      intro i
      have H := hbound (N + i) z (hmono (Nat.le_add_right N i) hz)
      simpa only [dist_eq_norm, Nat.add_assoc, norm_sub_rev] using H
    have Ht : Tendsto (fun i => F (N + i) z) atTop (𝓝 (f z)) := by
      simpa only [Function.comp_def, Nat.add_comm N] using (hf z).comp (tendsto_add_atTop_nat N)
    have H := dist_le_tsum_of_dist_le_of_tendsto₀ (fun i => b (N + i)) Hstep
      (hb.comp_injective (fun i j hij => by omega)) Ht
    simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using H

end FunctionTheory
