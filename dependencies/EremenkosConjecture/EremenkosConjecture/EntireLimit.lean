import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Abel

/-!
# Limits of successive entire approximations

Locally summable bounds on successive corrections give a locally uniform entire
limit. The bounds need hold only eventually on each neighbourhood, as in the
expanding approximation sets of Proposition 3.2.
-/

open Set Metric Filter
open scoped Topology

namespace EremenkosConjecture

noncomputable def correctionLimit (F : ℕ → ℂ → ℂ) (z : ℂ) : ℂ :=
  F 0 z + ∑' n, (F (n + 1) z - F n z)

theorem tendstoUniformlyOn_correctionLimit (F : ℕ → ℂ → ℂ) (A : Set ℂ)
    (ε : ℕ → ℝ) (hε : Summable ε)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ z ∈ A, ‖F (n + 1) z - F n z‖ ≤ ε n) :
    TendstoUniformlyOn F (correctionLimit F) atTop A := by
  have hsum := tendstoUniformlyOn_tsum_nat_eventually hε hbound
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hsum δ hδ] with n hn z hz
  have H := hn z hz
  have htel : ∑ i ∈ Finset.range n, (F (i + 1) z - F i z) = F n z - F 0 z :=
    Finset.sum_range_sub (fun i => F i z) n
  rw [htel] at H
  have heq : (∑' i, (F (i + 1) z - F i z)) - (F n z - F 0 z) =
      correctionLimit F z - F n z := by unfold correctionLimit; abel
  simpa only [dist_eq_norm, heq] using H

theorem exists_entire_limit_of_locally_summable_corrections
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, Differentiable ℂ (F n))
    (hlocal : ∀ z : ℂ, ∃ A ∈ 𝓝 z, ∃ ε : ℕ → ℝ, Summable ε ∧
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ A, ‖F (n + 1) w - F n w‖ ≤ ε n) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ TendstoLocallyUniformly F f atTop := by
  have hconv : TendstoLocallyUniformly F (correctionLimit F) atTop := by
    apply tendstoLocallyUniformly_of_forall_exists_nhds
    intro z
    obtain ⟨A, hA, ε, hε, hbound⟩ := hlocal z
    exact ⟨A, hA, tendstoUniformlyOn_correctionLimit F A ε hε hbound⟩
  refine ⟨correctionLimit F, ?_, hconv⟩
  rw [← differentiableOn_univ]
  exact hconv.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_univ

/-- A summable correction bound from stage `k` gives an explicit error bound
for the limiting function at that stage. -/
theorem limit_error_le_tsum {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)))
    (ε : ℕ → ℝ) (hε : Summable ε) (k : ℕ) (A : Set ℂ)
    (hbound : ∀ n ≥ k, ∀ z ∈ A, ‖F (n + 1) z - F n z‖ ≤ ε n) :
    ∀ z ∈ A, ‖f z - F k z‖ ≤ ∑' m, ε (k + m) := by
  intro z hz
  have htail : Tendsto (fun m => F (k + m) z) atTop (𝓝 (f z)) :=
    (hconv z).comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat k)
  have hsum : Summable (fun m => ε (k + m)) := hε.comp_injective (add_right_injective k)
  have hdist : ∀ m, dist (F (k + m) z) (F (k + (m + 1)) z) ≤ ε (k + m) := by
    intro m
    simpa only [dist_eq_norm, norm_sub_rev, Nat.add_assoc] using hbound (k + m) (by omega) z hz
  have H := dist_le_tsum_of_dist_le_of_tendsto₀ (fun m => ε (k + m)) hdist hsum htail
  simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using H

end EremenkosConjecture
