import FunctionTheory.Topology.FiniteComposition
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open Set Filter Function
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The local open mapping theorem preserves local nonconstancy under
composition. The outer map need not be differentiable for this assertion. -/
theorem locally_nonconstant_comp_of_analyticAt {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hfnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    (hgnc : ¬ ∀ᶠ w in 𝓝 (f a), g w = g (f a)) :
    ¬ ∀ᶠ z in 𝓝 a, g (f z) = g (f a) := by
  intro h
  have H : ∀ᶠ w in map f (𝓝 a), g w = g (f a) := h
  exact hgnc ((hf.eventually_constant_or_nhds_le_map_nhds.resolve_left hfnc) H)

/-- Analyticity of a finite composition only requires analytic germs along
the orbit of the base point. -/
theorem analyticAt_finiteComposition (g : ℕ → ℂ → ℂ) (n : ℕ) {a : ℂ}
    (hg : ∀ k < n, AnalyticAt ℂ (g k) (finiteComposition g k a)) :
    AnalyticAt ℂ (finiteComposition g n) a := by
  induction n with
  | zero => exact analyticAt_id
  | succ n ih =>
    change AnalyticAt ℂ (g n ∘ finiteComposition g n) a
    exact (hg n (Nat.lt_succ_self n)).comp
      (ih (fun k hk => hg k (Nat.lt_succ_of_lt hk)))

/-- A finite composition of locally nonconstant analytic germs is locally
nonconstant, including when critical points occur along the orbit. -/
theorem locally_nonconstant_finiteComposition (g : ℕ → ℂ → ℂ) (n : ℕ) {a : ℂ}
    (hg : ∀ k < n, AnalyticAt ℂ (g k) (finiteComposition g k a))
    (hnc : ∀ k < n, ¬ ∀ᶠ z in 𝓝 (finiteComposition g k a),
      g k z = g k (finiteComposition g k a)) :
    ¬ ∀ᶠ z in 𝓝 a, finiteComposition g n z = finiteComposition g n a := by
  induction n with
  | zero =>
    intro H
    have HE : (id : ℂ → ℂ) =ᶠ[𝓝 a] (fun _ => a) := by
      simpa only [Filter.EventuallyEq, finiteComposition, id_eq] using H
    have HD := HE.deriv_eq
    simp at HD
  | succ n ih =>
    change ¬ ∀ᶠ z in 𝓝 a, g n (finiteComposition g n z) = g n (finiteComposition g n a)
    exact locally_nonconstant_comp_of_analyticAt
      (analyticAt_finiteComposition g n (fun k hk => hg k (Nat.lt_succ_of_lt hk)))
      (ih (fun k hk => hg k (Nat.lt_succ_of_lt hk))
        (fun k hk => hnc k (Nat.lt_succ_of_lt hk)))
      (hnc n (Nat.lt_succ_self n))

/-- Neighbourhood conjugacies compose along a finite orbit. The identity is
retained as an equality of germs, rather than just at the base point. -/
theorem finiteComposition_conjugacy_eventually
    (f g α : ℕ → ℂ → ℂ) (n : ℕ) {a : ℂ}
    (hf : ∀ k < n, AnalyticAt ℂ (f k) (finiteComposition f k a))
    (hconj : ∀ k < n,
      (fun z => g k (α k z)) =ᶠ[𝓝 (finiteComposition f k a)]
        (fun z => α (k + 1) (f k z))) :
    (fun z => finiteComposition g n (α 0 z)) =ᶠ[𝓝 a]
      (fun z => α n (finiteComposition f n z)) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have HI := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      (fun k hk => hconj k (Nat.lt_succ_of_lt hk))
    have Hnew := (analyticAt_finiteComposition f n
      (fun k hk => hf k (Nat.lt_succ_of_lt hk))).continuousAt.eventually
        (hconj n (Nat.lt_succ_self n))
    filter_upwards [HI, Hnew] with z hz hz'
    change g n (finiteComposition g n (α 0 z)) = α (n + 1) (f n (finiteComposition f n z))
    rw [hz]
    exact hz'

end FunctionTheory
