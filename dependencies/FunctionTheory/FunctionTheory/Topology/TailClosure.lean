import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Points approaching a limit and lying at vanishing distance from a
sequence of sets put that limit in the closure of every tail union.
No compactness assumption on those sets is needed. -/
theorem mem_closure_iUnion_tail_of_approximations
    {α : Type*} [PseudoMetricSpace α] {a : α} {x : ℕ → α}
    (hx : Tendsto x atTop (𝓝 a)) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (A : ℕ → Set α)
    (hA : ∀ᶠ j in atTop, ∃ y ∈ A j, dist (x j) y ≤ r j)
    (j₀ : ℕ) : a ∈ closure (⋃ j, ⋃ (_ : j₀ ≤ j), A j) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have he : 0 < ε / 2 := half_pos hε
  have Hx := Metric.tendsto_nhds.mp hx (ε / 2) he
  have Hr : ∀ᶠ j in atTop, r j < ε / 2 := (tendsto_order.mp hr).2 _ he
  obtain ⟨j, hj, hxj, hrj, haj⟩ :=
    ((eventually_ge_atTop j₀).and (Hx.and (Hr.and hA))).exists
  obtain ⟨y, hy, hdist⟩ := haj
  refine ⟨y, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hy⟩⟩, ?_⟩
  calc
    dist a y ≤ dist a (x j) + dist (x j) y := dist_triangle _ _ _
    _ ≤ dist a (x j) + r j := add_le_add le_rfl hdist
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hxj) hrj
    _ = ε := add_halves ε

end FunctionTheory
