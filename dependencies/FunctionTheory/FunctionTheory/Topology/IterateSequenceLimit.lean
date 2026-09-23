import FunctionTheory.Analytic.SequenceLimit
import Mathlib.Logic.Function.Iterate

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Uniform convergence on some open neighbourhood of each point and
continuity of the limit imply convergence of every finite iterate.
No regularity of the approximating functions is required. -/
theorem tendsto_iterates_of_neighborhood_uniform_limit
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hf : Continuous f)
    (hF : ∀ a : ℂ, ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧
      TendstoUniformlyOn F f atTop U) :
    ∀ n z, Tendsto (fun j => (F j)^[n] z) atTop (𝓝 (f^[n] z)) := by
  intro n
  induction n with
  | zero => intro z; exact tendsto_const_nhds
  | succ n ih =>
    intro z
    obtain ⟨U,hU,ha,hconv⟩ := hF (f^[n] z)
    simpa only [Function.iterate_succ_apply'] using
      tendsto_uniformlyOn_at_moving_points hU hconv (ih z) ha hf.continuousAt

end FunctionTheory
