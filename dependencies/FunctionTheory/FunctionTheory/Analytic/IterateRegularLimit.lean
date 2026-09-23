import FunctionTheory.Analytic.SequenceLimit
import Mathlib.Logic.Function.Iterate

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Closed regularity domains prevent a limit of finite meromorphic orbits
from meeting a pole. Uniform convergence near each point then passes every
finite iterate to the limit, retaining regularity at all orbit inputs. -/
theorem tendsto_iterates_of_closed_regular_domains
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hF : ∀ a : ℂ, ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧
      TendstoUniformlyOn F f atTop U)
    (D : ℕ → Set ℂ) (n : ℕ)
    (hD : ∀ m < n, IsClosed (D m))
    (hf : ∀ m < n, AnalyticOnNhd ℂ f (D m))
    (horbit : ∀ m < n, ∀ᶠ j in atTop, (F j)^[m] z ∈ D m) :
    (∀ m ≤ n, Tendsto (fun j => (F j)^[m] z) atTop (𝓝 (f^[m] z))) ∧
    ∀ m < n, AnalyticAt ℂ f (f^[m] z) := by
  have hlim : ∀ m ≤ n,
      Tendsto (fun j => (F j)^[m] z) atTop (𝓝 (f^[m] z)) := by
    intro m hm
    induction m with
    | zero => exact tendsto_const_nhds
    | succ m ih =>
      have him := ih (by omega)
      have hmem := (hD m (by omega)).mem_of_tendsto him (horbit m (by omega))
      obtain ⟨U,hU,ha,hconv⟩ := hF (f^[m] z)
      simpa only [Function.iterate_succ_apply'] using
        tendsto_uniformlyOn_at_moving_points hU hconv him ha
          (hf m (by omega) _ hmem).continuousAt
  exact ⟨hlim,fun m hm => hf m hm _ ((hD m hm).mem_of_tendsto
    (hlim m hm.le) (horbit m hm))⟩

end FunctionTheory
