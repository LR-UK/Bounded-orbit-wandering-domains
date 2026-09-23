import FunctionTheory.Analytic.FiniteComposition
import FunctionTheory.Topology.IterateApproximationDomains

open Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Matching the germs at all points of a regular finite orbit preserves
the germ of the whole iterate. -/
theorem iterate_germ_eq_of_regular_orbit_germs
    {f g : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : ∀ j < n, AnalyticAt ℂ f (f^[j] a))
    (heq : ∀ j < n, g =ᶠ[𝓝 (f^[j] a)] f) :
    g^[n] =ᶠ[𝓝 a] f^[n] := by
  have H := finiteComposition_conjugacy_eventually
    (fun _ => f) (fun _ => g) (fun _ => id) n (a := a)
    (by simpa only [finiteComposition_const_eq_iterate] using hf)
    (by
      intro j hj
      simpa only [finiteComposition_const_eq_iterate,id_eq] using heq j hj)
  simpa only [finiteComposition_const_eq_iterate,id_eq] using H

end FunctionTheory
