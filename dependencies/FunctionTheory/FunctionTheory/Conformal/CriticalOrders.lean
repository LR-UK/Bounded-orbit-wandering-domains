import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Basic

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Containment of the critical set in a finite set excludes locally constant
germs on an open plane domain. Thus the correction lemma's original finite
critical-set hypothesis already implies local nonconstancy. -/
theorem locally_nonconstant_of_finite_critical_set
    {U C : Set ℂ} (hU : IsOpen U) (hC : C.Finite) {f : ℂ → ℂ}
    (hcritical : ∀ z ∈ U, deriv f z = 0 → z ∈ C) :
    ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro a ha hconst
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := hconst
  have hmem : C ∈ 𝓝 a := by
    filter_upwards [hU.mem_nhds ha, heq.deriv] with z hzU hdz
    apply hcritical z hzU
    simpa only [deriv_const] using hdz
  exact hC.not_infinite (infinite_of_mem_nhds a hmem)

/-- Equality of critical multiplicities gives equality of centered local
degrees. Both sides use Mathlib's analytic-order convention. -/
theorem analyticOrderAt_sub_eq_of_deriv_order_eq
    {f g : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt (deriv f) a = analyticOrderAt (deriv g) a) :
    analyticOrderAt (fun z => f z - f a) a =
      analyticOrderAt (fun z => g z - g a) a := by
  calc
    analyticOrderAt (fun z => f z - f a) a = analyticOrderAt (deriv f) a + 1 :=
      hf.analyticOrderAt_deriv_add_one.symm
    _ = analyticOrderAt (deriv g) a + 1 := by rw [horder]
    _ = analyticOrderAt (fun z => g z - g a) a := hg.analyticOrderAt_deriv_add_one

end FunctionTheory
