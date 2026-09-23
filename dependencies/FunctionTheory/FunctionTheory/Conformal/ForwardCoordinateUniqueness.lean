import FunctionTheory.Analytic.FiniteComposition
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

open Set Function Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Once the initial coordinate is fixed, a univalent finite conjugacy
has the canonical forward-composition formula on a neighbourhood of
each point. This retains an equality of germs, including at boundary
points of the compact model. -/
theorem forward_coordinate_eventually_eq_prefix
    (f g α : ℕ → ℂ → ℂ) (n : ℕ) {a : ℂ}
    (hg : ∀ k<n, AnalyticAt ℂ (g k) (finiteComposition g k a))
    (hconj : ∀ k<n,
      (fun z => f k (α k z)) =ᶠ[𝓝 (finiteComposition g k a)]
        (fun z => α (k+1) (g k z)))
    (hzero : α 0 =ᶠ[𝓝 a] id)
    (e : OpenPartialHomeomorph ℂ ℂ) (ha : a∈e.source)
    (he : (e : ℂ → ℂ)=finiteComposition g n) :
    α n =ᶠ[𝓝 (e a)] (finiteComposition f n ∘ e.symm) := by
  have H := finiteComposition_conjugacy_eventually g f α n hg hconj
  have H' : finiteComposition f n =ᶠ[𝓝 a] (fun z => α n (e z)) := by
    filter_upwards [H,hzero] with z hz hz0
    rw [hz0] at hz
    simpa only [id_eq,he] using hz
  have ht : e a∈e.target := e.map_source ha
  have hcont : ContinuousAt e.symm (e a) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds ht)
  have hinv : e.symm (e a)=a := e.left_inv ha
  have Hp := hcont.eventually (hinv.symm ▸ H')
  filter_upwards [Hp,e.open_target.mem_nhds ht] with z hz hzT
  rw [e.right_inv hzT] at hz
  exact hz.symm

end FunctionTheory
