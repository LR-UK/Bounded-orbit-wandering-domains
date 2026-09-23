import FunctionTheory.Topology.CountableDisc
import Mathlib.Analysis.Meromorphic.Basic

open Set Metric Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- The finite-valued regular set of a globally meromorphic function is
connected; the pole set is countable. -/
theorem isConnected_analyticAt_of_meromorphic {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    IsConnected {z | AnalyticAt ℂ f z} := by
  have hs : {z | AnalyticAt ℂ f z}ᶜ.Countable := by
    simpa only [inter_univ] using hf.countable_compl_analyticAt_inter
  simpa only [compl_compl] using hs.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)

end FunctionTheory
