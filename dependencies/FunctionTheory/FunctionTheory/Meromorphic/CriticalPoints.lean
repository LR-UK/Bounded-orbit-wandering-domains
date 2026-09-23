import FunctionTheory.Analytic.CompactCriticalPoints
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter Metric Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Critical points cannot accumulate at either a regular nonconstant
point or a pole of a meromorphic function in normal form. -/
theorem eventually_deriv_ne_zero_of_meromorphicNFAt
    {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicNFAt f a)
    (hnc : AnalyticAt ℂ f a → ¬ ∀ᶠ z in 𝓝 a, f z=f a) :
    ∀ᶠ z in 𝓝[≠] a, deriv f z≠0 := by
  by_cases ha : AnalyticAt ℂ f a
  · have horder : analyticOrderAt (deriv f) a≠⊤ := by
      intro htop
      have h := ha.analyticOrderAt_deriv_add_one
      rw [htop,top_add] at h
      have he := analyticOrderAt_eq_top.mp h.symm
      apply hnc ha
      filter_upwards [he] with z hz
      exact sub_eq_zero.mp hz
    rcases ha.deriv.eventually_eq_zero_or_eventually_ne_zero with hz|hn
    · exact False.elim (horder (analyticOrderAt_eq_top.mpr hz))
    · exact hn
  · have hneg := ((meromorphicNFAt_iff_analyticAt_or.mp hf).resolve_left ha).2.1
    have hfinite : meromorphicOrderAt (deriv f) a≠⊤ := by
      lift meromorphicOrderAt f a to ℤ using hneg.ne_top with k hk
      have hkneg : k<0 := by exact_mod_cast hneg
      have hk0 : (k:ℂ)≠0 := by exact_mod_cast hkneg.ne
      rw [meromorphicOrderAt_deriv_eq_sub_one hk0 hk.symm]
      exact WithTop.coe_ne_top
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf.meromorphicAt.deriv).mp hfinite

/-- Finitely many critical points occur in a compact subset of the plane,
including when the compact set meets poles. The total derivative's internal
value at a pole may also be zero; the stronger displayed finite set safely
includes these isolated points. -/
theorem finite_deriv_zeros_of_meromorphicNFOn
    {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℂ} (hf : MeromorphicNFOn f K)
    (hnc : ∀ a∈K, AnalyticAt ℂ f a → ¬ ∀ᶠ z in 𝓝 a, f z=f a) :
    {a∈K | deriv f a=0}.Finite := by
  have hcod : ∀ᶠ a in codiscreteWithin K, deriv f a≠0 := by
    rw [eventually_codiscreteWithin_iff_forall_eventually_nhdsNE]
    intro a ha
    exact (eventually_deriv_ne_zero_of_meromorphicNFAt (hf ha) (hnc a ha)).mono
      (fun z hz _ => hz)
  have H := hK.finite_sdiff_of_mem_codiscreteWithin hcod
  convert H using 1
  ext a
  simp

/-- Any sequence of distinct critical points of a locally nonconstant
meromorphic plane function leaves every compact subset of the plane. -/
theorem tendsto_norm_atTop_of_injective_meromorphic_critical_points
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ)
    (hnc : ∀ a, AnalyticAt ℂ f a → ¬ ∀ᶠ z in 𝓝 a, f z=f a)
    (u : ℕ → ℂ) (hu : Injective u) (hcrit : ∀ n, deriv f (u n)=0) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  have hs := finite_deriv_zeros_of_meromorphicNFOn (isCompact_closedBall (0:ℂ) R)
    (fun z hz => hf (mem_univ z)) (fun z hz => hnc z)
  have he : ∀ᶠ n : ℕ in cofinite, u n∉{z∈closedBall (0:ℂ) R | deriv f z=0} :=
    hu.tendsto_cofinite.eventually hs.compl_mem_cofinite
  have he' : ∀ᶠ n : ℕ in atTop, u n∉{z∈closedBall (0:ℂ) R | deriv f z=0} := by
    simpa only [Nat.cofinite_eq_atTop] using he
  filter_upwards [he'] with n hn
  have hnot : u n∉closedBall (0:ℂ) R := fun hz => hn ⟨hz,hcrit n⟩
  have : R<‖u n‖ := by simpa using hnot
  exact this.le

end FunctionTheory
