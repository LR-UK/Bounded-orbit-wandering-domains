import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic

open Set Filter Metric Function Bornology
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Every sufficiently large value is attained at a regular point of any
neighbourhood of a pole. This local result uses the open mapping theorem
on the reciprocal, not Picard's theorem. -/
theorem eventually_exists_regular_preimage_of_pole
    {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicNFAt f a)
    (hp : ¬ AnalyticAt ℂ f a) {V : Set ℂ} (hV : V∈𝓝 a) :
    ∀ᶠ b in cobounded ℂ, ∃ z∈V, z≠a ∧ AnalyticAt ℂ f z ∧ f z=b := by
  have hpole := (meromorphicNFAt_iff_analyticAt_or.mp hf).resolve_left hp
  have horder : meromorphicOrderAt f a<0 := hpole.2.1
  have hfzero : f a=0 := hpole.2.2
  have hinv : AnalyticAt ℂ f⁻¹ a := by
    apply hf.inv.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_inv]
    lift meromorphicOrderAt f a to ℤ using horder.ne_top with k hk
    norm_cast at horder ⊢
    omega
  have hinvzero : f⁻¹ a=0 := by simp [hfzero]
  have hnonzero : ∀ᶠ z in 𝓝[≠] a, f z≠0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf.meromorphicAt).mp horder.ne_top
  have hnc : ¬ ∀ᶠ z in 𝓝 a, f⁻¹ z=f⁻¹ a := by
    intro H
    have H' : ∀ᶠ z in 𝓝[≠] a, f z=0 := by
      filter_upwards [H.filter_mono nhdsWithin_le_nhds] with z hz
      simpa only [hinvzero,Pi.inv_apply,inv_eq_zero] using hz
    obtain ⟨z,hz,hz'⟩ := (H'.and hnonzero).exists
    exact hz' hz
  have hopen : 𝓝 (0:ℂ)≤map f⁻¹ (𝓝 a) := by
    simpa only [hinvzero] using hinv.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  have hreg : ∀ᶠ z in 𝓝 a, z≠a → AnalyticAt ℂ f z :=
    eventually_nhdsWithin_iff.mp hf.meromorphicAt.eventually_analyticAt
  let W : Set ℂ := {z | z∈V ∧ (z≠a → AnalyticAt ℂ f z)}
  have hW : W∈𝓝 a := by
    filter_upwards [hV,hreg] with z hz hzr
    exact ⟨hz,hzr⟩
  have himage : f⁻¹ '' W∈𝓝 (0:ℂ) := hopen (image_mem_map hW)
  have H := (tendsto_inv₀_cobounded (α := ℂ)).eventually himage
  filter_upwards [H,eventually_ne_cobounded (0:ℂ)] with b hb hb0
  obtain ⟨z,hz,hzeq⟩ := hb
  have hza : z≠a := by
    intro heq
    rw [heq,hinvzero] at hzeq
    exact hb0 (inv_eq_zero.mp hzeq.symm)
  refine ⟨z,hz.1,hza,hz.2 hza,?_⟩
  exact inv_injective hzeq

end FunctionTheory
