import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

open Set Metric Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Proper maps of the open disc send points near its boundary uniformly
near the boundary. The formulation uses maps on their actual domains and
requires no prior boundary extension or holomorphicity. -/
theorem exists_boundary_collar_of_isProperMap_disc
    (F : ball (0:ℂ) 1 → ball (0:ℂ) 1) (hF : IsProperMap F)
    {r : ℝ} (hr : r<1) :
    ∃ s : ℝ, 0<s ∧ s<1 ∧ ∀ z : ball (0:ℂ) 1, s<‖(z:ℂ)‖ → r<‖(F z:ℂ)‖ := by
  let K : Set (ball (0:ℂ) 1) := {z | ‖(z:ℂ)‖≤r}
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : ((↑) : ball (0:ℂ) 1 → ℂ) '' K=closedBall (0:ℂ) r := by
      ext z
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact mem_closedBall_zero_iff.mpr hz
      · intro hz
        have hzD : z∈ball (0:ℂ) 1 :=
          mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
        exact ⟨⟨z,hzD⟩,mem_closedBall_zero_iff.mp hz,rfl⟩
    rw [heq]
    exact isCompact_closedBall _ _
  let P : Set ℂ := ((↑) : ball (0:ℂ) 1 → ℂ) '' (F ⁻¹' K)
  have hP : IsCompact P := (hF.isCompact_preimage hK).image continuous_subtype_val
  have hPD : P⊆ball (0:ℂ) 1 := by
    rintro z ⟨w,hw,rfl⟩
    exact w.property
  by_cases hne : P.Nonempty
  · obtain ⟨w,hw,hwmax⟩ := hP.exists_isMaxOn hne continuous_norm.continuousOn
    have hwn : ‖w‖<1 := mem_ball_zero_iff.mp (hPD hw)
    refine ⟨(‖w‖+1)/2,by positivity,by linarith,?_⟩
    intro z hz
    by_contra H
    have hzK : F z∈K := le_of_not_gt H
    have hzP : (z:ℂ)∈P := ⟨z,hzK,rfl⟩
    have Hmax : ‖(z:ℂ)‖≤‖w‖ := hwmax hzP
    linarith
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro z hz
    by_contra H
    exact hne ⟨z,⟨z,le_of_not_gt H,rfl⟩⟩

/-- Fibres of a proper holomorphic disc map are finite. Nonconstancy is
forced by properness, so it is not imposed as an additional hypothesis. -/
theorem finite_fibre_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1)))
    {b : ℂ} (hb : ‖b‖<1) : {z∈ball (0:ℂ) 1 | f z=b}.Finite := by
  let F : ball (0:ℂ) 1 → ball (0:ℂ) 1 := fun z => ⟨f z,hmap z.property⟩
  obtain ⟨s,hs0,hs1,hlarge⟩ := exists_boundary_collar_of_isProperMap_disc F hproper hb
  let z₀ : ℂ := (((s+1)/2:ℝ):ℂ)
  have hn₀ : ‖z₀‖=(s+1)/2 := by
    simp only [z₀,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : (s+1)/2>0)]
  have hz₀ : z₀∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,hn₀]
    linarith
  have hfb : f z₀≠b := by
    have H := hlarge ⟨z₀,hz₀⟩ (by rw [hn₀]; linarith)
    change ‖b‖<‖f z₀‖ at H
    intro heq
    rw [heq] at H
    exact H.false
  have hcod : ∀ᶠ z in codiscreteWithin (ball (0:ℂ) 1), f z-b≠0 := by
    rcases (hf.sub analyticOnNhd_const).eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_ball (0:ℂ) 1).isPreconnected with H|H
    · exact False.elim (hfb (sub_eq_zero.mp (H hz₀)))
    · exact H
  have hKD : closedBall (0:ℂ) s⊆ball (0:ℂ) 1 := closedBall_subset_ball hs1
  have hcodK : {z : ℂ | f z-b≠0}∈codiscreteWithin (closedBall (0:ℂ) s) :=
    codiscreteWithin_mono hKD hcod
  have hfinite := (isCompact_closedBall (0:ℂ) s).finite_sdiff_of_mem_codiscreteWithin hcodK
  apply hfinite.subset
  intro z hz
  have hzs : ‖z‖≤s := by
    by_contra H
    have H' := hlarge ⟨z,hz.1⟩ (lt_of_not_ge H)
    change ‖b‖<‖f z‖ at H'
    rw [hz.2] at H'
    exact H'.false
  exact ⟨mem_closedBall_zero_iff.mpr hzs,fun H => H (sub_eq_zero.mpr hz.2)⟩

end FunctionTheory

