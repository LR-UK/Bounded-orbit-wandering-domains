import BoundedWanderingDomains.NormalFamilies
import FunctionTheory.Conformal.InverseLimits

/-!
# Persistence of inverse branches in covering limits

Bounded holomorphic inverse branches have subsequential limits. A prescribed
interior value, even at moving base points, prevents escape to the unit circle.
The inverse identity therefore passes to the limit. This establishes a local
step; the construction of an exhausting system of covering maps remains separate.
-/

open Set Filter Metric Function
open scoped Topology

namespace AreaDeficit

theorem exists_inverseBranch_limit
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {a : ℕ → ℂ} {z w : ℂ}
    (hz : z ∈ U) (hw : w ∈ ball (0 : ℂ) 1)
    (hG : ∀ n, DifferentiableOn ℂ (G n) U)
    (hmap : ∀ n, MapsTo (G n) U (ball 0 1))
    (hf : ContinuousOn f (ball 0 1))
    (hFconv : TendstoLocallyUniformlyOn F f atTop (ball 0 1))
    (hinv : ∀ n, LeftInvOn (F n) (G n) U)
    (ha : Tendsto a atTop (𝓝 z))
    (hbase : Tendsto (fun n => G n (a n)) atTop (𝓝 w)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ MapsTo g U (ball 0 1) ∧
      LeftInvOn f g U ∧ g z = w ∧ InjOn g U := by
  obtain ⟨σ, g, hσ, hconv, hg⟩ := bounded_holomorphic_subsequence hU hG
    (fun n y hy => (mem_ball_zero_iff.mp (hmap n hy)).le)
  have ha' : Tendsto (fun n => a (σ n)) atTop (𝓝[U] z) := by
    rw [hU.nhdsWithin_eq hz]
    exact ha.comp hσ.tendsto_atTop
  have hgw : g z = w := tendsto_nhds_unique
    (hconv.tendsto_comp (hg.continuousOn z hz) hz ha')
    (hbase.comp hσ.tendsto_atTop)
  have hnorm : ∀ y ∈ U, ‖g y‖ ≤ 1 := by
    intro y hy
    exact le_of_tendsto (hconv.tendsto_at hy).norm
      (.of_forall fun n => (mem_ball_zero_iff.mp (hmap (σ n) hy)).le)
  have hgmap : MapsTo g U (ball 0 1) := by
    intro y hy
    rw [mem_ball_zero_iff]
    by_contra! hbad
    have hmax : IsMaxOn (fun t => ‖g t‖) U y :=
      fun t ht => (hnorm t ht).trans hbad
    have heq : g z = g y :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU hg hy hmax hz
    have hw' := mem_ball_zero_iff.mp hw
    rw [← heq, hgw] at hbad
    exact (not_le_of_gt hw') hbad
  have hinv' : LeftInvOn f g U :=
    FunctionTheory.leftInvOn_of_locallyUniform_limits isOpen_ball hgmap hf hconv
      (FunctionTheory.locallyUniformOn_reindex hFconv hσ.tendsto_atTop)
      (.of_forall fun n => hinv (σ n))
  exact ⟨g, hg, hgmap, hinv', hgw, hinv'.injOn⟩

end AreaDeficit
