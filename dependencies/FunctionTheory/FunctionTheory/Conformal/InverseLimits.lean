import FunctionTheory.Conformal.KernelImage
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Inverse identities in holomorphic limits -/

open Set Filter Metric Function
open scoped Topology

namespace FunctionTheory

/-- A limit of disk-valued holomorphic maps fixing a point at zero still takes
values in the open disk. The fixed point excludes a constant boundary value. -/
theorem mapsTo_unitBall_of_holomorphic_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (hconv : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, MapsTo (F n) U (ball 0 1))
    (hzero : ∀ᶠ n in l, F n z₀ = 0) : MapsTo f U (ball 0 1) := by
  have hnorm : ∀ z ∈ U, ‖f z‖ ≤ 1 := by
    intro z hz
    apply le_of_tendsto (hconv.tendsto_at hz).norm
    exact hF.mono fun n hn => (mem_ball_zero_iff.mp (hn hz)).le
  have hfzero : f z₀ = 0 :=
    tendsto_nhds_unique (hconv.tendsto_at hz₀)
      (tendsto_const_nhds.congr' (hzero.mono fun _ hn => hn.symm))
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra! hbad
  have hmax : IsMaxOn (fun w => ‖f w‖) U z := fun w hw => (hnorm w hw).trans hbad
  have heq : f z₀ = f z :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hf hz hmax hz₀
  norm_num only [← heq, hfzero, norm_zero] at hbad

theorem leftInvOn_of_locallyUniform_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F G : ι → ℂ → ℂ} {f g : ℂ → ℂ} {U V : Set ℂ}
    (hV : IsOpen V) (hfV : MapsTo f U V) (hg : ContinuousOn g V)
    (hF : TendstoLocallyUniformlyOn F f l U)
    (hG : TendstoLocallyUniformlyOn G g l V)
    (hinv : ∀ᶠ n in l, LeftInvOn (G n) (F n) U) : LeftInvOn g f U := by
  intro z hz
  have ht : Tendsto (fun n => F n z) l (𝓝[V] (f z)) := by
    rw [hV.nhdsWithin_eq (hfV hz)]
    exact hF.tendsto_at hz
  have hcomp := hG.tendsto_comp (hg (f z) (hfV hz)) (hfV hz) ht
  exact tendsto_nhds_unique hcomp
    (tendsto_const_nhds.congr' (hinv.mono fun n hn => (hn hz).symm))

/-- Both inverse identities pass to the limit once the limiting maps take
values in the correct open domains. The approximating domains may be larger. -/
theorem invOn_of_locallyUniform_limits
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F G : ι → ℂ → ℂ} {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hfV : MapsTo f U V) (hgU : MapsTo g V U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hF : TendstoLocallyUniformlyOn F f l U)
    (hG : TendstoLocallyUniformlyOn G g l V)
    (hleft : ∀ᶠ n in l, LeftInvOn (G n) (F n) U)
    (hright : ∀ᶠ n in l, LeftInvOn (F n) (G n) V) : InvOn g f U V :=
  ⟨leftInvOn_of_locallyUniform_limits hV hfV hg hF hG hleft,
    leftInvOn_of_locallyUniform_limits hU hgU hf hG hF hright⟩

end FunctionTheory
