import FunctionTheory.Conformal.StripCoordinates
import Mathlib.Topology.UniformSpace.UniformApproximation

open Set Filter
open scoped Topology Uniformity

namespace FunctionTheory

/-- Continuous postcomposition preserves local uniform convergence when
the limit is continuous and all images remain in the continuity domain.
Uniform continuity on the entire target domain is unnecessary. -/
theorem locallyUniformOn_continuous_postcomposition
    {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {S : Set α} {D : Set β} {F : ι → α → β} {f : α → β} {g : β → γ}
    (hconv : TendstoLocallyUniformlyOn F f l S) (hf : ContinuousOn f S)
    (hg : ContinuousOn g D) (hF : ∀ n, MapsTo (F n) S D) (hfm : MapsTo f S D) :
    TendstoLocallyUniformlyOn (fun n x => g (F n x)) (fun x => g (f x)) l S := by
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro x hx
  have hconv' : TendstoLocallyUniformlyOn (fun p : ι × α => F p.1) f (l ×ˢ 𝓝[S] x) S := by
    intro u hu y hy
    obtain ⟨T, hT, he⟩ := hconv u hu y hy
    exact ⟨T, hT, tendsto_fst.eventually he⟩
  have htF := hconv'.tendsto_comp (hf x hx) hx tendsto_snd
  have hmem : ∀ᶠ p : ι × α in l ×ˢ 𝓝[S] x, p.2 ∈ S :=
    tendsto_snd.eventually self_mem_nhdsWithin
  have htFD : Tendsto (fun p : ι × α => F p.1 p.2) (l ×ˢ 𝓝[S] x) (𝓝[D] (f x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htF, hmem.mono (fun p hp => hF p.1 hp)⟩
  have htfD : Tendsto (fun p : ι × α => f p.2) (l ×ˢ 𝓝[S] x) (𝓝[D] (f x)) :=
    ((hf x hx).tendsto_nhdsWithin hfm).comp tendsto_snd
  have hgt : Tendsto g (𝓝[D] (f x)) (𝓝 (g (f x))) := hg (f x) (hfm hx)
  exact ((hgt.comp htfD).prodMk_nhds (hgt.comp htFD)).mono_right (nhds_le_uniformity _)

theorem locallyUniform_discToHorizontalStrip
    {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V) (hf : ContinuousOn f V)
    (hF : ∀ n, MapsTo (F n) V (Metric.ball 0 1)) (hfm : MapsTo f V (Metric.ball 0 1)) :
    TendstoLocallyUniformlyOn (fun n z => discToHorizontalStrip (F n z))
      (fun z => discToHorizontalStrip (f z)) atTop V :=
  locallyUniformOn_continuous_postcomposition hconv hf
    differentiableOn_discToHorizontalStrip.continuousOn hF hfm

end FunctionTheory
