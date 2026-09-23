import FunctionTheory.Conformal.BoundedKernel
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Convergence of normalized Riemann maps to a bounded kernel

Every subsequence has a further subsequence with a normalized conformal limit.
Uniqueness of normalization identifies all these limits, yielding convergence
of both the direct and inverse maps along the whole sequence.
-/

open Set Filter Metric Function Bornology
open scoped Topology

namespace FunctionTheory

theorem locallyUniformOn_of_subsequence_limits
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ n, ContinuousOn (F n) U) (hf : ContinuousOn f U)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, TendstoLocallyUniformlyOn (fun n => F (ns (ms n))) f atTop U) :
    TendstoLocallyUniformlyOn F f atTop U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let F' : ℕ → C(U, ℂ) := fun n => ⟨U.domRestrict (F n), (hF n).domRestrict⟩
  let f' : C(U, ℂ) := ⟨U.domRestrict f, hf.domRestrict⟩
  have hconv : Tendsto F' atTop (𝓝 f') := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms⟩ := hsub ns hns
    refine ⟨ms, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr ?_⟩
    exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hms
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv)

theorem normalized_riemannMaps_tendsto_on_kernel_of_locallyBounded
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U) (hbound : TauCeti.IsLocallyBoundedOn
      (fun n => invFunOn (F n) (U n)) (ball 0 1))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hf : TauCeti.IsNormalizedRiemannMapOn f V z₀)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    TendstoLocallyUniformlyOn F f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (U n)) (invFunOn f V) atTop
        (ball 0 1) := by
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoLocallyUniformlyOn (fun n => F (ns (ms n))) f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F (ns (ms n))) (U (ns (ms n))))
        (invFunOn f V) atTop (ball 0 1) := by
    intro ns hns
    obtain ⟨ρ, hρ, hnsρ⟩ := strictMono_subseq_of_tendsto_atTop hns
    have hclos : Antitone (fun n => closure (U n)) := fun n m hnm => closure_mono (hdec hnm)
    have hinter : (⋂ n, closure (U ((ns ∘ ρ) n))) = ⋂ n, closure (U n) :=
      hclos.iInter_comp_tendsto_atTop hnsρ.tendsto_atTop
    obtain ⟨σ, f₁, g₁, hσ, hf₁, hg₁, hgbij, hinv, -, hFc, hGc⟩ :=
      exists_normalized_riemann_kernel_subsequence_of_locallyBounded
        (U := fun n => U ((ns ∘ ρ) n)) (F := fun n => F ((ns ∘ ρ) n))
        (fun n => hUo _) (hdec.comp_monotone hnsρ.monotone)
        (hbound.comp (ns ∘ ρ)) (fun n => hF _)
        hVo hVc hf.base_mem (fun n => hVU _) (by simpa only [hinter] using hkernel)
    have hfeq : EqOn f₁ f V := hf₁.eqOn hf hVo
    have hgeq : EqOn g₁ (invFunOn f V) (ball 0 1) := by
      intro w hw
      have hgV := hgbij.mapsTo hw
      have hfg : f (g₁ w) = w := (hfeq hgV).symm.trans (hinv.2 hw)
      calc
        g₁ w = invFunOn f V (f (g₁ w)) := (hf.injOn.leftInvOn_invFunOn hgV).symm
        _ = invFunOn f V w := congrArg (invFunOn f V) hfg
    exact ⟨ρ ∘ σ, hFc.congr_right hfeq, hGc.congr_right hgeq⟩
  have hGhol : DifferentiableOn ℂ (invFunOn f V) (ball 0 1) := by
    have h := DifferentiableOn.invFunOn hf.differentiableOn hVo hf.injOn
    rwa [hf.image_eq] at h
  have hGn (n : ℕ) : DifferentiableOn ℂ (invFunOn (F n) (U n)) (ball 0 1) := by
    have h := DifferentiableOn.invFunOn (hF n).differentiableOn (hUo n) (hF n).injOn
    rwa [(hF n).image_eq] at h
  constructor
  · apply locallyUniformOn_of_subsequence_limits hVo
      (fun n => (hF n).differentiableOn.continuousOn.mono (hVU n)) hf.differentiableOn.continuousOn
    intro ns hns
    obtain ⟨ms, hms, -⟩ := hsub ns hns
    exact ⟨ms, hms⟩
  · apply locallyUniformOn_of_subsequence_limits isOpen_ball
      (fun n => (hGn n).continuousOn) hGhol.continuousOn
    intro ns hns
    obtain ⟨ms, -, hms⟩ := hsub ns hns
    exact ⟨ms, hms⟩

theorem normalized_riemannMaps_tendsto_on_bounded_kernel
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U) (hbound : IsBounded (U 0))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hf : TauCeti.IsNormalizedRiemannMapOn f V z₀)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    TendstoLocallyUniformlyOn F f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (U n)) (invFunOn f V) atTop
        (ball 0 1) := by
  obtain ⟨R, hR⟩ := hbound.exists_norm_le
  have hGb : TauCeti.IsLocallyBoundedOn
      (fun n => invFunOn (F n) (U n)) (ball 0 1) := by
    apply TauCeti.isLocallyBoundedOn_of_forall_norm_le (C := R)
    intro n w hw
    have hbij := BijOn.symm (hF n).bijOn.invOn_invFunOn.symm (hF n).bijOn
    exact hR _ (hdec (Nat.zero_le n) (hbij.mapsTo hw))
  exact normalized_riemannMaps_tendsto_on_kernel_of_locallyBounded
    hUo hdec hGb hF hVo hVc hf hVU hkernel

theorem exists_normalized_riemannMap_of_bounded_kernel
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {z₀ : ℂ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U) (hbound : IsBounded (U 0))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hz₀ : z₀ ∈ V)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    ∃ f : ℂ → ℂ, TauCeti.IsNormalizedRiemannMapOn f V z₀ ∧
      TendstoLocallyUniformlyOn F f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (U n)) (invFunOn f V) atTop
        (ball 0 1) := by
  obtain ⟨σ, f, g, hσ, hf, rest⟩ := exists_normalized_riemann_kernel_subsequence
    hUo hdec hbound hF hVo hVc hz₀ hVU hkernel
  exact ⟨f, hf, normalized_riemannMaps_tendsto_on_bounded_kernel
    hUo hdec hbound hF hVo hVc hf hVU hkernel⟩

end FunctionTheory
