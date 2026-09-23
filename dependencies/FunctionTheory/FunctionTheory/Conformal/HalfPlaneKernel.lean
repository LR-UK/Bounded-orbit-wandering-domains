import FunctionTheory.Conformal.KernelConvergence
import FunctionTheory.Conformal.ImaginaryBounds

/-! # Kernel convergence for domains in a horizontal halfplane

A common lower bound on imaginary parts supplies local bounds for the inverse
maps. The source domains may be unbounded, as in horizontal halfstrips.
-/

open Set Filter Metric Function
open scoped Topology

namespace FunctionTheory

theorem locallyBoundedOn_inverse_riemannMaps_of_im_lower_bound
    {ι : Type*} {U : ι → Set ℂ} {F : ι → ℂ → ℂ} {z₀ : ℂ} {M : ℝ}
    (hUo : ∀ n, IsOpen (U n))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hbound : ∀ n, ∀ z ∈ U n, -M ≤ z.im) :
    TauCeti.IsLocallyBoundedOn (fun n => invFunOn (F n) (U n)) (ball 0 1) := by
  apply locallyBoundedOn_of_im_lower_bound (z₀ := z₀) (M := M)
  · intro n
    have h := DifferentiableOn.invFunOn (hF n).differentiableOn (hUo n) (hF n).injOn
    rwa [(hF n).image_eq] at h
  · intro n
    simpa only [(hF n).map_base] using
      (hF n).injOn.leftInvOn_invFunOn (hF n).base_mem
  · intro n w hw
    have hbij := BijOn.symm (hF n).bijOn.invOn_invFunOn.symm (hF n).bijOn
    exact hbound n _ (hbij.mapsTo hw)

theorem normalized_riemannMaps_tendsto_on_halfPlane_kernel
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {M : ℝ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U)
    (hbound : ∀ z ∈ U 0, -M ≤ z.im)
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hf : TauCeti.IsNormalizedRiemannMapOn f V z₀)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    TendstoLocallyUniformlyOn F f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (U n)) (invFunOn f V) atTop
        (ball 0 1) := by
  apply normalized_riemannMaps_tendsto_on_kernel_of_locallyBounded hUo hdec
    (locallyBoundedOn_inverse_riemannMaps_of_im_lower_bound hUo hF
      (fun n z hz => hbound z (hdec (Nat.zero_le n) hz))) hF hVo hVc hf hVU hkernel

theorem exists_normalized_riemannMap_of_halfPlane_kernel
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {z₀ : ℂ} {M : ℝ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U)
    (hbound : ∀ z ∈ U 0, -M ≤ z.im)
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hz₀ : z₀ ∈ V)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    ∃ f : ℂ → ℂ, TauCeti.IsNormalizedRiemannMapOn f V z₀ ∧
      TendstoLocallyUniformlyOn F f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (U n)) (invFunOn f V) atTop
        (ball 0 1) := by
  have hGb := locallyBoundedOn_inverse_riemannMaps_of_im_lower_bound hUo hF
    (fun n z hz => hbound z (hdec (Nat.zero_le n) hz))
  obtain ⟨σ, f, g, hσ, hf, rest⟩ :=
    exists_normalized_riemann_kernel_subsequence_of_locallyBounded
      hUo hdec hGb hF hVo hVc hz₀ hVU hkernel
  exact ⟨f, hf, normalized_riemannMaps_tendsto_on_halfPlane_kernel
    hUo hdec hbound hF hVo hVc hf hVU hkernel⟩

end FunctionTheory
