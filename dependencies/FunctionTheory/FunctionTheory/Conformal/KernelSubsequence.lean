import FunctionTheory.Conformal.InverseLimits
import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import Mathlib.Topology.Connected.LocallyConnected

/-! # A convergent subsequence for locally bounded kernel systems

The direct and inverse maps are given on their actual open sets. Montel
selection provides simultaneous limits. The derivative bound prevents the
inverse limit from collapsing, while the closed constraints identify its image
with the kernel component. The inverse identities then prove surjectivity.
-/

open Set Filter Metric Function
open scoped Topology

namespace FunctionTheory

theorem exists_biholomorphic_kernel_subsequence_of_locallyBounded
    {κ : Type*} {F G : ℕ → ℂ → ℂ} {U : Set ℂ} {C : κ → Set ℂ}
    {z₀ : ℂ} {r : ℝ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hr : 0 < r)
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hGhol : ∀ n, DifferentiableOn ℂ (G n) (ball 0 1))
    (hFmap : ∀ n, MapsTo (F n) U (ball 0 1))
    (hGbound : TauCeti.IsLocallyBoundedOn G (ball 0 1))
    (hFzero : ∀ n, F n z₀ = 0) (hGzero : ∀ n, G n 0 = z₀)
    (hderiv : ∀ n, r ≤ ‖deriv (G n) 0‖)
    (hleft : ∀ n, LeftInvOn (G n) (F n) U)
    (hright : ∀ n, LeftInvOn (F n) (G n) (ball 0 1))
    (hC : ∀ k, IsClosed (C k))
    (hmem : ∀ k, ∀ᶠ n in atTop, MapsTo (G n) (ball 0 1) (C k))
    (hkernel : connectedComponentIn (interior (⋂ k, C k)) z₀ ⊆ U) :
    ∃ (σ : ℕ → ℕ) (f g : ℂ → ℂ), StrictMono σ ∧
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      InvOn g f U (ball 0 1) ∧ f z₀ = 0 ∧ g 0 = z₀ ∧
      TendstoLocallyUniformlyOn (fun n => F (σ n)) f atTop U ∧
      TendstoLocallyUniformlyOn (fun n => G (σ n)) g atTop (ball 0 1) := by
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hDb : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball _ _).isPreconnected
  obtain ⟨σ, g, hσ, hg, hGconv⟩ := TauCeti.montel isOpen_ball hGhol
    hGbound
  have hGconvDeriv : ∀ᶠ n in atTop, r ≤ ‖deriv (G (σ n)) 0‖ :=
    .of_forall fun n => hderiv (σ n)
  have hgimage : g '' ball 0 1 ⊆ interior (⋂ k, C k) :=
    image_subset_kernel_of_derivative_lower_bound isOpen_ball hDb h0 hr
      (.of_forall fun n => hGhol (σ n)) hGconv hGconvDeriv hC
      (fun k => hσ.tendsto_atTop.eventually (hmem k))
  have hgzero : g 0 = z₀ := tendsto_nhds_unique (hGconv.tendsto_at h0)
    (tendsto_const_nhds.congr' (.of_forall fun n => (hGzero (σ n)).symm))
  have hgU : MapsTo g (ball 0 1) U := by
    apply mapsTo_iff_image_subset.mpr
    apply Subset.trans _ hkernel
    apply (hDb.image g hg.continuousOn).subset_connectedComponentIn _ hgimage
    exact ⟨0, h0, hgzero⟩
  have hFbound : TauCeti.IsLocallyBoundedOn (fun n => F (σ n)) U :=
    TauCeti.isLocallyBoundedOn_of_forall_norm_le fun n z hz =>
      (mem_ball_zero_iff.mp (hFmap (σ n) hz)).le
  obtain ⟨τ, f, hτ, hf, hFconv⟩ := TauCeti.montel hUo
    (fun n => hFhol (σ n)) hFbound
  have hGconv' : TendstoLocallyUniformlyOn (fun n => G (σ (τ n))) g atTop (ball 0 1) :=
    locallyUniformOn_reindex hGconv hτ.tendsto_atTop
  have hfD : MapsTo f U (ball 0 1) := mapsTo_unitBall_of_holomorphic_limit
    hUo hUc hz₀ hf hFconv (.of_forall fun n => hFmap (σ (τ n)))
    (.of_forall fun n => hFzero (σ (τ n)))
  have hinv : InvOn g f U (ball 0 1) := invOn_of_locallyUniform_limits
    hUo isOpen_ball hfD hgU hf.continuousOn hg.continuousOn hFconv hGconv'
    (.of_forall fun n => hleft (σ (τ n)))
    (.of_forall fun n => hright (σ (τ n)))
  have hfbij : BijOn f U (ball 0 1) := by
    refine ⟨hfD, hinv.1.injOn, ?_⟩
    intro w hw
    exact ⟨g w, hgU hw, hinv.2 hw⟩
  have hgbij : BijOn g (ball 0 1) U := by
    refine ⟨hgU, hinv.2.injOn, ?_⟩
    intro z hz
    exact ⟨f z, hfD hz, hinv.1 hz⟩
  have hfzero : f z₀ = 0 := tendsto_nhds_unique (hFconv.tendsto_at hz₀)
    (tendsto_const_nhds.congr' (.of_forall fun n => (hFzero (σ (τ n))).symm))
  exact ⟨σ ∘ τ, f, g, hσ.comp hτ, hf, hg, hfbij, hgbij, hinv,
    hfzero, hgzero, hFconv, hGconv'⟩

theorem exists_biholomorphic_kernel_subsequence
    {κ : Type*} {F G : ℕ → ℂ → ℂ} {U : Set ℂ} {C : κ → Set ℂ}
    {z₀ : ℂ} {r R : ℝ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hr : 0 < r)
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hGhol : ∀ n, DifferentiableOn ℂ (G n) (ball 0 1))
    (hFmap : ∀ n, MapsTo (F n) U (ball 0 1))
    (hGbound : ∀ n, ∀ w ∈ ball 0 1, ‖G n w‖ ≤ R)
    (hFzero : ∀ n, F n z₀ = 0) (hGzero : ∀ n, G n 0 = z₀)
    (hderiv : ∀ n, r ≤ ‖deriv (G n) 0‖)
    (hleft : ∀ n, LeftInvOn (G n) (F n) U)
    (hright : ∀ n, LeftInvOn (F n) (G n) (ball 0 1))
    (hC : ∀ k, IsClosed (C k))
    (hmem : ∀ k, ∀ᶠ n in atTop, MapsTo (G n) (ball 0 1) (C k))
    (hkernel : connectedComponentIn (interior (⋂ k, C k)) z₀ ⊆ U) :
    ∃ (σ : ℕ → ℕ) (f g : ℂ → ℂ), StrictMono σ ∧
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      InvOn g f U (ball 0 1) ∧ f z₀ = 0 ∧ g 0 = z₀ ∧
      TendstoLocallyUniformlyOn (fun n => F (σ n)) f atTop U ∧
      TendstoLocallyUniformlyOn (fun n => G (σ n)) g atTop (ball 0 1) := by
  exact exists_biholomorphic_kernel_subsequence_of_locallyBounded
    hUo hUc hz₀ hr hFhol hGhol hFmap
    (TauCeti.isLocallyBoundedOn_of_forall_norm_le hGbound)
    hFzero hGzero hderiv hleft hright hC hmem hkernel

end FunctionTheory
