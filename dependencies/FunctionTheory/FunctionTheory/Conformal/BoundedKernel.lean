import FunctionTheory.Conformal.KernelSubsequence
import FunctionTheory.Conformal.RiemannInverseBounds

/-! # Kernel convergence for bounded decreasing domains

The kernel is identified by two explicit conditions: it lies in every source
domain, and it contains the base-point component of the interior of the
intersection of their closures. These conditions exclude disappearing slits
and retain the correct component when a limiting neck pinches off.
-/

open Set Filter Metric Function Bornology
open scoped Topology ComplexOrder

namespace FunctionTheory

theorem exists_normalized_riemann_kernel_subsequence_of_locallyBounded
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {z₀ : ℂ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U) (hbound : TauCeti.IsLocallyBoundedOn
      (fun n => invFunOn (F n) (U n)) (ball 0 1))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hz₀ : z₀ ∈ V)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    ∃ (σ : ℕ → ℕ) (f g : ℂ → ℂ), StrictMono σ ∧
      TauCeti.IsNormalizedRiemannMapOn f V z₀ ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn g (ball 0 1) V ∧
      InvOn g f V (ball 0 1) ∧ g 0 = z₀ ∧
      TendstoLocallyUniformlyOn (fun n => F (σ n)) f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F (σ n)) (U (σ n))) g atTop
        (ball 0 1) := by
  let G : ℕ → ℂ → ℂ := fun n => invFunOn (F n) (U n)
  have hGbij (n : ℕ) : BijOn (G n) (ball 0 1) (U n) :=
    BijOn.symm (hF n).bijOn.invOn_invFunOn.symm (hF n).bijOn
  have hGhol (n : ℕ) : DifferentiableOn ℂ (G n) (ball 0 1) := by
    have h := DifferentiableOn.invFunOn (hF n).differentiableOn (hUo n) (hF n).injOn
    rwa [(hF n).image_eq] at h
  have hGzero (n : ℕ) : G n 0 = z₀ := by
    simpa only [G, (hF n).map_base] using
      (hF n).injOn.leftInvOn_invFunOn (hF n).base_mem
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hVo.mem_nhds hz₀)
  have hderiv (n : ℕ) : r ≤ ‖deriv (G n) 0‖ :=
    normalized_inverse_derivative_lower_bound (hUo n) (hF n) hr (hrV.trans (hVU n))
  have hleft (n : ℕ) : LeftInvOn (G n) (F n) V :=
    fun z hz => (hF n).injOn.leftInvOn_invFunOn (hVU n hz)
  have hright (n : ℕ) : LeftInvOn (F n) (G n) (ball 0 1) :=
    (hF n).bijOn.surjOn.rightInvOn_invFunOn
  have hmem (k : ℕ) : ∀ᶠ n in atTop, MapsTo (G n) (ball 0 1) (closure (U k)) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    intro w hw
    exact subset_closure (hdec hn ((hGbij n).mapsTo hw))
  obtain ⟨σ, f, g, hσ, hf, hg, hfbij, hgbij, hinv, hfzero, hgzero, hFc, hGc⟩ :=
    exists_biholomorphic_kernel_subsequence_of_locallyBounded hVo hVc hz₀ hr
      (fun n => (hF n).differentiableOn.mono (hVU n)) hGhol
      (fun n z hz => (hF n).mapsTo (hVU n hz)) hbound
      (fun n => (hF n).map_base) hGzero hderiv hleft hright
      (fun _ => isClosed_closure) hmem hkernel
  have hdconv : Tendsto (fun n => deriv (F (σ n)) z₀) atTop (𝓝 (deriv f z₀)) :=
    (hFc.deriv (.of_forall fun n => (hF (σ n)).differentiableOn.mono (hVU (σ n)))
      hVo).tendsto_at hz₀
  have hre : 0 ≤ (deriv f z₀).re := ge_of_tendsto
    ((Complex.continuous_re.tendsto _).comp hdconv)
    (.of_forall fun n => (Complex.pos_iff.mp (hF (σ n)).deriv_pos).1.le)
  have him : (deriv f z₀).im = 0 := tendsto_nhds_unique
    ((Complex.continuous_im.tendsto _).comp hdconv)
    (tendsto_const_nhds.congr' (.of_forall fun n =>
      (Complex.pos_iff.mp (hF (σ n)).deriv_pos).2))
  have hdne : deriv f z₀ ≠ 0 := TauCeti.deriv_ne_zero_of_injOn hf hVo hfbij.injOn hz₀
  have hpos : 0 < deriv f z₀ := by
    apply Complex.pos_iff.mpr
    refine ⟨lt_of_le_of_ne hre ?_, him.symm⟩
    intro heq
    exact hdne (Complex.ext heq.symm him)
  exact ⟨σ, f, g, hσ, ⟨hz₀, hf, hfbij, hfzero, hpos⟩, hg, hgbij,
    hinv, hgzero, hFc, hGc⟩

theorem exists_normalized_riemann_kernel_subsequence
    {U : ℕ → Set ℂ} {V : Set ℂ} {F : ℕ → ℂ → ℂ} {z₀ : ℂ}
    (hUo : ∀ n, IsOpen (U n)) (hdec : Antitone U) (hbound : IsBounded (U 0))
    (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (U n) z₀)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hz₀ : z₀ ∈ V)
    (hVU : ∀ n, V ⊆ U n)
    (hkernel : connectedComponentIn (interior (⋂ n, closure (U n))) z₀ ⊆ V) :
    ∃ (σ : ℕ → ℕ) (f g : ℂ → ℂ), StrictMono σ ∧
      TauCeti.IsNormalizedRiemannMapOn f V z₀ ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn g (ball 0 1) V ∧
      InvOn g f V (ball 0 1) ∧ g 0 = z₀ ∧
      TendstoLocallyUniformlyOn (fun n => F (σ n)) f atTop V ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F (σ n)) (U (σ n))) g atTop
        (ball 0 1) := by
  obtain ⟨R, hR⟩ := hbound.exists_norm_le
  have hGb : TauCeti.IsLocallyBoundedOn
      (fun n => invFunOn (F n) (U n)) (ball 0 1) := by
    apply TauCeti.isLocallyBoundedOn_of_forall_norm_le (C := R)
    intro n w hw
    have hbij := BijOn.symm (hF n).bijOn.invOn_invFunOn.symm (hF n).bijOn
    exact hR _ (hdec (Nat.zero_le n) (hbij.mapsTo hw))
  exact exists_normalized_riemann_kernel_subsequence_of_locallyBounded
    hUo hdec hGb hF hVo hVc hz₀ hVU hkernel

end FunctionTheory
