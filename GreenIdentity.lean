import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

noncomputable def pd (f : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun x => fderiv ℝ f x v

theorem pd_contDiffAt {f : ℂ → ℝ} {x : ℂ} {n : ℕ∞ω}
    (hf : ContDiffAt ℝ (n + 1) f x) (v : ℂ) : ContDiffAt ℝ n (pd f v) x := by
  exact hf.fderiv_right_succ.clm_apply contDiffAt_const

theorem pd_contDiff {f : ℂ → ℝ} {n : ℕ∞ω}
    (hf : ContDiff ℝ (n + 1) f) (v : ℂ) : ContDiff ℝ n (pd f v) :=
  contDiff_iff_contDiffAt.mpr (fun _ => pd_contDiffAt hf.contDiffAt v)

theorem pd_tsupport_subset (f : ℂ → ℝ) (v : ℂ) : tsupport (pd f v) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ v

theorem pd_hasCompactSupport {f : ℂ → ℝ} (hf : HasCompactSupport f) (v : ℂ) :
    HasCompactSupport (pd f v) := hf.fderiv_apply ℝ v

theorem continuous_mul_of_local {f g : ℂ → ℝ} (hf : Continuous f)
    (hg : ∀ x ∈ tsupport f, ContinuousAt g x) : Continuous (fun x => f x * g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.mul (hg x hx)
  · apply (show ContinuousAt (fun _ : ℂ => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem integrable_mul_of_local {f g : ℂ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hg : ∀ x ∈ tsupport f, ContinuousAt g x) :
    Integrable (fun x => f x * g x) :=
  (continuous_mul_of_local hf hg).integrable_of_hasCompactSupport hc.mul_right

theorem pd2_eq {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    pd (pd f v) v x = iteratedFDeriv ℝ 2 f x ![v, v] := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change (fderiv ℝ (fun y => fderiv ℝ f y v) x) v = _
  rw [fderiv_clm_apply hfd (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]

theorem laplacian_eq_pd2 {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = pd (pd f 1) 1 x + pd (pd f Complex.I) Complex.I x := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane, pd2_eq hf, pd2_eq hf]

/-- Green's identity in one coordinate, with only local C² assumptions on `f`. -/
theorem green_pd {f chi : ℂ → ℝ} (v : ℂ)
    (hf : ∀ x ∈ tsupport chi, ContDiffAt ℝ 2 f x)
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi) :
    (∫ x, chi x * pd (pd f v) v x) = ∫ x, f x * pd (pd chi v) v x := by
  have hdc : ContDiff ℝ 1 (pd chi v) := pd_contDiff hchi v
  have hddc : ContDiff ℝ 0 (pd (pd chi v) v) := pd_contDiff hdc v
  have hdcC := pd_hasCompactSupport hc v
  have hddcC := pd_hasCompactSupport hdcC v
  have hdf (x) (hx : x ∈ tsupport chi) : ContDiffAt ℝ 1 (pd f v) x :=
    pd_contDiffAt (hf x hx) v
  have hddf (x) (hx : x ∈ tsupport chi) : ContinuousAt (pd (pd f v) v) x :=
    (pd_contDiffAt (n := 0) (hdf x hx) v).continuousAt
  have i1 : Integrable (fun x => chi x * pd (pd f v) v x) :=
    integrable_mul_of_local hchi.continuous hc hddf
  have i2 : Integrable (fun x => pd chi v x * pd f v x) :=
    integrable_mul_of_local hdc.continuous hdcC
      (fun x hx => (hdf x (pd_tsupport_subset chi v hx)).continuousAt)
  have i3 : Integrable (fun x => chi x * pd f v x) :=
    integrable_mul_of_local hchi.continuous hc (fun x hx => (hdf x hx).continuousAt)
  have i4 : Integrable (fun x => pd (pd chi v) v x * f x) :=
    integrable_mul_of_local hddc.continuous hddcC (fun x hx =>
      (hf x (pd_tsupport_subset chi v (pd_tsupport_subset (pd chi v) v hx))).continuousAt)
  have i5 : Integrable (fun x => pd chi v x * f x) :=
    integrable_mul_of_local hdc.continuous hdcC
      (fun x hx => (hf x (pd_tsupport_subset chi v hx)).continuousAt)
  have e1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := chi) (g := pd f v) (v := v) i2 i1 i3
    (fun x _ => hchi.differentiable (by norm_num) x)
    (fun x hx => (hdf x hx).differentiableAt (by norm_num))
  have e2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := pd chi v) (g := f) (v := v) i4 i2 i5
    (fun x _ => hdc.differentiable (by norm_num) x)
    (fun x hx => (hf x (pd_tsupport_subset chi v hx)).differentiableAt (by norm_num))
  change (∫ x, chi x * pd (pd f v) v x) = -(∫ x, pd chi v x * pd f v x) at e1
  change (∫ x, pd chi v x * pd f v x) = -(∫ x, pd (pd chi v) v x * f x) at e2
  rw [e1, e2, neg_neg]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- Local C² Green identity. No integration-by-parts hypothesis is assumed. -/
theorem green_laplacian {f chi : ℂ → ℝ}
    (hf : ∀ x ∈ tsupport chi, ContDiffAt ℝ 2 f x)
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi) :
    (∫ x, chi x * Δ f x) = ∫ x, f x * Δ chi x := by
  have hleft : (∫ x, chi x * Δ f x) =
      ∫ x, chi x * pd (pd f 1) 1 x + chi x * pd (pd f Complex.I) Complex.I x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport chi
    · simp only [laplacian_eq_pd2 (hf x hx), mul_add]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hir (v : ℂ) : Integrable (fun x => pd (pd chi v) v x * f x) :=
    integrable_mul_of_local (pd_contDiff (n := 0) (pd_contDiff (n := 1) hchi v) v).continuous
      (pd_hasCompactSupport (pd_hasCompactSupport hc v) v)
      (fun x hx => (hf x (pd_tsupport_subset chi v
        (pd_tsupport_subset (pd chi v) v hx))).continuousAt)
  have hil (v : ℂ) : Integrable (fun x => chi x * pd (pd f v) v x) :=
    integrable_mul_of_local hchi.continuous hc (fun x hx =>
      (pd_contDiffAt (n := 0) (pd_contDiffAt (n := 1) (hf x hx) v) v).continuousAt)
  rw [hleft, integral_add (hil 1) (hil Complex.I), green_pd 1 hf hchi hc,
    green_pd Complex.I hf hchi hc]
  have hir' (v : ℂ) : Integrable (fun x => f x * pd (pd chi v) v x) := by
    simpa only [mul_comm] using hir v
  rw [← integral_add (hir' 1) (hir' Complex.I)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [laplacian_eq_pd2 hchi.contDiffAt, mul_add]

theorem laplacian_continuousAt {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (Δ f) x := by
  have he : Δ f =ᶠ[𝓝 x] (fun y => pd (pd f 1) 1 y + pd (pd f Complex.I) Complex.I y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact laplacian_eq_pd2 hy
  exact ((pd_contDiffAt (n := 0) (pd_contDiffAt (n := 1) hf 1) 1).continuousAt.add
    (pd_contDiffAt (n := 0) (pd_contDiffAt (n := 1) hf Complex.I) Complex.I).continuousAt).congr_of_eventuallyEq he

theorem laplacian_tsupport_subset (f : ℂ → ℝ) : tsupport (Δ f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  have he := laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hxf)
  have hz : Δ f x = 0 := by simpa [Pi.zero_def] using he.eq_of_nhds
  exact hx hz

theorem laplacian_hasCompactSupport {f : ℂ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (Δ f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (laplacian_tsupport_subset f)

end AreaDeficit
