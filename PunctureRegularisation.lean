import LaplacianChain
import LogBarrier

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff

namespace AreaDeficit

noncomputable def puncturedBeta (F : Finset ℂ) (u L : ℂ → ℝ) (a : ℝ) (z : ℂ) : ℝ :=
  if z ∈ F then 0 else beta (a * u z + L z) / a

noncomputable def puncturedSlope (F : Finset ℂ) (u L : ℂ → ℝ) (a : ℝ) (z : ℂ) : ℝ :=
  if z ∈ F then 0 else Real.smoothTransition (a * u z + L z)

theorem argument_eventually_nonpos {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {p : ℂ} (hp : p ∈ F)
    (hu : ∃ M : ℝ, ∀ᶠ z in 𝓝 p, z ∉ F → u z ≤ M)
    (hL : ∀ B : ℝ, ∀ᶠ z in 𝓝[≠] p, L z ≤ B) :
    ∀ᶠ z in 𝓝 p, z ∉ F → a * u z + L z ≤ 0 := by
  obtain ⟨M, hM⟩ := hu
  filter_upwards [hM, eventually_nhdsWithin_iff.mp (hL (-a * M))] with z hz hzL hzf
  have hzp : z ≠ p := by intro h; subst z; exact hzf hp
  have h1 := hz hzf
  have h2 := hzL hzp
  nlinarith

theorem puncturedBeta_eventually_zero {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {p : ℂ} (hp : p ∈ F)
    (hu : ∃ M : ℝ, ∀ᶠ z in 𝓝 p, z ∉ F → u z ≤ M)
    (hL : ∀ B : ℝ, ∀ᶠ z in 𝓝[≠] p, L z ≤ B) :
    puncturedBeta F u L a =ᶠ[𝓝 p] 0 := by
  filter_upwards [argument_eventually_nonpos ha hp hu hL] with z hz
  by_cases hzf : z ∈ F
  · simp [puncturedBeta, hzf]
  · simp [puncturedBeta, hzf, beta_zero_of_nonpos (hz hzf)]

theorem puncturedSlope_eventually_zero {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {p : ℂ} (hp : p ∈ F)
    (hu : ∃ M : ℝ, ∀ᶠ z in 𝓝 p, z ∉ F → u z ≤ M)
    (hL : ∀ B : ℝ, ∀ᶠ z in 𝓝[≠] p, L z ≤ B) :
    puncturedSlope F u L a =ᶠ[𝓝 p] 0 := by
  filter_upwards [argument_eventually_nonpos ha hp hu hL] with z hz
  by_cases hzf : z ∈ F
  · simp [puncturedSlope, hzf]
  · simp [puncturedSlope, hzf, Real.smoothTransition.zero_of_nonpos (hz hzf)]

theorem eventually_not_mem_finset (F : Finset ℂ) {x : ℂ} (hx : x ∉ F) :
    ∀ᶠ y in 𝓝 x, y ∉ F :=
  F.finite_toSet.isClosed.isOpen_compl.mem_nhds hx

theorem puncturedBeta_eq_near {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ} {x : ℂ}
    (hx : x ∉ F) :
    puncturedBeta F u L a =ᶠ[𝓝 x] (fun z => beta (a * u z + L z) / a) := by
  filter_upwards [eventually_not_mem_finset F hx] with z hz
  simp [puncturedBeta, hz]

theorem puncturedBeta_contDiffAt {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {x : ℂ}
    (hu : x ∉ F → ContDiffAt ℝ 2 u x)
    (hLc : x ∉ F → ContDiffAt ℝ 2 L x)
    (hup : x ∈ F → ∃ M : ℝ, ∀ᶠ z in 𝓝 x, z ∉ F → u z ≤ M)
    (hLp : x ∈ F → ∀ B : ℝ, ∀ᶠ z in 𝓝[≠] x, L z ≤ B) :
    ContDiffAt ℝ 2 (puncturedBeta F u L a) x := by
  by_cases hx : x ∈ F
  · exact contDiffAt_const.congr_of_eventuallyEq
      (puncturedBeta_eventually_zero ha hx (hup hx) (hLp hx))
  · have hw : ContDiffAt ℝ 2 (fun z => a * u z + L z) x :=
      (contDiffAt_const.mul (hu hx)).add (hLc hx)
    exact (((beta_contDiff.of_le (by simp)).contDiffAt.comp x hw).div_const a).congr_of_eventuallyEq
      (puncturedBeta_eq_near hx)

theorem laplacian_fun_const_mul {f : ℂ → ℝ} {x : ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f x) : Δ (fun z => c * f z) x = c * Δ f x := by
  simpa only [Pi.smul_def, smul_eq_mul] using laplacian_smul c hf

theorem laplacian_fun_add {f g : ℂ → ℝ} {x : ℂ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun z => f z + g z) x = Δ f x + Δ g x := by
  simpa only [Pi.add_def] using hf.laplacian_add hg

/-- A harmonic perturbation only adds a nonnegative convexity term. -/
theorem puncturedBeta_laplacian_ge {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {x : ℂ} (hx : x ∉ F)
    (hu : ContDiffAt ℝ 2 u x) (hL : HarmonicAt L x) :
    puncturedSlope F u L a x * Δ u x ≤ Δ (puncturedBeta F u L a) x := by
  let w : ℂ → ℝ := fun z => a * u z + L z
  have hw : ContDiffAt ℝ 2 w x := (contDiffAt_const.mul hu).add hL.1
  have hwlap : Δ w x = a * Δ u x := by
    rw [laplacian_fun_add (contDiffAt_const.mul hu) hL.1,
      laplacian_fun_const_mul a hu, hL.2.eq_of_nhds]
    simp
  have hb : ContDiffAt ℝ 2 (fun z => beta (w z)) x :=
    (beta_contDiff.of_le (by simp)).contDiffAt.comp x hw
  rw [(laplacian_congr_nhds (puncturedBeta_eq_near (u := u) (L := L) (a := a) hx)).eq_of_nhds]
  have heq : (fun z => beta (a * u z + L z) / a) = fun z => a⁻¹ * beta (w z) := by
    funext z
    simp [w, div_eq_mul_inv, mul_comm]
  rw [heq, laplacian_fun_const_mul a⁻¹ hb,
    laplacian_comp hw (beta_contDiff.of_le (by simp)) beta_hasDerivAt transition_hasDerivAt,
    hwlap]
  simp only [puncturedSlope, ite_eq_right hx]
  have hpos := mul_nonneg (transition_deriv_nonneg (w x)) (gradientSq_nonneg w x)
  have he : a⁻¹ * (Real.smoothTransition (w x) * (a * Δ u x) +
      deriv Real.smoothTransition (w x) * gradientSq w x) =
      Real.smoothTransition (w x) * Δ u x +
        a⁻¹ * (deriv Real.smoothTransition (w x) * gradientSq w x) := by
    field_simp
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr ha.le) hpos)

theorem puncturedBeta_bounds {F : Finset ℂ} {u L : ℂ → ℝ} {a : ℝ}
    (ha : 0 < a) {x : ℂ} (hL : L x ≤ 0) :
    0 ≤ puncturedBeta F u L a x ∧ puncturedBeta F u L a x ≤ max (u x) 0 := by
  by_cases hx : x ∈ F
  · simp [puncturedBeta, hx]
  · simp only [puncturedBeta, ite_eq_right hx]
    constructor
    · exact div_nonneg (beta_bounds _).1 ha.le
    · apply (div_le_iff₀ ha).mpr
      apply (beta_bounds _).2.trans
      apply max_le
      · nlinarith [le_max_left (u x) 0]
      · exact mul_nonneg (le_max_right _ _) ha.le

theorem transition_scaled_add_tendsto (u L : ℝ) (hL : L ≤ 0) :
    Tendsto (fun n : ℕ => Real.smoothTransition (((n : ℝ) + 1) * u + L)) atTop
      (𝓝 (if 0 < u then 1 else 0)) := by
  by_cases hu : 0 < u
  · obtain ⟨N, hN⟩ := exists_nat_gt ((1 - L) / u)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnr : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have hnu : 1 - L < (N : ℝ) * u := (div_lt_iff₀ hu).mp hN
    simp only [ite_eq_left hu]
    exact (Real.smoothTransition.one_of_one_le (by nlinarith)).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards with n
    simp only [ite_eq_right hu]
    apply Eq.symm
    apply Real.smoothTransition.zero_of_nonpos
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (n : ℝ) + 1 by positivity) (le_of_not_gt hu)
    linarith

end AreaDeficit
