import FunctionTheory.NormalFamilies.SphericalHurwitz
import FunctionTheory.Conformal.LittlePicardBloch

/-! # Omitted-values Montel via Zalcman
The rescaling theorem is the attributed public result of Li and Luo.
Spherical Hurwitz and Little Picard exclude its nonconstant entire limit. -/

open Set Filter Metric OnePoint
open scoped Topology
namespace FunctionTheory
open NoWanderingDomains
set_option autoImplicit false

/-- Every fixed bounded disc of the rescaled plane eventually maps into
any prescribed neighbourhood of the limiting centre. -/
theorem eventually_rescaled_ball_subset {z : ℕ → ℂ} {ρ : ℕ → ℝ} {z₀ : ℂ}
    {U : Set ℂ} (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0))
    (hρpos : ∀ n, 0 < ρ n) (hU : U ∈ 𝓝 z₀) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, MapsTo (fun w => z n + (ρ n : ℂ)*w) (ball 0 R) U := by
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hz' := hz.eventually (ball_mem_nhds z₀ (by positivity : 0 < δ/2))
  have hρ' := hρ.eventually (gt_mem_nhds (by positivity : (0:ℝ) < δ/(2*R)))
  filter_upwards [hz',hρ'] with n hzn hρn w hw
  apply hδU
  rw [mem_ball,dist_eq_norm]
  have hw' : ‖w‖ < R := by simpa using hw
  have hz'' : ‖z n-z₀‖ < δ/2 := by simpa [dist_eq_norm] using hzn
  have hρR : ρ n * R < δ/2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2*R)).mp hρn
    nlinarith
  have he : ‖(ρ n : ℂ)*w‖ < δ/2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρpos n)]
    exact (mul_lt_mul_of_pos_left hw' (hρpos n)).trans hρR
  have ht : ‖z n+(ρ n : ℂ)*w-z₀‖ ≤ ‖z n-z₀‖+‖(ρ n : ℂ)*w‖ := by
    convert norm_add_le (z n-z₀) ((ρ n : ℂ)*w) using 1 <;> congr 1 <;> ring
  linarith

/-- Montel's omitted-values theorem via the public Zalcman rescaling lemma,
spherical Hurwitz, and Little Picard. The three omitted sphere values are
two distinct finite values and infinity. -/
theorem isNormalAt_of_two_omitted_values {𝓕 : Set (ℂ → ℂ̂)} {U : Set ℂ}
    {a b : ℂ} (hab : a ≠ b) (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U)
    (homit : ∀ F ∈ 𝓕, ∀ w ∈ U,
      F w ≠ (a : ℂ̂) ∧ F w ≠ (b : ℂ̂) ∧ F w ≠ ∞)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : IsNormalAt 𝓕 z₀ := by
  classical
  by_contra hn
  obtain ⟨F,z,ρ,g,hF,hz,hρpos,hρ,hg,hgder,-,hconv⟩ :=
    exists_zalcman_rescale hU hol hz₀ hn
  have hnc : ∀ p : ℂ̂, ¬ ∀ w, g w = p := by
    intro p hp
    have he : g = fun _ => p := funext hp
    simp [he,sphericalDeriv] at hgder
  have hev : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      SphereHolomorphicOn (fun w => F n (z n+(ρ n : ℂ)*w)) (ball 0 R) ∧
      ∀ w ∈ ball 0 R, F n (z n+(ρ n : ℂ)*w) ≠ (a : ℂ̂) ∧
        F n (z n+(ρ n : ℂ)*w) ≠ (b : ℂ̂) ∧
        F n (z n+(ρ n : ℂ)*w) ≠ ∞ := by
    intro R hR
    filter_upwards [eventually_rescaled_ball_subset hz hρ hρpos (hU.mem_nhds hz₀) hR]
      with n hn
    exact ⟨sphereHolomorphicOn_mono ((hol (F n) (hF n)).comp_affine (z n) (ρ n))
      isOpen_ball hn,fun w hw => homit (F n) (hF n) _ (hn hw)⟩
  have hgc : Continuous g := continuousOn_univ.mp hg.continuousOn
  have hginf : ∀ w, g w ≠ ∞ := (spherical_hurwitz_infty hgc hconv
    (fun R hR => (hev R hR).mono fun n hn => ⟨hn.1,fun w hw => (hn.2 w hw).2.2⟩)).resolve_right (hnc ∞)
  have hg0 : ∀ w, g w ≠ (a : ℂ̂) := (spherical_hurwitz_finite hgc hconv
    (fun R hR => (hev R hR).mono fun n hn => ⟨hn.1,fun w hw => (hn.2 w hw).1⟩)).resolve_right (hnc _)
  have hg1 : ∀ w, g w ≠ (b : ℂ̂) := (spherical_hurwitz_finite hgc hconv
    (fun R hR => (hev R hR).mono fun n hn => ⟨hn.1,fun w hw => (hn.2 w hw).2.1⟩)).resolve_right (hnc _)
  have hcoe : ∀ w, ((chartFiniteMap (g w) : ℂ) : ℂ̂) = g w := by
    intro w
    cases hp : g w with
    | infty => exact False.elim (hginf w hp)
    | coe a => rfl
  have hd : Differentiable ℂ (fun w => chartFiniteMap (g w)) :=
    differentiableOn_univ.mp (hg.differentiableOn_chartFiniteMap (fun w _ => hginf w))
  obtain ⟨c,hc⟩ := exists_eq_const_of_two_omitted_values hd hab
    (fun w he => hg0 w (by rw [← hcoe w,he]))
    (fun w he => hg1 w (by rw [← hcoe w,he]))
  apply hnc (c : ℂ̂)
  intro w
  rw [← hcoe w,congrFun hc w]

end FunctionTheory
