import FunctionTheory.Conformal.BlaschkeUnicritical
import FunctionTheory.Conformal.LocalConjugacyCritical
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Metric Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A proper map between conformally parametrised domains with a single
critical point mapping to the next chart centre becomes a monomial in
those charts. Properness is stated for the actual source and target domains. -/
theorem exists_monomial_in_unicritical_conformal_charts
    {U V : Set ℂ} (f σ τ : ℂ → ℂ)
    (hσ : DifferentiableOn ℂ σ (ball (0:ℂ) 1))
    (hτ : DifferentiableOn ℂ τ (ball (0:ℂ) 1))
    (hσbij : BijOn σ (ball (0:ℂ) 1) U)
    (hτbij : BijOn τ (ball (0:ℂ) 1) V)
    (hf : DifferentiableOn ℂ f U) (hmap : MapsTo f U V)
    (hproper : IsProperMap (fun z : U => (⟨f z,hmap z.property⟩ : V)))
    (hcentre : f (σ 0)=τ 0)
    (hcrit : ∀ z∈U, deriv f z=0 ↔ z=σ 0) :
    ∃ (d : ℕ) (c : ℂ), 2≤d ∧ ‖c‖=1 ∧
      ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (c*z^d) := by
  have hU : IsOpen U := by
    rw [← hσbij.image_eq]
    exact TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hσ hσbij.injOn
  have hV : IsOpen V := by
    rw [← hτbij.image_eq]
    exact TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hτ hτbij.injOn
  let q := invFunOn τ (ball (0:ℂ) 1)
  have hq : DifferentiableOn ℂ q V := by
    have H := DifferentiableOn.invFunOn hτ isOpen_ball hτbij.injOn
    rwa [hτbij.image_eq] at H
  have hqmap : MapsTo q V (ball (0:ℂ) 1) := hτbij.surjOn.mapsTo_invFunOn
  let F : ℂ → ℂ := fun z => q (f (σ z))
  have hFd : DifferentiableOn ℂ F (ball (0:ℂ) 1) :=
    hq.comp (hf.comp hσ hσbij.mapsTo) (hmap.comp hσbij.mapsTo)
  have hFm : MapsTo F (ball (0:ℂ) 1) (ball (0:ℂ) 1) :=
    hqmap.comp (hmap.comp hσbij.mapsTo)
  let σh := hσ.toHomeomorphOfBijOn isOpen_ball hσbij
  let τh := hτ.toHomeomorphOfBijOn isOpen_ball hτbij
  let fR : U → V := fun z => ⟨f z,hmap z.property⟩
  have hFp : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨F z,hFm z.property⟩ : ball (0:ℂ) 1)) := by
    convert τh.symm.isProperMap.comp (hproper.comp σh.isProperMap) using 1
    funext z
    apply Subtype.ext
    rfl
  have hconj : ∀ z∈ball (0:ℂ) 1, f (σ z)=τ (F z) := by
    intro z hz
    exact (hτbij.invOn_invFunOn.2 (hmap (hσbij.mapsTo hz))).symm
  have hF0 : F 0=0 := by
    dsimp only [F]
    rw [hcentre]
    exact hτbij.injOn.leftInvOn_invFunOn (mem_ball_self one_pos)
  have hderiv : ∀ z∈ball (0:ℂ) 1, deriv f (σ z)=0 ↔ deriv F z=0 := by
    intro z hz
    apply deriv_eq_zero_iff_of_local_conjugacy
      (hFd.differentiableAt (isOpen_ball.mem_nhds hz))
      (hf.differentiableAt (hU.mem_nhds (hσbij.mapsTo hz)))
      (hσ.differentiableAt (isOpen_ball.mem_nhds hz))
      (hτ.differentiableAt (isOpen_ball.mem_nhds (hFm hz)))
      (TauCeti.deriv_ne_zero_of_injOn hσ isOpen_ball hσbij.injOn hz)
      (TauCeti.deriv_ne_zero_of_injOn hτ isOpen_ball hτbij.injOn (hFm hz))
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hconj w hw
  have hFd0 : deriv F 0=0 := (hderiv 0 (mem_ball_self one_pos)).mp
    ((hcrit (σ 0) (hσbij.mapsTo (mem_ball_self one_pos))).mpr rfl)
  have hFc : ∀ z∈ball (0:ℂ) 1, z≠0 → deriv F z≠0 := by
    intro z hz hn H
    have H' := (hcrit (σ z) (hσbij.mapsTo hz)).mp ((hderiv z hz).mpr H)
    exact hn (hσbij.injOn hz (mem_ball_self one_pos) H')
  obtain ⟨d,c,hd,hc,heq⟩ := exists_monomial_of_isProperMap_unicritical_disc
    (hFd.analyticOnNhd isOpen_ball) hFm hFp hF0 hFd0 hFc
  refine ⟨d,c,hd,hc,?_⟩
  intro z hz
  rw [hconj z hz,heq hz]

end FunctionTheory
