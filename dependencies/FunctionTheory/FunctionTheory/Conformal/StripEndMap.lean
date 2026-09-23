import FunctionTheory.Conformal.StraightBoundaryInverse
import FunctionTheory.Conformal.StripCoordinates
import FunctionTheory.Conformal.StripEndCoordinates
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # A normalized conformal strip map with end estimates

For a simply connected domain in the standard strip, bounded to the left and
equal to that strip sufficiently far to the right, exponential coordinates
give a bounded domain with a straight boundary at zero. If its boundary is a
Jordan curve, Carathéodory continuity and local reflection construct the map
and prove both end asymptotics. No reflected analytic map is assumed.

The Jordan-curve property of the exponential image remains a geometric
hypothesis, to be supplied by the decorated-domain construction.
-/

open Set Metric Complex Function Filter Asymptotics
open scoped Topology

namespace FunctionTheory

def exponentialImage (U : Set ℂ) : Set ℂ := (fun z => exp (-z)) '' U

theorem zero_mem_frontier_of_halfplane_neighbourhood
    {Ω : Set ℂ} {r : ℝ} (hΩ : IsOpen Ω) (hr : 0 < r)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re) :
    (0 : ℂ) ∈ frontier Ω := by
  rw [hΩ.frontier_eq]
  refine ⟨?_, fun h => by simpa using (hnear 0 (mem_ball_self hr)).mp h⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min r ε / 2
  have ht : 0 < t := half_pos (lt_min hr hε)
  have htr : t < r := (half_lt_self (lt_min hr hε)).trans_le (min_le_left _ _)
  have htε : t < ε := (half_lt_self (lt_min hr hε)).trans_le (min_le_right _ _)
  have htb : (t : ℂ) ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos ht] using htr
  refine ⟨(t : ℂ), (hnear _ htb).mpr (by simpa using ht), ?_⟩
  simpa only [dist_zero_left, norm_real, Real.norm_eq_abs, abs_of_pos ht] using htε

theorem isBounded_exponentialImage_of_re_lower_bound {U : Set ℂ} {L : ℝ}
    (hleft : ∀ z ∈ U, L ≤ z.re) : Bornology.IsBounded (exponentialImage U) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.exp (-L), ?_⟩
  rintro w ⟨z, hz, rfl⟩
  rw [norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (neg_le_neg (hleft z hz))

theorem exponentialImage_agrees_with_halfplane_at_zero {U : Set ℂ} {R : ℝ}
    (hUS : U ⊆ standardHorizontalStrip)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U) :
    ∀ w ∈ ball (0 : ℂ) (Real.exp (-R)), w ∈ exponentialImage U ↔ 0 < w.re := by
  intro w hw
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact re_exp_neg_pos_of_mem_strip (hUS hz)
  · intro hre
    have hwne : w ≠ 0 := by intro h; simp [h] at hre
    have hnorm : ‖w‖ < Real.exp (-R) := by simpa only [mem_ball, dist_zero_right] using hw
    have hlog : Real.log ‖w‖ < -R := by
      rw [← Real.exp_lt_exp, Real.exp_log (norm_pos_iff.mpr hwne)]
      exact hnorm
    refine ⟨-log w, htail _ (neg_log_mem_strip hre) ?_, exp_neg_neg_log_of_re_pos hre⟩
    simp only [neg_re, log_re]
    linarith

theorem tendsto_re_atTop_of_strip_translation_asymptotic {U : Set ℂ}
    {φ : ℂ → ℂ} {ρ : ℝ}
    (h : (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
      (fun z => Real.exp (-z.re))) :
    Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop := by
  have hre : Tendsto Complex.re (comap Complex.re atTop ⊓ 𝓟 U) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hdecay : Tendsto (fun z : ℂ => Real.exp (-z.re))
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hre)
  have herr : Tendsto (fun z => (φ z - (z + (ρ : ℂ))).re)
      (comap Complex.re atTop ⊓ 𝓟 U) (𝓝 0) :=
    (Complex.continuous_re.tendsto 0).comp (h.trans_tendsto hdecay)
  apply ((hre.atTop_add (tendsto_const_nhds (x := ρ))).atTop_add herr).congr'
  apply Filter.Eventually.of_forall
  intro z
  simp only [sub_re, add_re, ofReal_re]
  ring

/-- A geometrically normalized strip map and both asymptotics needed in
Lemma 7.2. The exponential image must have Jordan boundary; its boundedness,
simple connectivity, and straight boundary at zero follow from the other
displayed geometric hypotheses. -/
theorem exists_normalized_strip_map_of_jordan_exponential_image
    {U : Set ℂ} {z₀ : ℂ} {L R : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUS : U ⊆ standardHorizontalStrip) (hleft : ∀ z ∈ U, L ≤ z.re)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U)
    (hJordan : TauCeti.IsJordanCurve (frontier (exponentialImage U))) (hz₀ : z₀ ∈ U) :
    ∃ (φ : ℂ → ℂ) (ρ : ℝ), DifferentiableOn ℂ φ U ∧
      BijOn φ U standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop := by
  let Ω := exponentialImage U
  have hed : DifferentiableOn ℂ (fun z => exp (-z)) U :=
    (differentiable_exp.comp differentiable_id.neg).differentiableOn
  have hei : InjOn (fun z => exp (-z)) U := bijOn_exp_neg_strip.injOn.mono hUS
  have hebij : BijOn (fun z => exp (-z)) U Ω := hei.bijOn_image
  have hΩo : IsOpen Ω := TauCeti.isOpen_image_of_differentiableOn_of_injOn hUo hed hei
  have hΩc : IsSimplyConnected Ω :=
    TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn hUo hUc hed hei
  have hΩb : Bornology.IsBounded Ω := isBounded_exponentialImage_of_re_lower_bound hleft
  have hnear := exponentialImage_agrees_with_halfplane_at_zero hUS htail
  have h0 : (0 : ℂ) ∈ frontier Ω :=
    zero_mem_frontier_of_halfplane_neighbourhood hΩo (Real.exp_pos _) hnear
  obtain ⟨G, hGc, hGd, hGbij, hG0, hG1, -, -⟩ :=
    exists_boundary_normalized_disc_map hΩo hΩc hΩb hJordan (hebij.mapsTo hz₀) h0
  obtain ⟨ψ, a, hψa, hψ0, ha, hψd, hψeq⟩ :=
    exists_analytic_extension_of_cayley_inverse hΩo (Real.exp_pos _) hnear hGc hGd hGbij hG1
  let g := invFunOn G (ball 0 1)
  have hgbij : BijOn g Ω (ball 0 1) := BijOn.symm hGbij.invOn_invFunOn.symm hGbij
  have hgd : DifferentiableOn ℂ g Ω := by
    simpa only [hGbij.image_eq] using DifferentiableOn.invFunOn hGd isOpen_ball hGbij.injOn
  let φ : ℂ → ℂ := fun z => discToHorizontalStrip (g (exp (-z)))
  have hφd : DifferentiableOn ℂ φ U :=
    differentiableOn_discToHorizontalStrip.comp (hgd.comp hed hebij.mapsTo)
      (hgbij.mapsTo.comp hebij.mapsTo)
  have hφbij : BijOn φ U standardHorizontalStrip :=
    bijOn_discToHorizontalStrip.comp (hgbij.comp hebij)
  have hφ0 : φ z₀ = 0 := by
    have hginv : g (exp (-z₀)) = 0 := by
      rw [← hG0]
      exact hGbij.injOn.leftInvOn_invFunOn (mem_ball_self one_pos)
    simp only [φ, hginv, discToHorizontalStrip_zero]
  have heq : EqOn (fun z => ψ (exp (-z))) (fun z => exp (-φ z)) U := by
    intro z hz
    exact (hψeq (hebij.mapsTo hz)).trans
      (exp_neg_discToHorizontalStrip (hgbij.mapsTo (hebij.mapsTo hz))).symm
  obtain ⟨ρ, hd, hv⟩ := stripEnd_estimates_of_reflected_map hUo hφd heq
    (fun z hz => hUS hz) (fun z hz => hφbij.mapsTo hz) hψa hψ0 ha hψd
  exact ⟨φ, ρ, hφd, hφbij, hφ0, hd, hv,
    tendsto_re_atTop_of_strip_translation_asymptotic hv⟩

end FunctionTheory
