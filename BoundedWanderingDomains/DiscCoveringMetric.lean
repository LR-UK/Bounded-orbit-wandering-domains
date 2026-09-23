import BoundedWanderingDomains.HolomorphicLifting
import BoundedWanderingDomains.DiscSchwarzPick
import BoundedWanderingDomains.ConformalLaplacian
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Moebius
import Mathlib.Analysis.Convex.Contractible

/-!
# The curvature −1 metric induced by a holomorphic disc covering

The covering condition is Mathlib's topological covering condition on the restriction
to the open unit disc. Nonvanishing derivatives are proved from it, not assumed.
-/

open Set Function Filter Metric
open scoped Topology ContDiff

namespace AreaDeficit

/-- A surjective holomorphic covering by the open unit disc. Since the disc is
simply connected, this is a universal covering. -/
structure IsHolomorphicDiscCovering (p : ℂ → ℂ) (S : Set ℂ) : Prop where
  holo : DifferentiableOn ℂ p (ball 0 1)
  maps : MapsTo p (ball 0 1) S
  surj : SurjOn p (ball 0 1) S
  covering : IsCoveringMapOn (fun w : ball (0 : ℂ) 1 => p w) S

theorem unitBall_isSimplyConnected : IsSimplyConnected (ball (0 : ℂ) 1) := by
  let := (convex_ball (0 : ℂ) 1).contractibleSpace (nonempty_ball.mpr (by norm_num))
  change SimplyConnectedSpace (ball (0 : ℂ) 1)
  exact inferInstance

/-- The metric induced by a disc covering, using an arbitrary selected preimage.
Its value off the image is immaterial. Fibre independence is proved below. -/
noncomputable def coveringDensity (p : ℂ → ℂ) (z : ℂ) : ℝ :=
  let w := invFunOn p (ball 0 1) z
  discDensity w / ‖deriv p w‖

theorem discDensity_contDiffAt {w : ℂ} (hw : ‖w‖ < 1) :
    ContDiffAt ℝ 2 discDensity w := by
  have hs : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  exact contDiffAt_const.div (discDenom_contDiff.of_le (by simp)).contDiffAt
    (ne_of_gt (sub_pos.mpr hs))

/-- Recentre the unit disc; the derivative at zero fixes the curvature −1 scale. -/
theorem exists_disc_recentring {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∃ m : ℂ → ℂ, DifferentiableOn ℂ m (ball 0 1) ∧
      MapsTo m (ball 0 1) (ball 0 1) ∧ m 0 = w ∧
      discDensity w * ‖deriv m 0‖ = 2 := by
  have hn : ‖w‖ < 1 := by simpa using hw
  have hneg : ‖-w‖ < 1 := by simpa using hn
  let m : ℂ → ℂ := fun z => (z - -w) / (1 - (starRingEnd ℂ) (-w) * z)
  refine ⟨m, TauCeti.differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hneg,
    TauCeti.mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hneg, by simp [m], ?_⟩
  have hs : 0 < 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have he : deriv m 0 = ((1 - Complex.normSq w : ℝ) : ℂ) := by
    simp [m, Complex.mul_conj, mul_comm]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact div_mul_cancel₀ 2 (ne_of_gt hs)

namespace IsHolomorphicDiscCovering

variable {p : ℂ → ℂ} {S : Set ℂ} (hp : IsHolomorphicDiscCovering p S)
include hp

theorem local_injective {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ V ⊆ ball 0 1 ∧ InjOn p V := by
  obtain ⟨e, hew, he⟩ := hp.covering.isLocalHomeomorphOn ⟨w, hw⟩ (hp.maps hw)
  refine ⟨Subtype.val '' e.source, isOpen_ball.isOpenMap_subtype_val _ e.open_source,
    ⟨⟨w, hw⟩, hew, rfl⟩, ?_, ?_⟩
  · rintro z ⟨v, hv, rfl⟩
    exact v.2
  · rintro z ⟨v, hv, rfl⟩ z' ⟨v', hv', rfl⟩ h
    apply congrArg Subtype.val (e.injOn hv hv' ?_)
    simpa only [← he] using h

theorem deriv_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : deriv p w ≠ 0 := by
  obtain ⟨V, hV, hwV, hVD, hinj⟩ := hp.local_injective hw
  exact TauCeti.deriv_ne_zero_of_injOn (hp.holo.mono hVD) hV hinj hwV

/-- Schwarz–Pick with the density computed at any chosen point of the fibre. -/
theorem schwarz_at_fibre {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgS : MapsTo g (ball 0 1) S)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hwp : p w = g 0) :
    (discDensity w / ‖deriv p w‖) * ‖deriv g 0‖ ≤ 2 := by
  obtain ⟨h, h0, hm, hfac, hh, hd⟩ := exists_holomorphic_covering_lift
    isOpen_ball unitBall_isSimplyConnected (by simp) hw hwp hp.covering
    (hp.holo.analyticOnNhd isOpen_ball) hg hgS (fun z hz _ => hp.deriv_ne_zero hz)
  have hs := disc_schwarz_centre (by norm_num : (0 : ℝ) < 1) hh hm
  have hd0 := (hd 0 (by simp)).deriv
  rw [h0] at hd0 hs
  rw [hd0, norm_div] at hs
  simpa only [div_one, div_mul_eq_mul_div, mul_div_assoc] using hs

theorem extremal_at_fibre {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ MapsTo g (ball 0 1) S ∧
      g 0 = p w ∧ (discDensity w / ‖deriv p w‖) * ‖deriv g 0‖ = 2 := by
  obtain ⟨m, hm, hmD, hm0, hmd⟩ := exists_disc_recentring hw
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  refine ⟨p ∘ m, hp.holo.comp hm hmD, hp.maps.comp hmD, by simp [hm0], ?_⟩
  have hd := ((hp.holo.differentiableAt (isOpen_ball.mem_nhds (hmD h0))).hasDerivAt.comp 0
    (hm.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt).deriv
  rw [hm0] at hd
  rw [hd, norm_mul]
  have hp0 : ‖deriv p w‖ ≠ 0 := norm_ne_zero_iff.mpr (hp.deriv_ne_zero hw)
  calc
    _ = discDensity w * ‖deriv m 0‖ := by field_simp
    _ = 2 := hmd

theorem fibre_density_eq {v w : ℂ} (hv : v ∈ ball (0 : ℂ) 1)
    (hw : w ∈ ball (0 : ℂ) 1) (hvw : p v = p w) :
    discDensity v / ‖deriv p v‖ = discDensity w / ‖deriv p w‖ := by
  have hle {a b : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1)
      (hab : p a = p b) : discDensity a / ‖deriv p a‖ ≤ discDensity b / ‖deriv p b‖ := by
    obtain ⟨g, hg, hgS, hg0, he⟩ := hp.extremal_at_fibre hb
    have hs := hp.schwarz_at_fibre hg hgS ha (hab.trans hg0.symm)
    have hd : 0 < ‖deriv g 0‖ := by
      have hn := norm_nonneg (deriv g 0)
      by_contra h
      have hz : ‖deriv g 0‖ = 0 := le_antisymm (le_of_not_gt h) hn
      rw [hz, mul_zero] at he
      norm_num at he
    exact (mul_le_mul_iff_left₀ hd).mp (hs.trans_eq he.symm)
  exact le_antisymm (hle hv hw hvw) (hle hw hv hvw.symm)

theorem density_eq {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    coveringDensity p (p w) = discDensity w / ‖deriv p w‖ := by
  exact hp.fibre_density_eq (invFunOn_mem ⟨w, hw, rfl⟩) hw
    (invFunOn_eq ⟨w, hw, rfl⟩)

theorem density_pos {z : ℂ} (hz : z ∈ S) : 0 < coveringDensity p z := by
  obtain ⟨w, hw, rfl⟩ := hp.surj hz
  rw [hp.density_eq hw]
  exact div_pos (discDensity_pos (by simpa using hw))
    (norm_pos_iff.mpr (hp.deriv_ne_zero hw))

theorem density_schwarz {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgS : MapsTo g (ball 0 1) S) :
    coveringDensity p (g 0) * ‖deriv g 0‖ ≤ 2 := by
  obtain ⟨w, hw, he⟩ := hp.surj (hgS (by simp : (0 : ℂ) ∈ ball 0 1))
  rw [← he, hp.density_eq hw]
  exact hp.schwarz_at_fibre hg hgS hw he

theorem density_extremal {z : ℂ} (hz : z ∈ S) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ MapsTo g (ball 0 1) S ∧
      g 0 = z ∧ coveringDensity p z * ‖deriv g 0‖ = 2 := by
  obtain ⟨w, hw, rfl⟩ := hp.surj hz
  rw [hp.density_eq hw]
  exact hp.extremal_at_fibre hw

/-- Locally the induced density is the pullback of the disc density by a
holomorphic inverse branch. No regularity of the selected preimage is needed. -/
theorem local_density_expression {z : ℂ} (hz : z ∈ S) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z ∧ h z ∈ ball 0 1 ∧ deriv h z ≠ 0 ∧
      coveringDensity p =ᶠ[𝓝 z] (fun t => ‖deriv h t‖ * discDensity (h t)) := by
  obtain ⟨w, hw, rfl⟩ := hp.surj hz
  obtain ⟨V, hV, hwV, hVD, hinj⟩ := hp.local_injective hw
  have hpV := hp.holo.mono hVD
  have hO : IsOpen (p '' V) := TauCeti.isOpen_image_of_differentiableOn_of_injOn hV hpV hinj
  let h := invFunOn p V
  have hh : DifferentiableOn ℂ h (p '' V) := hpV.invFunOn hV hinj
  have hpw : p w ∈ p '' V := mem_image_of_mem p hwV
  have hh0 : h (p w) = w := hinj.leftInvOn_invFunOn hwV
  have hd0 : deriv h (p w) = (deriv p w)⁻¹ :=
    (TauCeti.hasDerivAt_invFunOn hpV hV hinj hwV).deriv
  refine ⟨h, hh.analyticAt (hO.mem_nhds hpw), by simpa [hh0] using hw,
    by rw [hd0]; exact inv_ne_zero (hp.deriv_ne_zero hw), ?_⟩
  filter_upwards [hO.mem_nhds hpw] with t ht
  have hht : h t ∈ V := invFunOn_mem ht
  have hpt : p (h t) = t := invFunOn_eq ht
  have hd : deriv h t = (deriv p (h t))⁻¹ := by
    simpa only [hpt] using (TauCeti.hasDerivAt_invFunOn hpV hV hinj hht).deriv
  rw [← hpt, hp.density_eq (hVD hht), hpt, hd, norm_inv]
  exact div_eq_inv_mul _ _

theorem density_contDiffAt {z : ℂ} (hz : z ∈ S) :
    ContDiffAt ℝ 2 (coveringDensity p) z := by
  obtain ⟨h, hh, hD, hd, he⟩ := hp.local_density_expression hz
  exact (pullback_density_contDiffAt (discDensity_contDiffAt (by simpa using hD)) hh hd).congr_of_eventuallyEq he

theorem density_curvature {z : ℂ} (hz : z ∈ S) :
    Laplacian.laplacian (fun t => Real.log (coveringDensity p t)) z =
      (coveringDensity p z)^2 := by
  obtain ⟨h, hh, hD, hd, he⟩ := hp.local_density_expression hz
  have hn : ‖h z‖ < 1 := by simpa using hD
  have hlog := he.fun_comp Real.log
  simp only [Function.comp_def] at hlog
  rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds, he.eq_of_nhds]
  exact pullback_density_curvature (discDensity_contDiffAt hn) (discDensity_pos hn)
    (discDensity_curvature hn) hh hd

end IsHolomorphicDiscCovering

end AreaDeficit
