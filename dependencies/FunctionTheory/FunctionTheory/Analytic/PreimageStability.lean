import TauCeti.Analysis.Complex.Conformal.Rouche
import TauCeti.Analysis.Complex.IsolatedZero
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Quantitative persistence of a prescribed value under perturbation. -/
theorem exists_preimage_of_circle_bound
    {f g : ℂ → ℂ} {a v : ℂ} {r μ δ : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall a r))
    (hg : AnalyticOnNhd ℂ g (closedBall a r))
    (hμ : ∀ z ∈ sphere a r, μ ≤ ‖f z - f a‖)
    (hδ : 2 * δ < μ)
    (hclose : ∀ z ∈ sphere a r, ‖f z - g z‖ < δ)
    (hv : ‖v - f a‖ < δ) :
    ∃ z ∈ ball a r, g z = v := by
  have hs : ∀ z ∈ sphere a r,
      ‖(f z - f a) - (g z - v)‖ < ‖f z - f a‖ := by
    intro z hz
    calc
      ‖(f z - f a) - (g z - v)‖ = ‖(f z - g z) + (v - f a)‖ := by congr 1; ring
      _ ≤ ‖f z - g z‖ + ‖v - f a‖ := norm_add_le _ _
      _ < 2 * δ := by linarith [hclose z hz]
      _ < μ := hδ
      _ ≤ ‖f z - f a‖ := hμ z hz
  obtain ⟨z, hz, heq⟩ := (TauCeti.rouche_exists_eq_zero_iff hr
    (hf.sub analyticOnNhd_const) (hg.sub analyticOnNhd_const) hs).mp
      ⟨a, mem_ball_self hr, sub_self _⟩
  exact ⟨z, hz, sub_eq_zero.mp heq⟩

/-- Every locally nonconstant holomorphic germ has a stable local image disk.
The closed disk used for the comparison is kept inside the working domain.
The disk selection follows the isolated-zero argument used in Tau Ceti's
Hurwitz theorem. -/
theorem exists_stable_local_image
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ∈ U)
    (hnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖f z - g z‖ < δ) →
      ∀ v : ℂ, ‖v - f a‖ < δ → ∃ z ∈ U ∩ ball a ε, g z = v := by
  have hpunct := ((hf a ha).eventually_eq_or_eventually_ne
    (analyticAt_const (v := f a))).resolve_left hnc
  have hev : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (z ≠ a → f z ≠ f a) :=
    (hU.eventually_mem ha).and (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hev
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  have hsub : closedBall a r ⊆ closedBall a R :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hrU : closedBall a r ⊆ U := fun z hz => (hball (hsub hz)).1
  have hne : ∀ z ∈ sphere a r, f z - f a ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr ((hball (hsub (sphere_subset_closedBall hz))).2
      (ne_of_mem_sphere hz hr.ne'))
  obtain ⟨μ, hμ, hbound⟩ := TauCeti.exists_pos_le_norm_of_mem_sphere
    ((hf.sub analyticOnNhd_const).continuousOn.mono
      (sphere_subset_closedBall.trans hrU)) hne
  refine ⟨μ / 3, by positivity, ?_⟩
  intro g hg hclose v hv
  obtain ⟨z, hz, heq⟩ := exists_preimage_of_circle_bound hr (hf.mono hrU)
    (hg.mono hrU) hbound (by linarith)
    (fun z hz => hclose z (hrU (sphere_subset_closedBall hz))) hv
  exact ⟨z, ⟨hrU (ball_subset_closedBall hz),
    ball_subset_ball (min_le_right _ _) hz⟩, heq⟩

/-- A compact set has uniformly dense preimages of every sufficiently dense
set of target values, even after a small holomorphic perturbation.
Extended distance handles an empty target set without the real-valued
`infDist` convention `infDist x ∅ = 0`. -/
theorem compact_preimage_density_of_approximation
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, f z = f a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (P : Set ℂ) (g : ℂ → ℂ),
      (∀ a ∈ K, infEDist (f a) P ≤ ENNReal.ofReal δ) →
      AnalyticOnNhd ℂ g U → (∀ z ∈ U, ‖f z - g z‖ < δ) →
      ∀ a ∈ K, ∃ z ∈ U, g z ∈ P ∧ dist a z < ε := by
  classical
  have hlocal : ∀ a : K, ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ z ∈ U, ‖f z - g z‖ < δ) →
      ∀ v : ℂ, ‖v - f a‖ < δ → ∃ z ∈ U ∩ ball (a : ℂ) (ε / 2), g z = v := by
    intro a
    exact exists_stable_local_image hU hf (hKU a.property)
      (hnc a a.property) (half_pos hε)
  choose d hd hstable using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : K => ball (a : ℂ) (ε / 2))
    (fun _ => isOpen_ball) (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, mem_ball_self (half_pos hε)⟩)
  have hsmall : ∃ δ > 0, ∀ a ∈ t, δ < d a := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a t ha ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min δ (d a / 2), lt_min hδ (half_pos (hd a)), ?_⟩
      intro b hbmem
      rcases Finset.mem_insert.mp hbmem with rfl | hbmem
      · exact (min_le_right _ _).trans_lt (half_lt_self (hd b))
      · exact (min_le_left _ _).trans_lt (hb b hbmem)
  obtain ⟨δ, hδ, hsmall⟩ := hsmall
  refine ⟨δ, hδ, ?_⟩
  intro P g hP hg hclose a ha
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht ha)
  have htarget : infEDist (f b) P < ENNReal.ofReal (d b) :=
    (hP b b.property).trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le).mpr
      (hsmall b hb))
  obtain ⟨v, hvP, hv⟩ := infEDist_lt_iff.mp htarget
  have hv' : ‖v - f b‖ < d b := by
    simpa [dist_eq_norm, norm_sub_rev] using edist_lt_ofReal.mp hv
  obtain ⟨z, hz, heq⟩ := hstable b g hg
    (fun w hw => (hclose w hw).trans (hsmall b hb)) v hv'
  refine ⟨z, hz.1, heq ▸ hvP, ?_⟩
  have hzb : dist (b : ℂ) z < ε / 2 := by
    simpa [dist_comm] using mem_ball.mp hz.2
  exact (dist_triangle a b z).trans_lt (by linarith [mem_ball.mp hab])

end FunctionTheory
