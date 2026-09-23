/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.TrappedComponentCovering
import BoundedWanderingDomains.ShrinkingChartDiscs
import FunctionTheory.Conformal.LocalPowerCoordinate
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- A local power coordinate is injective on a connected set mapping into a
simply connected domain that omits its branch value. This constructs just the
local inverse branch needed by the wandering-disc argument. -/
theorem injOn_of_power_coordinate
    {f ψ : ℂ → ℂ} {D W : Set ℂ} {c : ℂ} {d : ℕ}
    (hd : d ≠ 0) (hD : IsPreconnected D) (hW : IsOpen W)
    (hWsc : IsSimplyConnected W) (hc : c ∉ W)
    (hf : ContinuousOn f D) (hψ : ContinuousOn ψ D) (hψi : InjOn ψ D)
    (hm : MapsTo f D W) (he : ∀ x ∈ D, f x = c + ψ x ^ d) : InjOn f D := by
  obtain ⟨g, hg, hgp⟩ := TauCeti.exists_differentiableOn_pow_eq hWsc hW
    (differentiableOn_id.sub_const c) (by
      rintro ⟨w, hw, he⟩
      exact hc ((sub_eq_zero.mp he) ▸ hw)) hd
  have hpow : ∀ w ∈ W, g w ^ d = w - c := fun w hw => hgp hw
  have hg0 : ∀ w ∈ W, g w ≠ 0 := by
    intro w hw hz
    have h := hpow w hw
    rw [hz, zero_pow hd] at h
    exact hc ((sub_eq_zero.mp h.symm) ▸ hw)
  let q : ℂ → ℂ := fun x => ψ x / g (f x)
  have hq : ContinuousOn q D := hψ.div (hg.continuousOn.comp hf hm)
    (fun x hx => hg0 _ (hm hx))
  have hqp : ∀ x ∈ D, q x ^ d = 1 := by
    intro x hx
    dsimp [q]
    rw [div_pow]
    have hp : ψ x ^ d = g (f x) ^ d := by
      rw [hpow _ (hm hx), he x hx]
      ring
    rw [hp, div_self (pow_ne_zero d (hg0 _ (hm hx)))]
  have hfin : {w : ℂ | w ^ d = 1}.Finite := by
    have hp : (Polynomial.X ^ d - Polynomial.C (1 : ℂ)) ≠ 0 := by
      intro hp
      have H := congrArg (fun p : Polynomial ℂ => p.eval 0) hp
      simp [hd] at H
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hp
  intro x hx y hy hxy
  have hqeq := hD.constant_of_mapsTo hfin.isDiscrete hq hqp hx hy
  apply hψi hx hy
  exact (div_left_inj' (hg0 _ (hm hx))).mp (by simpa only [q, hxy] using hqeq)

/-- Local nonconstant holomorphic maps have univalent power coordinates on
an open neighbourhood of each point. -/
theorem exists_univalent_power_neighbourhood {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hn : ¬EventuallyConst f (𝓝 a)) :
    ∃ O : Set ℂ, IsOpen O ∧ a ∈ O ∧ ∃ d : ℕ, d ≠ 0 ∧ ∃ ψ : ℂ → ℂ,
      ContinuousOn ψ O ∧ InjOn ψ O ∧ ∀ x ∈ O, f x = f a + ψ x ^ d := by
  obtain ⟨d, hd, ψ, hψ, _, hψd, he⟩ := FunctionTheory.exists_local_power_coordinate hf
    (fun h => hn (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨f a, h⟩))
  let e := (hψ.hasStrictDerivAt.hasStrictFDerivAt_equiv hψd).toOpenPartialHomeomorph ψ
  obtain ⟨O, hO, ho, ha⟩ := _root_.mem_nhds_iff.mp he
  refine ⟨O ∩ e.source, ho.inter e.open_source,
    ⟨ha, HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _⟩, d, hd.ne', ψ,
    e.continuousOn.mono inter_subset_right, e.injOn.mono inter_subset_right, ?_⟩
  exact fun x hx => hO hx.1

/-- Intrinsic discs are connected, by transport through the inverse Riemann chart. -/
theorem chartDisc_isPreconnected {u : ℂ → ℂ} {U : Set ℂ} {r : ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    (hub : BijOn u U (ball 0 1)) (hr : r < 1) : IsPreconnected (chartDisc u U r) := by
  let p := invFunOn u U
  have hpd : DifferentiableOn ℂ p (ball 0 1) := by
    simpa only [hub.image_eq] using hu.invFunOn hU hub.injOn
  have he : p '' ball 0 r = chartDisc u U r := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 := ball_subset_ball hr.le hw
      exact ⟨invFunOn_mem (hub.surjOn hw1), by
        change u (p w) ∈ ball 0 r
        simpa only [p, invFunOn_eq (hub.surjOn hw1)] using hw⟩
    · intro hx
      exact ⟨u x, hx.2, hub.injOn.leftInvOn_invFunOn hx.1⟩
  rw [← he]
  exact (convex_ball (0 : ℂ) r).isPreconnected.image p
    (hpd.continuousOn.mono (ball_subset_ball hr.le))

/-- Shrinking discs in a compact part of the source eventually admit the
local inverse branches. Only finitely many local branch values occur, and
disjoint successor domains eventually omit all of them. -/
theorem eventually_injOn_shrinking_chart_discs
    {f : ℂ → ℂ} {K : Set ℂ} {U : ℕ → Set ℂ}
    {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {M : ℝ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ a ∈ K, ¬EventuallyConst f (𝓝 a))
    (hU : ∀ n, IsOpen (U n)) (hsc : ∀ n, IsSimplyConnected (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hzK : ∀ n, z n ∈ K)
    (hu0 : ∀ n, u n (z n) = 0)
    (hb : ∀ n x, x ∈ U n → ‖x‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hfc : ∀ n, ContinuousOn f (U n))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn f (chartDisc (u n) (U n) r) := by
  classical
  have hloc : ∀ a : K, ∃ O : Set ℂ, IsOpen O ∧ (a : ℂ) ∈ O ∧
      ∃ d : ℕ, d ≠ 0 ∧ ∃ ψ : ℂ → ℂ, ContinuousOn ψ O ∧ InjOn ψ O ∧
      ∀ x ∈ O, f x = f a + ψ x ^ d :=
    fun a => exists_univalent_power_neighbourhood (hf a a.2) (hn a a.2)
  choose O hOo haO d hd ψ hψ hψi he using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hOo (by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, haO ⟨a, ha⟩⟩)
  let I := {a : K // a ∈ t}
  have hcover : K ⊆ ⋃ a : I, O a.val := by
    intro x hx
    obtain ⟨a, hat, ha⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, ha⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric hK
    (fun a : I => hOo a.val) hcover
  let E : Set ℂ := Set.range (fun a : I => f a.val)
  have hE : E.Finite := Set.finite_range _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_disjoint_finite hdis hE)
  filter_upwards [eventually_ge_atTop N,
    disjoint_bounded_chart_discs_shrink hU hu hub hz hu0 hb hdis hr hr1 hδ]
    with n hnN hshrink
  obtain ⟨a, ha⟩ := hδcover (z n) (hzK n)
  have hDO : chartDisc (u n) (U n) r ⊆ O a.val :=
    fun x hx => ha (hshrink x hx)
  apply injOn_of_power_coordinate (hd a.val)
    (chartDisc_isPreconnected (hU n) (hu n) (hub n) hr1)
    (hU (n + 1)) (hsc (n + 1))
  · intro hx
    exact disjoint_left.mp (hN (n + 1) (by omega)) hx ⟨a, rfl⟩
  · exact (hfc n).mono inter_subset_left
  · exact (hψ a.val).mono hDO
  · exact (hψi a.val).mono hDO
  · exact (hfm n).mono_left inter_subset_left
  · exact fun x hx => he a.val x (hDO hx)

end AreaDeficit
