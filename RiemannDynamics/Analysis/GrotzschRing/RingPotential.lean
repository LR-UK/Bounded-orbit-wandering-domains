/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Potential.PerronEnvelope

/-!
# Boundary regularity of the Perron solution and the harmonic potential of a ring

The Perron envelope is harmonic (`perronEnvelope_harmonicOn`); this file supplies its **boundary
behaviour** and assembles the **harmonic potential of a ring domain**.

A boundary point `ζ` of `U` is *regular* when it carries a **barrier**: a subharmonic function on
`U`, continuous up to the closure, vanishing exactly at `ζ` and strictly negative elsewhere on the
closure. At a regular point where the boundary data `φ` is continuous, the Perron envelope attains
`φ ζ` as a limit from inside `U` (the classical barrier sandwich). When every frontier point is
regular and the frontier splits into two closed pieces `E` (inner) and `F` (outer), the Perron
envelope of the data `0` on `E`, `1` on `F` is the **harmonic potential** `u` of the ring: harmonic
on `U`, continuous up to the closure, `0` on `E` and `1` on `F`.

The potential is the bridge to the conformal modulus and conjugate-modulus reciprocity: its gradient
is the extremal metric of the connecting family, and its boundary flux is the modulus.

## Main definitions

* `IsBarrier β U ζ` — `β` is a barrier for `U` at the boundary point `ζ`;
* `IsRegularBoundary U` — every frontier point of `U` carries a barrier.

## Main statements

* `perronEnvelope_tendsto_of_barrier` — at a barrier point where `φ` is continuous, the Perron
  envelope tends to `φ ζ`;
* `exists_ringPotential` — the harmonic potential of a regular ring domain (`0` on `E`, `1` on `F`).
-/

open MeasureTheory Filter Metric Topology
open scoped Real Topology

namespace RiemannDynamics

/-- A **barrier** for the open set `U` at a frontier point `ζ`: a subharmonic function on `U`,
continuous up to the closure, vanishing at `ζ` and strictly negative everywhere else on the closure.
Its existence makes `ζ` a regular boundary point for the Dirichlet problem. -/
def IsBarrier (β : ℂ → ℝ) (U : Set ℂ) (ζ : ℂ) : Prop :=
  SubharmonicOn β U ∧ ContinuousOn β (closure U) ∧ β ζ = 0 ∧
    ∀ z ∈ closure U, z ≠ ζ → β z < 0

/-- `U` has **regular boundary** when every frontier point carries a barrier. -/
def IsRegularBoundary (U : Set ℂ) : Prop :=
  ∀ ζ ∈ frontier U, ∃ β : ℂ → ℝ, IsBarrier β U ζ

/-- **Boundary attainment of the Perron solution at a barrier point.** If `U` is bounded open with a
barrier at the frontier point `ζ`, the boundary data `φ` is bounded above on the frontier and
continuous at `ζ` within the frontier, and the Perron family is nonempty, then the Perron envelope
converges to `φ ζ` as `z → ζ` from inside `U`. (Classical barrier sandwich: for `ε > 0`, a multiple
of the barrier squeezes the envelope between `φ ζ ± ε` near `ζ`.) -/
theorem perronEnvelope_tendsto_of_barrier {φ : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) {M : ℝ} (hM : 0 ≤ M) (hφ : ∀ ζ ∈ frontier U, φ ζ ≤ M)
    (hne : (perronFamily φ U).Nonempty) {ζ : ℂ} (hζ : ζ ∈ frontier U)
    (hβ : ∃ β : ℂ → ℝ, IsBarrier β U ζ)
    (hφcont : ContinuousWithinAt φ (frontier U) ζ) :
    Tendsto (perronEnvelope φ U) (𝓝[U] ζ) (𝓝 (φ ζ)) := by
  classical
  have _hM : 0 ≤ M := hM
  obtain ⟨β, hβsub, hβcont, hβζ, hβneg⟩ := hβ
  set u : ℂ → ℝ := perronEnvelope φ U with hu
  -- `ζ` lies in the closure of `U`.
  have hζcl : ζ ∈ closure U := frontier_subset_closure hζ
  -- `closure U` is compact.
  have hKcompact : IsCompact (closure U) :=
    isCompact_of_isClosed_isBounded isClosed_closure hUbdd.closure
  -- A subharmonic helper: `a + C • β` is subharmonic for `0 ≤ C` (with `a` constant).
  have hsub_affine : ∀ (a C : ℝ), 0 ≤ C →
      SubharmonicOn (fun z => a + C * β z) U := by
    intro a C _
    obtain ⟨hβc, hβmv⟩ := hβsub
    refine ⟨continuousOn_const.add (continuousOn_const.mul hβc), ?_⟩
    intro c hc r hr hball
    have hsphere : Metric.sphere c r ⊆ U := (Metric.sphere_subset_closedBall).trans hball
    have hβci : CircleIntegrable β c r := (hβc.mono hsphere).circleIntegrable hr.le
    have hCci : CircleIntegrable (fun z => C * β z) c r :=
      ((continuousOn_const.mul hβc).mono hsphere).circleIntegrable hr.le
    have hconstci : CircleIntegrable (fun _ : ℂ => a) c r := circleIntegrable_const a c r
    have havg : Real.circleAverage (fun z => a + C * β z) c r
        = a + C * Real.circleAverage β c r := by
      have heq : (fun z => a + C * β z) = (fun _ => a) + fun z => C * β z := by
        funext z; simp
      rw [heq, Real.circleAverage_add hconstci hCci, Real.circleAverage_const]
      congr 1
      rw [show (fun z => C * β z) = (fun z => C • β z) from funext fun z => by
        simp [smul_eq_mul], Real.circleAverage_fun_smul, smul_eq_mul]
    rw [havg]
    have := hβmv c hc r hr hball
    nlinarith [mul_le_mul_of_nonneg_left this (by assumption : (0:ℝ) ≤ C)]
  -- The sum of two subharmonic functions is subharmonic (no global lemma; proved inline).
  have hsub_add : ∀ (f g : ℂ → ℝ), SubharmonicOn f U → SubharmonicOn g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g ⟨hfc, hfmv⟩ ⟨hgc, hgmv⟩
    refine ⟨hfc.add hgc, ?_⟩
    intro c hc r hr hball
    have hsphere : Metric.sphere c r ⊆ U := (Metric.sphere_subset_closedBall).trans hball
    have hfci : CircleIntegrable f c r := (hfc.mono hsphere).circleIntegrable hr.le
    have hgci : CircleIntegrable g c r := (hgc.mono hsphere).circleIntegrable hr.le
    have heq : (fun z => f z + g z) = f + g := rfl
    rw [heq, Real.circleAverage_add hfci hgci, Pi.add_apply]
    have h1 := hfmv c hc r hr hball
    have h2 := hgmv c hc r hr hball
    linarith
  -- `β z → 0` as `z → ζ` within `U`.
  have hβtend : Tendsto β (𝓝[U] ζ) (𝓝 (0 : ℝ)) := by
    have : ContinuousWithinAt β (closure U) ζ := hβcont ζ hζcl
    have h2 : Tendsto β (𝓝[U] ζ) (𝓝 (β ζ)) :=
      (this.mono (subset_closure)).tendsto
    rwa [hβζ] at h2
  -- A lower bound for `φ` on the frontier, from a Perron-family member (continuous on the compact
  -- closure, hence bounded below; dominated by `φ` on the frontier).
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ξ ∈ frontier U, -B ≤ φ ξ := by
    obtain ⟨v₀, hv₀sub, hv₀cont, hv₀front⟩ := hne
    obtain ⟨B, hBbd⟩ := hKcompact.exists_bound_of_continuousOn hv₀cont
    refine ⟨B, fun ξ hξ => ?_⟩
    have h1 : -B ≤ v₀ ξ := by
      have := hBbd ξ (frontier_subset_closure hξ)
      rw [Real.norm_eq_abs, abs_le] at this; exact this.1
    exact le_trans h1 (hv₀front ξ hξ)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- ===== LOWER BOUND: build a barrier-modified subsolution `w ≤ u` =====
  -- Choose `r > 0` so `|φ ξ - φ ζ| < ε/2` on the near frontier.
  obtain ⟨r, hr, hrφ⟩ : ∃ r > 0, ∀ ξ ∈ frontier U, dist ξ ζ < r →
      φ ζ - ε / 2 < φ ξ ∧ φ ξ < φ ζ + ε / 2 := by
    rw [Metric.continuousWithinAt_iff] at hφcont
    obtain ⟨r, hr, hrφ⟩ := hφcont (ε / 2) (by linarith)
    refine ⟨r, hr, fun ξ hξ hdist => ?_⟩
    have := hrφ hξ hdist
    rw [Real.dist_eq, abs_lt] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- The far compact set where `β` is strictly negative.
  set K : Set ℂ := closure U ∩ {z | r ≤ dist z ζ} with hK
  have hKcl : IsClosed K := isClosed_closure.inter (isClosed_le continuous_const (by fun_prop))
  have hKcomp : IsCompact K := hKcompact.inter_right (isClosed_le continuous_const (by fun_prop))
  -- A constant `C ≥ 0` working for both bounds on the far frontier `K`: the lower subsolution
  -- stays `≤ -B ≤ φ`, the upper supersolution stays `≥ M ≥ φ`. We find `m > 0` with `β ≤ -m`.
  obtain ⟨C, hC0, hCfar, hCfar'⟩ : ∃ C : ℝ, 0 ≤ C ∧ (∀ ξ ∈ K, (φ ζ - ε / 2) + C * β ξ ≤ -B)
      ∧ ∀ ξ ∈ K, M ≤ (φ ζ + ε / 2) - C * β ξ := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, le_refl _, fun ξ hξ => absurd (hKe ▸ hξ : ξ ∈ (∅ : Set ℂ)) (by simp),
        fun ξ hξ => absurd (hKe ▸ hξ : ξ ∈ (∅ : Set ℂ)) (by simp)⟩
    · -- `β` attains a max `-m < 0` on `K`.
      have hβKcont : ContinuousOn β K := hβcont.mono Set.inter_subset_left
      obtain ⟨x₀, hx₀K, hx₀max⟩ := hKcomp.exists_isMaxOn hKne hβKcont
      have hx₀ne : x₀ ≠ ζ := by
        intro h; have : r ≤ dist x₀ ζ := hx₀K.2; rw [h, dist_self] at this; linarith
      set m : ℝ := -β x₀ with hm
      have hm0 : 0 < m := by
        have := hβneg x₀ hx₀K.1 hx₀ne; simp only [hm]; linarith
      set C : ℝ := max 0 (max (((φ ζ - ε / 2) + B) / m) ((M - (φ ζ + ε / 2)) / m)) with hCdef
      have hC0 : 0 ≤ C := le_max_left _ _
      have hCge1 : ((φ ζ - ε / 2) + B) / m ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
      have hCge2 : (M - (φ ζ + ε / 2)) / m ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
      have hbothfar : ∀ ξ ∈ K, β ξ ≤ -m := fun ξ hξ => by simpa [hm] using hx₀max hξ
      have hCm1 : (φ ζ - ε / 2) + B ≤ C * m := by
        have hstep : ((φ ζ - ε / 2) + B) / m * m ≤ C * m :=
          mul_le_mul_of_nonneg_right hCge1 hm0.le
        rwa [div_mul_cancel₀ _ hm0.ne'] at hstep
      have hCm2 : M - (φ ζ + ε / 2) ≤ C * m := by
        have hstep : (M - (φ ζ + ε / 2)) / m * m ≤ C * m :=
          mul_le_mul_of_nonneg_right hCge2 hm0.le
        rwa [div_mul_cancel₀ _ hm0.ne'] at hstep
      refine ⟨C, hC0, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
      · have hmul : C * β ξ ≤ C * (-m) := mul_le_mul_of_nonneg_left (hbothfar ξ hξ) hC0
        nlinarith [hmul, hCm1]
      · have hmul : C * β ξ ≤ C * (-m) := mul_le_mul_of_nonneg_left (hbothfar ξ hξ) hC0
        nlinarith [hmul, hCm2]
  -- The candidate subsolution `w := (φ ζ - ε/2) + C • β` is in the Perron family.
  have hwmem : (fun z => (φ ζ - ε / 2) + C * β z) ∈ perronFamily φ U := by
    refine ⟨hsub_affine (φ ζ - ε / 2) C hC0, ?_, ?_⟩
    · -- continuous on `closure U`.
      exact continuousOn_const.add (continuousOn_const.mul hβcont)
    · -- `w ≤ φ` on the frontier.
      intro ξ hξ
      have hβle0 : β ξ ≤ 0 := le_of_lt_or_eq (by
        rcases eq_or_ne ξ ζ with rfl | hne
        · right; exact hβζ
        · left; exact hβneg ξ (frontier_subset_closure hξ) hne)
      by_cases hξfar : r ≤ dist ξ ζ
      · -- far frontier: `ξ ∈ K`, so `w ξ ≤ -B ≤ φ ξ`.
        have hξK : ξ ∈ K := ⟨frontier_subset_closure hξ, hξfar⟩
        exact le_trans (hCfar ξ hξK) (hB ξ hξ)
      · -- near frontier: `dist ξ ζ < r`, so `φ ξ > φ ζ - ε/2 ≥ w ξ` (since `Cβ ≤ 0`).
        rw [not_le] at hξfar
        have h1 : φ ζ - ε / 2 < φ ξ := (hrφ ξ hξ hξfar).1
        have h2 : C * β ξ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC0 hβle0
        linarith
  -- LOWER BOUND on `u`: `w z ≤ u z` for `z ∈ U`.
  have hlower : ∀ z ∈ U, (φ ζ - ε / 2) + C * β z ≤ u z := fun z hz =>
    subharmonicOn_mem_perronFamily_le_perronEnvelope hUopen hUbdd hφ hwmem hz
  -- ===== UPPER BOUND: every member is `≤ W := (φ ζ + ε/2) - C • β` on `U` =====
  have hupper : ∀ z ∈ U, u z ≤ (φ ζ + ε / 2) - C * β z := by
    intro z hz
    -- Each member `v` satisfies `v z ≤ W z`, so the supremum does too.
    have hmemle : ∀ v ∈ perronFamily φ U, v z ≤ (φ ζ + ε / 2) - C * β z := by
      intro v ⟨hvsub, hvcont, hvfront⟩
      -- `D := v + C·β - (φζ+ε/2)` is subharmonic and `≤ 0` on the frontier, hence `≤ 0` on `U`.
      set D : ℂ → ℝ := fun y => v y + (-(φ ζ + ε / 2) + C * β y) with hD
      have hDsub : SubharmonicOn D U :=
        hsub_add v (fun y => -(φ ζ + ε / 2) + C * β y) hvsub (hsub_affine _ C hC0)
      have hDcont : ContinuousOn D (closure U) :=
        hvcont.add (continuousOn_const.add (continuousOn_const.mul hβcont))
      have hDfront : ∀ ξ ∈ frontier U, D ξ ≤ 0 := by
        intro ξ hξ
        have hβle0 : β ξ ≤ 0 := le_of_lt_or_eq (by
          rcases eq_or_ne ξ ζ with rfl | hne
          · right; exact hβζ
          · left; exact hβneg ξ (frontier_subset_closure hξ) hne)
        by_cases hξfar : r ≤ dist ξ ζ
        · -- far frontier: `v ξ ≤ φ ξ ≤ M ≤ (φζ+ε/2) - Cβξ`.
          have hξK : ξ ∈ K := ⟨frontier_subset_closure hξ, hξfar⟩
          have hvφ : v ξ ≤ φ ξ := hvfront ξ hξ
          have hφM : φ ξ ≤ M := hφ ξ hξ
          have := hCfar' ξ hξK
          simp only [hD]; linarith
        · -- near frontier: `v ξ ≤ φ ξ < φζ+ε/2 ≤ (φζ+ε/2) - Cβξ` (since `-Cβξ ≥ 0`).
          rw [not_le] at hξfar
          have hvφ : v ξ ≤ φ ξ := hvfront ξ hξ
          have h1 : φ ξ < φ ζ + ε / 2 := (hrφ ξ hξ hξfar).2
          have h2 : 0 ≤ -(C * β ξ) := by
            have : C * β ξ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC0 hβle0
            linarith
          simp only [hD]; linarith
      have hDle := hDsub.le_of_frontier_le hUopen hUbdd hDcont hDfront z hz
      simp only [hD] at hDle; linarith
    -- The supremum over the (nonempty) value set is `≤ W z`.
    rw [hu, perronEnvelope]
    have hsne : ((fun v => v z) '' perronFamily φ U).Nonempty := by
      obtain ⟨v, hv⟩ := hne; exact ⟨v z, v, hv, rfl⟩
    refine csSup_le hsne ?_
    rintro x ⟨v, hv, rfl⟩
    exact hmemle v hv
  -- ===== CHOOSE δ and combine =====
  -- A radius making `|C·β z| < ε/2` near `ζ` within `U`.
  rw [Metric.tendsto_nhdsWithin_nhds] at hβtend
  obtain ⟨δ, hδ, hδβ⟩ := hβtend ((ε / 2) / (|C| + 1)) (by positivity)
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  have hβz : |C * β z| < ε / 2 := by
    have h1 := hδβ hz hdist
    rw [Real.dist_eq, sub_zero] at h1
    have hbound : |C * β z| ≤ |C| * ((ε / 2) / (|C| + 1)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
    have hlt : |C| * ((ε / 2) / (|C| + 1)) < ε / 2 := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      have : |C| * (ε / 2) < (ε / 2) * (|C| + 1) := by nlinarith [abs_nonneg C, hε]
      linarith
    linarith
  -- `φ ζ - ε < u z < φ ζ + ε`.
  have hL := hlower z hz
  have hU := hupper z hz
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hβz
  constructor
  · linarith [hβz.1, hβz.2, hL]
  · linarith [hβz.1, hβz.2, hU]

/-- **The harmonic potential of a regular ring domain.** Let `U` be a bounded open set with regular
boundary whose frontier is the disjoint union of two closed sets `E` (inner) and `F` (outer). Then
there is a harmonic function `u` on `U`, continuous up to the closure, equal to `0` on `E` and `1`
on `F`, with `0 ≤ u ≤ 1`. It is the Perron solution of the boundary data that is `0` on `E` and `1`
on `F`. -/
theorem exists_ringPotential {U E F : Set ℂ} (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) (hUreg : IsRegularBoundary U)
    (hfrontier : frontier U = E ∪ F) (hEF : Disjoint E F)
    (hEcl : IsClosed E) (hFcl : IsClosed F) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ContinuousOn u (closure U) ∧
      (∀ z ∈ E, u z = 0) ∧ (∀ z ∈ F, u z = 1) ∧ (∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1) := by
  classical
  -- Boundary data: `1` on `F`, `0` elsewhere.
  set φ : ℂ → ℝ := fun z => if z ∈ F then (1 : ℝ) else 0 with hφdef
  -- `φ ≤ 1` on the frontier (indeed everywhere).
  have hφM : ∀ ζ ∈ frontier U, φ ζ ≤ 1 := by
    intro ζ _; simp only [hφdef]; split <;> norm_num
  -- The constant `0` lies in the Perron family.
  have h0mem : (fun _ : ℂ => (0 : ℝ)) ∈ perronFamily φ U := by
    refine ⟨?_, continuousOn_const, ?_⟩
    · exact HarmonicOnNhd.subharmonicOn (InnerProductSpace.harmonicOnNhd_const (0 : ℝ) (s := U))
    · intro ζ _; simp only [hφdef]; split <;> norm_num
  -- The Perron family is nonempty.
  have hne : (perronFamily φ U).Nonempty := ⟨fun _ => 0, h0mem⟩
  -- `φ` is continuous within the frontier at every frontier point (locally constant there).
  have hφcont : ∀ ζ ∈ frontier U, ContinuousWithinAt φ (frontier U) ζ := by
    intro ζ hζ
    -- An open neighbourhood `V ∋ ζ` on which `φ` is constant on the frontier.
    have hEF' : Disjoint E F := hEF
    obtain ⟨V, hVopen, hζV, hVconst⟩ :
        ∃ V : Set ℂ, IsOpen V ∧ ζ ∈ V ∧ ∀ y ∈ V, y ∈ frontier U → φ y = φ ζ := by
      have hζEF : ζ ∈ E ∪ F := hfrontier ▸ hζ
      rcases hζEF with hζE | hζF
      · -- `ζ ∈ E`: away from `F` (closed), `φ = 0 = φ ζ` on the frontier.
        have hζnotF : ζ ∉ F := fun h => (hEF.le_bot ⟨hζE, h⟩)
        refine ⟨Fᶜ, hFcl.isOpen_compl, hζnotF, fun y hyV hyfront => ?_⟩
        simp only [hφdef, ite_eq_right hyV, ite_eq_right hζnotF]
      · -- `ζ ∈ F`: away from `E` (closed), `φ = 1 = φ ζ` on the frontier.
        have hζnotE : ζ ∉ E := fun h => (hEF.le_bot ⟨h, hζF⟩)
        refine ⟨Eᶜ, hEcl.isOpen_compl, hζnotE, fun y hyV hyfront => ?_⟩
        have hyEF : y ∈ E ∪ F := hfrontier ▸ hyfront
        have hyF : y ∈ F := hyEF.resolve_left hyV
        simp only [hφdef, ite_eq_left hyF, ite_eq_left hζF]
    have hee : φ =ᶠ[𝓝[frontier U] ζ] (fun _ => φ ζ) := by
      have hmem : frontier U ∩ V ∈ 𝓝[frontier U] ζ :=
        inter_mem_nhdsWithin _ (hVopen.mem_nhds hζV)
      filter_upwards [hmem] with y hy using hVconst y hy.2 hy.1
    exact (continuousWithinAt_const).congr_of_eventuallyEq hee rfl
  -- Perron's theorem: the envelope is harmonic on `U`.
  have hharm : InnerProductSpace.HarmonicOnNhd (perronEnvelope φ U) U :=
    perronEnvelope_harmonicOn hUopen hUbdd hφM hne
  -- Bounds: `0 ≤ perronEnvelope ≤ 1` on `U`.
  have hub : ∀ z ∈ U, perronEnvelope φ U z ≤ 1 := fun z hz =>
    perronEnvelope_le_sSup hUopen hUbdd (by norm_num) hφM hz
  have hlb : ∀ z ∈ U, 0 ≤ perronEnvelope φ U z := by
    intro z hz
    -- the constant `0` is a member, dominated by the envelope.
    have := subharmonicOn_mem_perronFamily_le_perronEnvelope hUopen hUbdd hφM h0mem hz
    simpa using this
  -- Boundary attainment at every frontier point.
  have htend : ∀ ζ ∈ frontier U,
      Tendsto (perronEnvelope φ U) (𝓝[U] ζ) (𝓝 (φ ζ)) := by
    intro ζ hζ
    exact perronEnvelope_tendsto_of_barrier hUopen hUbdd (by norm_num : (0:ℝ) ≤ 1) hφM hne hζ
      (hUreg ζ hζ) (hφcont ζ hζ)
  -- The extended potential, equal to the boundary data off `U`.
  set u : ℂ → ℝ := fun z => if z ∈ U then perronEnvelope φ U z else φ z with hudef
  -- `u` agrees with the Perron envelope on the open set `U` (harmonicity transfers).
  have huU : ∀ z ∈ U, u z = perronEnvelope φ U z := fun z hz => by
    simp only [hudef, ite_eq_left hz]
  have huoff : ∀ z, z ∉ U → u z = φ z := fun z hz => by simp only [hudef, ite_eq_right hz]
  -- `U` and `frontier U` are disjoint.
  have hUfront : ∀ z ∈ frontier U, z ∉ U := by
    intro z hz hzU
    exact (Set.eq_empty_iff_forall_notMem.1 hUopen.inter_frontier_eq) z ⟨hzU, hz⟩
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · -- Harmonic on `U`: `u` agrees with the envelope on the open `U`.
    intro w hw
    have heqnhd : u =ᶠ[𝓝 w] perronEnvelope φ U := by
      filter_upwards [hUopen.mem_nhds hw] with y hy using huU y hy
    exact (InnerProductSpace.harmonicAt_congr_nhds heqnhd).2 (hharm w hw)
  · -- Continuous on `closure U`.
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hxU | hxfront
    · -- interior point: `u` agrees with the (continuous) envelope on a nbhd.
      have hcontAt : ContinuousAt (perronEnvelope φ U) x :=
        (hharm x hxU).1.continuousAt
      have heqnhd : u =ᶠ[𝓝 x] perronEnvelope φ U := by
        filter_upwards [hUopen.mem_nhds hxU] with y hy using huU y hy
      exact ((hcontAt.congr heqnhd.symm).continuousWithinAt).mono subset_closure
    · -- boundary point: split `closure U = U ∪ frontier U`.
      have huxφ : u x = φ x := huoff x (hUfront x hxfront)
      -- continuity within `U`: agrees with the envelope, which tends to `φ x`.
      have hwithinU : ContinuousWithinAt u U x := by
        rw [ContinuousWithinAt, huxφ]
        refine (htend x hxfront).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy using (huU y hy).symm
      -- continuity within `frontier U`: `u = φ` there, and `φ` is continuous within frontier.
      have hwithinF : ContinuousWithinAt u (frontier U) x := by
        have heeF : u =ᶠ[𝓝[frontier U] x] φ := by
          filter_upwards [self_mem_nhdsWithin] with y hy using huoff y (hUfront y hy)
        exact (hφcont x hxfront).congr_of_eventuallyEq heeF huxφ
      have hunion : ContinuousWithinAt u (U ∪ frontier U) x := hwithinU.union hwithinF
      exact hunion.mono (by rw [← closure_eq_self_union_frontier])
  · -- `u = 0` on `E`.
    intro z hzE
    have hzfront : z ∈ frontier U := hfrontier ▸ Or.inl hzE
    have hznotF : z ∉ F := fun h => (hEF.le_bot ⟨hzE, h⟩)
    rw [huoff z (hUfront z hzfront)]; simp only [hφdef, ite_eq_right hznotF]
  · -- `u = 1` on `F`.
    intro z hzF
    have hzfront : z ∈ frontier U := hfrontier ▸ Or.inr hzF
    rw [huoff z (hUfront z hzfront)]; simp only [hφdef, ite_eq_left hzF]
  · -- `0 ≤ u ≤ 1` on `U`.
    intro z hz
    rw [huU z hz]
    exact ⟨hlb z hz, hub z hz⟩

end RiemannDynamics
