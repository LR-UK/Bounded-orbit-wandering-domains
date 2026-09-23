/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Potential.Subharmonic
import RiemannDynamics.Analysis.Potential.HarmonicHarnack

/-!
# Perron's method: the harmonic envelope

For boundary data `φ` on a bounded open set `U`, the **Perron family** consists of the continuous
subharmonic functions on `U`, continuous up to the closure, that are dominated by `φ` on the
frontier. The **Perron envelope** is their pointwise supremum. Perron's theorem: the envelope is
harmonic on `U`. (Its boundary behaviour — that it attains `φ` continuously at regular boundary
points, via barriers — is treated separately; the harmonicity is the part needed to construct the
harmonic potential of a ring domain.)

The envelope is harmonic because the family is closed under taking pointwise maxima
(`subharmonicOn_max`) and under Poisson modification on a disk (`SubharmonicOn.poissonModify`),
which does not decrease a member and makes it harmonic on the disk; a monotone Poisson-modified
maximizing sequence converges (by the monotone convergence of the Poisson representation) to a
harmonic function agreeing with the envelope.

## Main definitions

* `perronFamily φ U` — continuous subharmonic functions on `U`, continuous up to `closure U`,
  dominated by `φ` on `frontier U`;
* `perronEnvelope φ U` — the pointwise supremum of the Perron family.

## Main statements

* `subharmonicOn_mem_perronFamily_le_perronEnvelope` — every family member is `≤` the envelope;
* `perronEnvelope_le_sSup` — the envelope is bounded by the frontier supremum of `φ`;
* `perronEnvelope_harmonicOn` — **Perron's theorem**: the envelope is harmonic on `U`.
-/

open MeasureTheory Filter Metric Topology
open scoped Real Topology

namespace RiemannDynamics

/-- The **Perron family** for boundary data `φ` on `U`: the continuous subharmonic functions on `U`
that extend continuously to `closure U` and are dominated by `φ` on the frontier. -/
def perronFamily (φ : ℂ → ℝ) (U : Set ℂ) : Set (ℂ → ℝ) :=
  {v | SubharmonicOn v U ∧ ContinuousOn v (closure U) ∧ ∀ ζ ∈ frontier U, v ζ ≤ φ ζ}

/-- The **Perron envelope** of boundary data `φ` on `U`: the pointwise supremum over the Perron
family of the values at `z`. On a bounded `U` with `φ` bounded above on the frontier, and a nonempty
family, this supremum is finite and defines a harmonic function on `U`. -/
noncomputable def perronEnvelope (φ : ℂ → ℝ) (U : Set ℂ) (z : ℂ) : ℝ :=
  sSup ((fun v => v z) '' perronFamily φ U)

/-- **Every Perron-family member is dominated by the envelope.** Immediate from the definition of
the supremum, provided the value set is bounded above (supplied by the maximum principle through the
`perronEnvelope_le_sSup` hypotheses). -/
theorem subharmonicOn_mem_perronFamily_le_perronEnvelope {φ : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U) {M : ℝ} (hφ : ∀ ζ ∈ frontier U, φ ζ ≤ M)
    {v : ℂ → ℝ} (hv : v ∈ perronFamily φ U) {z : ℂ} (hz : z ∈ U) :
    v z ≤ perronEnvelope φ U z := by
  -- The value set is bounded above by `M`: every member, dominated by `φ ≤ M` on the frontier,
  -- is `≤ M` throughout `U` by the maximum principle.
  set S : Set ℝ := (fun w => w z) '' perronFamily φ U with hS
  have hUB : ∀ x ∈ S, x ≤ M := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨hwsub, hwc, hwfront⟩ := hw
    exact hwsub.le_of_frontier_le hUopen hUbdd hwc
      (fun ζ hζ => le_trans (hwfront ζ hζ) (hφ ζ hζ)) z hz
  have hbdd : BddAbove S := ⟨M, fun x hx => hUB x hx⟩
  have hmem : v z ∈ S := ⟨v, hv, rfl⟩
  exact le_csSup hbdd hmem

/-- **The Perron envelope is bounded by the frontier bound of `φ`.** Each family member satisfies
the maximum principle (`SubharmonicOn.le_of_frontier_le`): dominated by `φ ≤ M` on the frontier, it
is `≤ M` throughout `U`; hence so is the supremum. -/
theorem perronEnvelope_le_sSup {φ : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) {M : ℝ} (hM : 0 ≤ M) (hφ : ∀ ζ ∈ frontier U, φ ζ ≤ M)
    {z : ℂ} (hz : z ∈ U) : perronEnvelope φ U z ≤ M := by
  -- Every member of the value set is `≤ M` by the maximum principle.
  have hUB : ∀ x ∈ (fun w => w z) '' perronFamily φ U, x ≤ M := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨hwsub, hwc, hwfront⟩ := hw
    exact hwsub.le_of_frontier_le hUopen hUbdd hwc
      (fun ζ hζ => le_trans (hwfront ζ hζ) (hφ ζ hζ)) z hz
  rcases (((fun w => w z) '' perronFamily φ U)).eq_empty_or_nonempty with hempty | hne
  · -- Empty value set: `perronEnvelope = sSup ∅ = 0 ≤ M`.
    rw [perronEnvelope, hempty, Real.sSup_empty]; exact hM
  · exact csSup_le hne hUB

/-- **Perron's theorem: the envelope is harmonic.** For a bounded open `U`, boundary data `φ`
bounded above on the frontier, and a nonempty Perron family, the Perron envelope
`perronEnvelope φ U` is harmonic on `U`. The proof modifies a maximizing sequence by
`SubharmonicOn.poissonModify` on a disk
about each point, obtaining an increasing sequence of harmonic functions whose monotone Poisson
limit is harmonic and equals the envelope on the disk. -/
theorem perronEnvelope_harmonicOn {φ : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) {M : ℝ} (hφ : ∀ ζ ∈ frontier U, φ ζ ≤ M)
    (hne : (perronFamily φ U).Nonempty) :
    InnerProductSpace.HarmonicOnNhd (perronEnvelope φ U) U := by
  classical
  set u : ℂ → ℝ := perronEnvelope φ U with hu
  -- Every family member is dominated by the envelope on `U`.
  have hmem_le : ∀ v ∈ perronFamily φ U, ∀ z ∈ U, v z ≤ u z := by
    intro v hv z hz
    exact subharmonicOn_mem_perronFamily_le_perronEnvelope hUopen hUbdd hφ hv hz
  -- The envelope is bounded above by `max M 0` on `U` (so the value sets are bdd above).
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hφ0 : ∀ ζ ∈ frontier U, φ ζ ≤ max M 0 :=
    fun ζ hζ => le_trans (hφ ζ hζ) (le_max_left _ _)
  have hu_le : ∀ z ∈ U, u z ≤ max M 0 := fun z hz =>
    perronEnvelope_le_sSup hUopen hUbdd hM0 hφ0 hz
  -- The running-max operator on a sequence of functions.
  set rmax : (ℕ → ℂ → ℝ) → ℕ → ℂ → ℝ :=
    fun g => fun k => Nat.rec (g 0) (fun n acc => fun z => max (acc z) (g (n + 1) z)) k with hrmax
  -- The running max of family members is a family member, monotone, and `≥` each `g k`.
  have hrmax_mem : ∀ (g : ℕ → ℂ → ℝ), (∀ n, g n ∈ perronFamily φ U) →
      ∀ k, rmax g k ∈ perronFamily φ U := by
    intro g hg k
    induction k with
    | zero => exact hg 0
    | succ n ih =>
      obtain ⟨hs1, hc1, hf1⟩ := ih
      obtain ⟨hs2, hc2, hf2⟩ := hg (n + 1)
      refine ⟨subharmonicOn_max hs1 hs2, fun x hx => (hc1 x hx).max (hc2 x hx), ?_⟩
      intro ζ hζ; exact max_le (hf1 ζ hζ) (hf2 ζ hζ)
  have hrmax_ge : ∀ (g : ℕ → ℂ → ℝ) (k : ℕ) (z : ℂ), g k z ≤ rmax g k z := by
    intro g k z
    cases k with
    | zero => simp [hrmax]
    | succ n => exact le_max_right _ _
  have hrmax_mono : ∀ (g : ℕ → ℂ → ℝ) (z : ℂ), Monotone (fun k => rmax g k z) := by
    intro g z
    apply monotone_nat_of_le_succ
    intro n; exact le_max_left _ _
  -- The running max is monotone in the data `g` (pointwise everywhere).
  have hrmax_data_mono : ∀ (g₁ g₂ : ℕ → ℂ → ℝ), (∀ n z, g₁ n z ≤ g₂ n z) →
      ∀ k z, rmax g₁ k z ≤ rmax g₂ k z := by
    intro g₁ g₂ hle k z
    induction k with
    | zero => exact hle 0 z
    | succ n ih => exact max_le_max ih (hle (n + 1) z)
  -- Poisson modification on a disk inside `U` keeps a family member in the family.
  have hpmod_mem : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall w ρ ⊆ U →
      ∀ p, p ∈ perronFamily φ U → poissonModify p w ρ ∈ perronFamily φ U := by
    intro w ρ hρ hball p hp
    obtain ⟨hsub, hcont, hfront⟩ := hp
    refine ⟨(hsub.poissonModify hρ hball), ?_, ?_⟩
    · -- continuity on `closure U`. Cover `closure U` by `closedBall w ρ` and `(ball w ρ)ᶜ`:
      -- on the closed disk `poissonModify` is continuous (Poisson integral + boundary matching),
      -- off the open disk it equals the continuous `p`.
      have hsph : Metric.sphere w ρ ⊆ U := (Metric.sphere_subset_closedBall).trans hball
      have hfsph : ContinuousOn p (Metric.sphere w ρ) := hcont.mono (hsph.trans subset_closure)
      have hPI : ContinuousOn (poissonIntegral p w ρ) (Metric.ball w ρ) :=
        (poissonIntegral_harmonicOn p w hρ hfsph).continuousOn
      have hoff : ∀ z, z ∉ Metric.ball w ρ → poissonModify p w ρ z = p z := by
        intro z hz; simp only [poissonModify, ite_eq_right hz]
      -- continuity on the closed disk
      have hpm_cb : ContinuousOn (poissonModify p w ρ) (Metric.closedBall w ρ) := by
        have hsplit : Metric.closedBall w ρ = Metric.ball w ρ ∪ Metric.sphere w ρ :=
          Metric.ball_union_sphere.symm
        intro ζ hζ
        rw [Metric.mem_closedBall] at hζ
        rcases lt_or_eq_of_le hζ with hlt | heq
        · have hζball : ζ ∈ Metric.ball w ρ := Metric.mem_ball.2 hlt
          have heqf : poissonModify p w ρ =ᶠ[𝓝 ζ] poissonIntegral p w ρ := by
            filter_upwards [Metric.isOpen_ball.mem_nhds hζball] with z hz
            simp only [poissonModify, ite_eq_left hz]
          exact (((hPI ζ hζball).continuousAt
            (Metric.isOpen_ball.mem_nhds hζball)).congr heqf.symm).continuousWithinAt
        · have hζsphere : ζ ∈ Metric.sphere w ρ := Metric.mem_sphere.2 heq
          have hnb : ζ ∉ Metric.ball w ρ := by rw [Metric.mem_ball, heq]; exact lt_irrefl _
          have hPζ : poissonModify p w ρ ζ = p ζ := hoff ζ hnb
          rw [hsplit]
          apply ContinuousWithinAt.union
          · have htend : Tendsto (poissonIntegral p w ρ)
                (𝓝[Metric.ball w ρ] ζ) (𝓝 (p ζ)) :=
              poissonIntegral_tendsto_boundary p w hρ hfsph hζsphere
            have heqb : poissonModify p w ρ
                =ᶠ[𝓝[Metric.ball w ρ] ζ] poissonIntegral p w ρ := by
              filter_upwards [self_mem_nhdsWithin] with z hz
              simp only [poissonModify, ite_eq_left hz]
            rw [ContinuousWithinAt, hPζ]; exact htend.congr' heqb.symm
          · apply (hfsph ζ hζsphere).congr (fun z hz => ?_) hPζ
            have : z ∉ Metric.ball w ρ := by
              rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; exact lt_irrefl _
            simp only [poissonModify, ite_eq_right this]
      -- continuity off the open disk, where `poissonModify = p`
      have hpm_offcl : ContinuousOn (poissonModify p w ρ)
          (closure U ∩ (Metric.ball w ρ)ᶜ) := by
        apply (hcont.mono Set.inter_subset_left).congr
        intro z hz; exact hoff z hz.2
      -- combine the two on the cover `closedBall w ρ ∪ (closure U ∩ (ball)ᶜ)`
      have hcover_cont : ContinuousOn (poissonModify p w ρ)
          (Metric.closedBall w ρ ∪ (closure U ∩ (Metric.ball w ρ)ᶜ)) := by
        intro x hx
        apply ContinuousWithinAt.union
        · by_cases hxcb : x ∈ Metric.closedBall w ρ
          · exact hpm_cb x hxcb
          · have hbot : 𝓝[Metric.closedBall w ρ] x = ⊥ := by
              rw [nhdsWithin, inf_principal_eq_bot]
              exact (isClosed_closedBall (x := w) (ε := ρ)).isOpen_compl.mem_nhds hxcb
            rw [ContinuousWithinAt, hbot]; exact tendsto_bot
        · by_cases hxb : x ∈ Metric.ball w ρ
          · have hbot : 𝓝[closure U ∩ (Metric.ball w ρ)ᶜ] x = ⊥ := by
              rw [nhdsWithin, inf_principal_eq_bot]
              apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxb)
              intro y hy; simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and, not_not]
              intro _; exact hy
            rw [ContinuousWithinAt, hbot]; exact tendsto_bot
          · refine hpm_offcl x ?_
            rcases hx with h | h
            · exact ⟨subset_closure (hball h), hxb⟩
            · exact h
      have hcover : closure U ⊆
          Metric.closedBall w ρ ∪ (closure U ∩ (Metric.ball w ρ)ᶜ) := by
        intro y hy
        by_cases hyb : y ∈ Metric.ball w ρ
        · exact Or.inl (Metric.ball_subset_closedBall hyb)
        · exact Or.inr ⟨hy, hyb⟩
      change ContinuousOn (poissonModify p w ρ) (closure U)
      exact hcover_cont.mono hcover
    · -- frontier condition: `frontier U ∩ ball w ρ = ∅`, so `poissonModify = p ≤ φ`.
      intro ζ hζ
      have hζU : ζ ∉ Metric.ball w ρ := by
        intro hζb
        have hζU' : ζ ∈ U := hball (Metric.ball_subset_closedBall hζb)
        have : ζ ∈ U ∩ frontier U := ⟨hζU', hζ⟩
        rw [hUopen.inter_frontier_eq] at this; exact this
      change poissonModify p w ρ ζ ≤ φ ζ
      rw [show poissonModify p w ρ ζ = p ζ from by simp only [poissonModify, ite_eq_right hζU]]
      exact hfront ζ hζ
  -- Poisson integral / modification is monotone in the data on the disk.
  have hpmod_data_mono : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall w ρ ⊆ U →
      ∀ (p q : ℂ → ℝ), ContinuousOn p (closure U) → ContinuousOn q (closure U) →
      (∀ z ∈ Metric.sphere w ρ, p z ≤ q z) →
      ∀ z ∈ Metric.ball w ρ, poissonModify p w ρ z ≤ poissonModify q w ρ z := by
    intro w ρ hρ hball p q hpc hqc hpq z hz
    have hsph : Metric.sphere w ρ ⊆ U := (Metric.sphere_subset_closedBall).trans hball
    have hpsph : ContinuousOn p (Metric.sphere w ρ) := hpc.mono (hsph.trans subset_closure)
    have hqsph : ContinuousOn q (Metric.sphere w ρ) := hqc.mono (hsph.trans subset_closure)
    simp only [poissonModify, ite_eq_left hz, poissonIntegral]
    have hzlt : ‖z - w‖ < ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hz
    have hkcont : ContinuousOn (fun s => poissonKernel w z s) (Metric.sphere w ρ) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      apply Complex.continuous_re.comp_continuousOn
      rw [herglotzRieszKernel_fun_def]
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro s hs
      have hsn : ‖s - w‖ = ρ := by rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
      intro hcontra
      have : s - w = z - w := by linear_combination (norm := ring_nf) hcontra
      rw [this] at hsn; rw [hsn] at hzlt; linarith
    have hci_p : CircleIntegrable (fun s => poissonKernel w z s * p s) w ρ :=
      (hkcont.mul hpsph).circleIntegrable hρ.le
    have hci_q : CircleIntegrable (fun s => poissonKernel w z s * q s) w ρ :=
      (hkcont.mul hqsph).circleIntegrable hρ.le
    have hker_nn : ∀ s ∈ Metric.sphere w |ρ|, 0 ≤ poissonKernel w z s := by
      intro s hs
      rw [abs_of_pos hρ] at hs
      have hzc : ‖s - w‖ = ρ := by rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
      rw [poissonKernel_def]
      apply div_nonneg _ (by positivity)
      have : ‖z - w‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzlt.le 2
      rw [hzc]; linarith
    apply Real.circleAverage_mono hci_p hci_q
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (hker_nn s hs)
    exact hpq s (by rwa [abs_of_pos hρ] at hs)
  -- The core construction: from a sequence of family members, build a harmonic limit on a disk.
  -- For a chosen disk `closedBall w ρ ⊆ U`, this produces the supremum of Poisson-modified
  -- running maxima, which is harmonic on `ball w ρ`, `≤ u`, and dominates each `g k`.
  have hbuild : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall w ρ ⊆ U →
      ∀ (g : ℕ → ℂ → ℝ), (∀ n, g n ∈ perronFamily φ U) →
      ∃ V : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd V (Metric.ball w ρ)
        ∧ (∀ z ∈ Metric.ball w ρ, V z ≤ u z)
        ∧ (∀ k, ∀ z ∈ Metric.ball w ρ, g k z ≤ V z)
        ∧ (V = fun z => ⨆ k, poissonModify (rmax g k) w ρ z) := by
    intro w ρ hρ hball g hg
    -- The Poisson-modified running max, a family member, harmonic on the ball.
    set Vseq : ℕ → ℂ → ℝ := fun k => poissonModify (rmax g k) w ρ with hVseq
    -- Each `rmax g k` is a family member; record its subharmonicity.
    have hrm_mem : ∀ k, rmax g k ∈ perronFamily φ U := hrmax_mem g hg
    have hrm_sub : ∀ k, SubharmonicOn (rmax g k) U := fun k => (hrm_mem k).1
    -- Each `Vseq k` is a family member.
    have hVseq_mem : ∀ k, Vseq k ∈ perronFamily φ U :=
      fun k => hpmod_mem w ρ hρ hball (rmax g k) (hrm_mem k)
    -- `Vseq k ≤ u` on `U`.
    have hVseq_le_u : ∀ k, ∀ z ∈ U, Vseq k z ≤ u z := fun k z hz =>
      hmem_le (Vseq k) (hVseq_mem k) z hz
    -- `Vseq k ≥ rmax g k` on `U`.
    have hVseq_ge : ∀ k, ∀ z ∈ U, rmax g k z ≤ Vseq k z := fun k z hz =>
      poissonModify_ge (hrm_sub k) hρ hball z hz
    -- `Vseq k` harmonic on `ball w ρ`.
    have hVseq_harm : ∀ k, InnerProductSpace.HarmonicOnNhd (Vseq k) (Metric.ball w ρ) :=
      fun k => poissonModify_harmonicOn (hrm_sub k) hρ hball
    -- `Vseq` is monotone in `k` on `ball w ρ` (data `rmax g k` is monotone, kernel ≥ 0).
    have hVseq_mono : ∀ z ∈ Metric.ball w ρ, Monotone (fun k => Vseq k z) := by
      intro z hz
      apply monotone_nat_of_le_succ
      intro k
      exact hpmod_data_mono w ρ hρ hball (rmax g k) (rmax g (k + 1)) (hrm_mem k).2.1
        (hrm_mem (k + 1)).2.1 (fun s _ => hrmax_mono g s (Nat.le_succ k)) z hz
    -- `Vseq k z ≤ u z` on the ball, hence the supremum exists.
    have hVseq_le_u_ball : ∀ k, ∀ z ∈ Metric.ball w ρ, Vseq k z ≤ u z := by
      intro k z hz; exact hVseq_le_u k z (hball (Metric.ball_subset_closedBall hz))
    have hbddrange : ∀ z ∈ Metric.ball w ρ, BddAbove (Set.range (fun k => Vseq k z)) := by
      intro z hz
      exact ⟨u z, by rintro x ⟨k, rfl⟩; exact hVseq_le_u_ball k z hz⟩
    -- The supremum limit.
    set V : ℂ → ℝ := fun z => ⨆ k, Vseq k z with hV
    have htends : ∀ z ∈ Metric.ball w ρ, Tendsto (fun k => Vseq k z) atTop (𝓝 (V z)) := by
      intro z hz
      have := tendsto_atTop_ciSup (hVseq_mono z hz) (hbddrange z hz)
      simpa [hV] using this
    have hV_le : ∀ z ∈ Metric.ball w ρ, V z ≤ u z := by
      intro z hz
      exact ciSup_le (fun k => hVseq_le_u_ball k z hz)
    have hbdd : ∀ z ∈ Metric.ball w ρ, ∀ n, Vseq n z ≤ V z := by
      intro z hz n
      exact le_ciSup (hbddrange z hz) n
    -- Harnack's principle: `V` is harmonic on `ball w ρ`.
    have hVharm : InnerProductSpace.HarmonicOnNhd V (Metric.ball w ρ) :=
      harmonicOnNhd_of_monotone_tendsto hVseq_harm hVseq_mono hbdd htends
    -- `g k ≤ V` on the ball (chain `g k ≤ rmax g k ≤ Vseq k ≤ V`).
    have hgle : ∀ k, ∀ z ∈ Metric.ball w ρ, g k z ≤ V z := by
      intro k z hz
      have hzU : z ∈ U := hball (Metric.ball_subset_closedBall hz)
      calc g k z ≤ rmax g k z := hrmax_ge g k z
        _ ≤ Vseq k z := hVseq_ge k z hzU
        _ ≤ V z := hbdd z hz k
    exact ⟨V, hVharm, hV_le, hgle, rfl⟩
  -- Monotonicity of the built limit in the data sequence (on the ball).
  have hbuild_mono : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall w ρ ⊆ U →
      ∀ (g₁ g₂ : ℕ → ℂ → ℝ), (∀ n, g₁ n ∈ perronFamily φ U) →
      (∀ n, g₂ n ∈ perronFamily φ U) → (∀ n z, g₁ n z ≤ g₂ n z) →
      ∀ z ∈ Metric.ball w ρ,
        (⨆ k, poissonModify (rmax g₁ k) w ρ z)
          ≤ ⨆ k, poissonModify (rmax g₂ k) w ρ z := by
    intro w ρ hρ hball g₁ g₂ hg₁ hg₂ hle z hz
    have hzU : z ∈ U := hball (Metric.ball_subset_closedBall hz)
    -- Termwise comparison and bdd above by `u z`.
    have hterm : ∀ k,
        poissonModify (rmax g₁ k) w ρ z ≤ poissonModify (rmax g₂ k) w ρ z := by
      intro k
      exact hpmod_data_mono w ρ hρ hball (rmax g₁ k) (rmax g₂ k) (hrmax_mem g₁ hg₁ k).2.1
        (hrmax_mem g₂ hg₂ k).2.1 (fun s _ => hrmax_data_mono g₁ g₂ hle k s) z hz
    have hbdd2 : BddAbove (Set.range (fun k => poissonModify (rmax g₂ k) w ρ z)) := by
      refine ⟨u z, ?_⟩
      rintro x ⟨k, rfl⟩
      exact hmem_le _ (hpmod_mem w ρ hρ hball (rmax g₂ k) (hrmax_mem g₂ hg₂ k)) z hzU
    exact ciSup_mono hbdd2 hterm
  -- A maximizing sequence of family members at any point `p ∈ U`.
  have hmaxseq : ∀ p ∈ U, ∃ s : ℕ → ℂ → ℝ, (∀ n, s n ∈ perronFamily φ U) ∧
      Tendsto (fun n => s n p) atTop (𝓝 (u p)) := by
    intro p hp
    set S : Set ℝ := (fun v => v p) '' perronFamily φ U with hS
    have hSne : S.Nonempty := by
      obtain ⟨v, hv⟩ := hne; exact ⟨v p, v, hv, rfl⟩
    have hSbdd : BddAbove S := by
      refine ⟨max M 0, ?_⟩
      rintro x ⟨v, hv, rfl⟩
      exact le_trans (hmem_le v hv p hp) (hu_le p hp)
    obtain ⟨a, _, hatends, hamem⟩ := exists_seq_tendsto_sSup hSne hSbdd
    -- Choose a family member realizing each `a n`.
    have hchoose : ∀ n, ∃ v ∈ perronFamily φ U, v p = a n := fun n => hamem n
    choose s hs hsval using hchoose
    refine ⟨s, hs, ?_⟩
    have hsup : sSup S = u p := rfl
    rw [← hsup]
    have : (fun n => s n p) = a := funext fun n => hsval n
    rw [this]; exact hatends
  -- Prove `HarmonicAt u w` for each `w ∈ U`.
  intro w hw
  -- A closed disk `closedBall w ρ ⊆ U`.
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ > 0, Metric.closedBall w ρ ⊆ U := by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hUopen.mem_nhds hw)
    exact ⟨ρ, hρpos, hρsub⟩
  have hwball : w ∈ Metric.ball w ρ := Metric.mem_ball_self hρpos
  -- A maximizing sequence at `w`; build the harmonic limit `V`.
  obtain ⟨gw, hgw_mem, hgw_tends⟩ := hmaxseq w hw
  obtain ⟨V, hVharm, hV_le, hV_ge, hVeq⟩ := hbuild w ρ hρpos hρsub gw hgw_mem
  -- `V w = u w` (squeeze: `gw k w ≤ V w ≤ u w` and `gw k w → u w`).
  have hVw : V w = u w := by
    apply le_antisymm (hV_le w hwball)
    refine le_of_tendsto_of_tendsto hgw_tends tendsto_const_nhds ?_
    filter_upwards with k using hV_ge k w hwball
  -- `V = u` on `ball w ρ`.
  have hVu_ball : ∀ y ∈ Metric.ball w ρ, V y = u y := by
    intro y hy
    have hyU : y ∈ U := hρsub (Metric.ball_subset_closedBall hy)
    -- A maximizing sequence at `y`; combine with `gw` and build `Q`.
    obtain ⟨gy, hgy_mem, hgy_tends⟩ := hmaxseq y hyU
    set gc : ℕ → ℂ → ℝ := fun n z => max (gw n z) (gy n z) with hgc
    have hgc_mem : ∀ n, gc n ∈ perronFamily φ U := by
      intro n
      obtain ⟨hs1, hc1, hf1⟩ := hgw_mem n
      obtain ⟨hs2, hc2, hf2⟩ := hgy_mem n
      exact ⟨subharmonicOn_max hs1 hs2, fun x hx => (hc1 x hx).max (hc2 x hx),
        fun ζ hζ => max_le (hf1 ζ hζ) (hf2 ζ hζ)⟩
    obtain ⟨Q, hQharm, hQ_le, hQ_ge, hQeq⟩ := hbuild w ρ hρpos hρsub gc hgc_mem
    -- `Q w = u w` and `Q y = u y` (squeeze from the maximizing subsequences).
    have hQw : Q w = u w := by
      apply le_antisymm (hQ_le w hwball)
      refine le_of_tendsto_of_tendsto hgw_tends tendsto_const_nhds ?_
      filter_upwards with k using le_trans (le_max_left _ _) (hQ_ge k w hwball)
    have hQy : Q y = u y := by
      apply le_antisymm (hQ_le y hy)
      refine le_of_tendsto_of_tendsto hgy_tends tendsto_const_nhds ?_
      filter_upwards with k using le_trans (le_max_right _ _) (hQ_ge k y hy)
    -- `Q ≥ V` on `ball w ρ` (since `gc ≥ gw` and the construction is monotone in the data).
    have hQgeV : ∀ z ∈ Metric.ball w ρ, V z ≤ Q z := by
      intro z hz
      rw [hVeq, hQeq]
      exact hbuild_mono w ρ hρpos hρsub gw gc hgw_mem hgc_mem
        (fun n z => le_max_left _ _) z hz
    -- `Q - V` is nonnegative harmonic on `ball w ρ`, vanishes at `w`; strong min principle.
    set D : ℂ → ℝ := fun z => Q z - V z with hD
    have hDharm : InnerProductSpace.HarmonicOnNhd D (Metric.ball w ρ) := hQharm.sub hVharm
    have hDnn : ∀ z ∈ Metric.ball w ρ, 0 ≤ D z := fun z hz => by
      simp only [hD]; linarith [hQgeV z hz]
    have hDw0 : D w = 0 := by simp only [hD, hQw, hVw, sub_self]
    have hDzero := harmonic_eq_zero_of_nonneg_eq_zero Metric.isOpen_ball
      (convex_ball w ρ).isPreconnected hDharm hDnn hwball hDw0
    -- Hence `Q y = V y`, so `V y = u y` (using `Q y = u y`).
    have hDy : D y = 0 := hDzero y hy
    have : Q y = V y := by simp only [hD] at hDy; linarith
    rw [← this, hQy]
  -- `u` agrees with the harmonic `V` on the neighbourhood `ball w ρ`; transfer harmonicity.
  have heqnhd : u =ᶠ[𝓝 w] V := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwball] with y hy using (hVu_ball y hy).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds heqnhd).2 (hVharm w hwball)

end RiemannDynamics
