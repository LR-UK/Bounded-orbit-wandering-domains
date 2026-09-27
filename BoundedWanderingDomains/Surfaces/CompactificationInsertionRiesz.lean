/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationInsertionEnds
import BoundedWanderingDomains.Surfaces.CompactificationCutoffGreen

/-! # Riesz bound for one insertion on a compactification complement -/

open Set Function Filter Metric MeasureTheory TopologicalSpace
  InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff BigOperators

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X] [DecidableEq X]

namespace FinitePunctureDiscs

/-- The intrinsic Green pairings of the compactification cutoffs are
eventually bounded for a one-point insertion. -/
theorem DiscCover.eventually_bounded_compactification_intrinsicGreen
    (E : Finset X) (O : Opens X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    [ConnectedSpace O] [Infinite O]
    (p : DiscCover O) (P : Finset O) (a0 : O) (ha0 : a0 ∉ P)
    (q : DiscCover (finitePunctureDomain P))
    (s : DiscCover (finitePunctureDomain
      ({(⟨a0, ha0⟩ : finitePunctureDomain P)} : Finset _)))
    (D : FinitePunctureDiscs (compactificationInsertionEnds E O P a0)) :
    let U := finitePunctureDomain P
    let V := finitePunctureDomain (insert a0 P)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop,
      D.Admissible t ∧
      |∫ x, p.domainLogRatio U V x *
        p.intrinsicLaplacian (D.restrictedCutoff O t) x
          ∂p.hyperbolicArea| ≤ B := by
  let F := compactificationInsertionEnds E O P a0
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (insert a0 P)
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hEF : E ⊆ F := left_mem_compactificationInsertionEnds E O P a0
  let raw : ↑F → ℝ → ℝ := fun i t => ∫ z : ℂ,
    p.domainChartLogRatio U V
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ (D.disc i).center (D.disc i).center)
        (-2 * t) (-t)) z
  obtain ⟨Braw, hBraw, hraw⟩ :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_bounded_compactification_boundary_sum
      E O hO hON p P a0 ha0 q s D
  have hint :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_integrable_compactification_boundary
      E O hO hON p P a0 ha0 q s D
  obtain ⟨r, hr, hir⟩ : ∃ r : ℝ, D.Admissible r ∧
      ∀ i : ↑F, Integrable (fun z : ℂ =>
        p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
          Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * r) (-r)) z) :=
    (D.eventually_admissible.and hint).exists
  let G : ℝ → ℝ := fun t => ∫ x, p.domainLogRatio U V x *
    p.intrinsicLaplacian (D.restrictedCutoff O t) x ∂p.hyperbolicArea
  let C : ℝ := |G r| + |∑ i : ↑F, raw i r|
  refine ⟨Braw + C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hraw, D.eventually_admissible, hint] with t htbound ht hit
  refine ⟨ht, ?_⟩
  have hcutV : ∀ {v : ℝ}, D.Admissible v →
      tsupport (D.restrictedCutoff O v) ⊆ V := by
    intro v hv x hx
    have hxF := D.restrictedCutoff_tsupport_avoids O hv hx
    change x ∉ insert a0 P
    intro hxinsert
    rw [Finset.mem_insert] at hxinsert
    rcases hxinsert with hxa | hxP
    · exact hxF (hxa ▸ new_mem_compactificationInsertionEnds E O P a0)
    · exact hxF (old_mem_compactificationInsertionEnds E O P a0 hxP)
  have hetaV : ∀ i : ↑F, tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoffDiff (D.disc i) O t r)) ⊆ V := by
    intro i x hx
    have hxeta := p.tsupport_intrinsicLaplacian_subset _ hx
    have hxF := D.restrictedSurfaceLogCutoffDiff_tsupport_avoids i O ht hr hxeta
    change x ∉ insert a0 P
    intro hxinsert
    rw [Finset.mem_insert] at hxinsert
    rcases hxinsert with hxa | hxP
    · exact hxF (hxa ▸ new_mem_compactificationInsertionEnds E O P a0)
    · exact hxF (old_mem_compactificationInsertionEnds E O P a0 hxP)
  have hgreen :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.intrinsicGreen_restrictedCutoff_sub
      hON p hVU D E hO hEF ht hr hetaV
  have hsmooth_t := D.restrictedCutoff_contMDiff O ht
  have hsmooth_r := D.restrictedCutoff_contMDiff O hr
  have hcompact_t := D.restrictedCutoff_hasCompactSupport_of_compl_finset
    O E hO hEF ht
  have hcompact_r := D.restrictedCutoff_hasCompactSupport_of_compl_finset
    O E hO hEF hr
  have hint_t := p.integrable_domainLogRatio_mul_intrinsicLaplacian hVU
    hsmooth_t hcompact_t
      ((p.tsupport_intrinsicLaplacian_subset _).trans (hcutV ht))
  have hint_r := p.integrable_domainLogRatio_mul_intrinsicLaplacian hVU
    hsmooth_r hcompact_r
      ((p.tsupport_intrinsicLaplacian_subset _).trans (hcutV hr))
  have hleft : (∫ x, p.domainLogRatio U V x *
      p.intrinsicLaplacian (D.restrictedCutoff O t -
        D.restrictedCutoff O r) x ∂p.hyperbolicArea) = G t - G r := by
    rw [show (fun x => p.domainLogRatio U V x *
        p.intrinsicLaplacian (D.restrictedCutoff O t -
          D.restrictedCutoff O r) x) =
        (fun x => p.domainLogRatio U V x *
          p.intrinsicLaplacian (D.restrictedCutoff O t) x) -
        (fun x => p.domainLogRatio U V x *
          p.intrinsicLaplacian (D.restrictedCutoff O r) x) by
      funext x
      rw [p.intrinsicLaplacian_sub hsmooth_t hsmooth_r x]
      simp only [Pi.sub_apply]
      ring]
    change (∫ x, (p.domainLogRatio U V x *
      p.intrinsicLaplacian (D.restrictedCutoff O t) x) -
      (p.domainLogRatio U V x *
      p.intrinsicLaplacian (D.restrictedCutoff O r) x)
        ∂p.hyperbolicArea) = G t - G r
    rw [integral_sub hint_t hint_r]
  have hright : (∑ i : ↑F, ∫ z,
      p.domainChartLogRatio U V
        ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t) -
        AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * r) (-r)) z) =
      (∑ i : ↑F, raw i t) - ∑ i : ↑F, raw i r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (fun z => p.domainChartLogRatio U V
        ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
        Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * t) (-t) -
          AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * r) (-r)) z) =
        (fun z => p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
          Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * t) (-t)) z) -
        (fun z => p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
          Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * r) (-r)) z) by
      funext z
      have hct : ContDiffAt ℝ 2 (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t)) z :=
        (AreaDeficit.logCutoff_contDiff _ (by linarith [ht.1])).contDiffAt.of_le
          (by norm_num)
      have hcr : ContDiffAt ℝ 2 (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * r) (-r)) z :=
        (AreaDeficit.logCutoff_contDiff _ (by linarith [hr.1])).contDiffAt.of_le
          (by norm_num)
      rw [hct.laplacian_sub hcr]
      simp only [Pi.sub_apply]
      ring]
    change (∫ z, (p.domainChartLogRatio U V
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ (D.disc i).center (D.disc i).center)
        (-2 * t) (-t)) z) -
      (p.domainChartLogRatio U V
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ (D.disc i).center (D.disc i).center)
        (-2 * r) (-r)) z)) = raw i t - raw i r
    rw [integral_sub (hit i) (hir i)]
  rw [hleft, hright] at hgreen
  have hG : G t = -(∑ i : ↑F, raw i t) +
      (G r + ∑ i : ↑F, raw i r) := by linarith [hgreen]
  have htbound' : |∑ i : ↑F, raw i t| ≤ Braw := by
    simpa only [raw, F, U, V] using htbound
  change |G t| ≤ Braw + C
  rw [hG]
  calc
    |-∑ i : ↑F, raw i t + (G r + ∑ i : ↑F, raw i r)| ≤
        |∑ i : ↑F, raw i t| + (|G r| + |∑ i : ↑F, raw i r|) := by
      calc
        _ ≤ |-∑ i : ↑F, raw i t| + |G r + ∑ i : ↑F, raw i r| := abs_add_le _ _
        _ ≤ |∑ i : ↑F, raw i t| + (|G r| + |∑ i : ↑F, raw i r|) := by
          rw [abs_neg]
          gcongr
          exact abs_add_le _ _
    _ ≤ Braw + C := by
      dsimp only [C]
      linarith [htbound']

/-- Inserting one point into a finite-puncture model of a compactification
has finite total domain-area gain. -/
theorem DiscCover.compactification_pointInsertion_areaGain_finite
    (E : Finset X) (O : Opens X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    [ConnectedSpace O] [Infinite O]
    (p : DiscCover O) (P : Finset O) (a0 : O) (ha0 : a0 ∉ P)
    (q : DiscCover (finitePunctureDomain P))
    (s : DiscCover (finitePunctureDomain
      ({(⟨a0, ha0⟩ : finitePunctureDomain P)} : Finset _)))
    (D : FinitePunctureDiscs (compactificationInsertionEnds E O P a0)) :
    ∃ C : ℝ, 0 ≤ C ∧
      p.domainAreaGain (finitePunctureDomain P)
        (finitePunctureDomain (insert a0 P)) Set.univ ≤ ENNReal.ofReal C := by
  let F := compactificationInsertionEnds E O P a0
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (insert a0 P)
  let μ := p.domainAreaGain U V
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hEF : E ⊆ F := left_mem_compactificationInsertionEnds E O P a0
  obtain ⟨B, hB, hbound⟩ :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_bounded_compactification_intrinsicGreen
      E O hO hON p P a0 ha0 q s D
  have hadmNat : ∀ᶠ n : ℕ in atTop, D.Admissible (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually D.eventually_admissible
  obtain ⟨N, hN⟩ := eventually_atTop.mp hadmNat
  let time : ℕ → ℝ := fun n => ((n + N : ℕ) : ℝ)
  have htime : Tendsto time atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)
  have hadm : ∀ n, D.Admissible (time n) := by
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  let chi : ℕ → O → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (D.restrictedCutoff O (time n) x)
  let boundary : ℕ → ℝ := fun n => ∫ x,
    p.domainLogRatio U V x *
      p.intrinsicLaplacian (D.restrictedCutoff O (time n)) x
        ∂p.hyperbolicArea
  have hchi : ∀ n, AEMeasurable (chi n) μ := by
    intro n
    exact ((D.restrictedCutoff_contMDiff O (hadm n)).continuous.measurable
      |>.ennreal_ofReal).aemeasurable
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => chi n x) atTop (𝓝 1) := by
    have hmem : (V : Set O) ∈ ae μ := by
      rw [mem_ae_iff]
      exact p.domainAreaGain_compl U V
    filter_upwards [hmem] with x hxV
    have hxF : (x : X) ∉ F := by
      intro hx
      rw [mem_compactificationInsertionEnds] at hx
      rcases hx with hxE | ⟨y, hyP, hyx⟩ | hax
      · exact (hO (x : X)).mp x.property hxE
      · have hxy : x = y := Subtype.ext hyx.symm
        exact hxV (Finset.mem_insert_of_mem (hxy ▸ hyP))
      · exact hxV (Finset.mem_insert.mpr (Or.inl (Subtype.ext hax.symm)))
    have hone := D.restrictedCutoff_eventually_one O hxF
    have honeNat : ∀ᶠ n : ℕ in atTop,
        D.restrictedCutoff O (time n) x = 1 := htime.eventually hone
    apply tendsto_const_nhds.congr'
    filter_upwards [honeNat] with n hn
    simp [chi, hn]
  have hgreen : ∀ n, (∫⁻ x, chi n x ∂μ) =
      ENNReal.ofReal (boundary n) := by
    intro n
    have ht := hadm n
    have hsmooth := D.restrictedCutoff_contMDiff O ht
    have hcompact := D.restrictedCutoff_hasCompactSupport_of_compl_finset
      O E hO hEF ht
    have hnonneg : ∀ x, 0 ≤ D.restrictedCutoff O (time n) x :=
      fun x => (D.restrictedCutoff_bounds O ht x).1
    have hsupport : tsupport (D.restrictedCutoff O (time n)) ⊆ V := by
      intro x hx
      have hxF := D.restrictedCutoff_tsupport_avoids O ht hx
      change x ∉ insert a0 P
      intro hxinsert
      rw [Finset.mem_insert] at hxinsert
      rcases hxinsert with hxa | hxP
      · exact hxF (hxa ▸ new_mem_compactificationInsertionEnds E O P a0)
      · exact hxF (old_mem_compactificationInsertionEnds E O P a0 hxP)
    simpa only [chi, μ, boundary] using
      p.domainAreaGain_lintegral_eq_intrinsic hVU hsmooth hcompact
        hnonneg hsupport
  have hboundNat : ∀ᶠ n : ℕ in atTop, |boundary n| ≤ B := by
    have hreal := (htime.eventually hbound).mono (fun _ h => h.2)
    simpa only [boundary, U, V] using hreal
  refine ⟨B, hB, ?_⟩
  exact measure_univ_le_of_eventually_bounded_riesz_cutoffs μ chi hchi
    hlim boundary hgreen hB hboundNat

end FinitePunctureDiscs
end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_bounded_compactification_intrinsicGreen



