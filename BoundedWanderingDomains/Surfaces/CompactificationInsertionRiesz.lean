/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationInsertionEnds
import BoundedWanderingDomains.Surfaces.CompactificationCutoffGreen
import BoundedWanderingDomains.Surfaces.FinitePunctureTopology
import BoundedWanderingDomains.Surfaces.GlobalPointInsertion

/-! # Riesz bound for one insertion on a compactification complement -/

open Set Function Filter Metric MeasureTheory TopologicalSpace
  InnerProductSpace Laplacian
open scoped Manifold Topology ENNReal ContDiff BigOperators

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X] [DecidableEq X]

namespace FinitePunctureDiscs

/-- The intrinsic Green pairings of the compactification cutoffs have the
same universal bound at every finite puncture stage. -/
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
    ∀ᶠ t : ℝ in atTop,
      D.Admissible t ∧
      |∫ x, p.domainLogRatio U V x *
        p.intrinsicLaplacian (D.restrictedCutoff O t) x
          ∂p.hyperbolicArea| ≤
        1 + 3 * (2 * Real.pi * ∫ u : ℝ,
          |AreaDeficit.transitionSecond u|) := by
  let F := compactificationInsertionEnds E O P a0
  let U := finitePunctureDomain P
  let a : U := ⟨a0, ha0⟩
  let W := finitePunctureDomain ({a} : Finset U)
  let V := finitePunctureDomain (insert a0 P)
  have hUN : Nonempty U := ⟨a⟩
  have hWN : Nonempty W := ⟨s.projection discZero⟩
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hraw :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_bounded_compactification_boundary_sum
      E O hO hON p P a0 ha0 q s D
  have hrad : ∀ᶠ t : ℝ in atTop,
      ∀ i : ↑F, -Real.log (D.disc i).radius < t :=
    ((Filter.eventually_all_finite Set.finite_univ).2 fun i _ =>
      eventually_gt_atTop (-Real.log (D.disc i).radius)).mono
        (fun _ h i => h i (mem_univ i))
  filter_upwards [hraw, D.eventually_admissible, hrad] with t htbound ht hrt
  refine ⟨ht, ?_⟩
  have hball : ∀ i : ↑F,
      ball (chartAt ℂ (D.disc i).center (D.disc i).center)
          (D.disc i).radius \
        {chartAt ℂ (D.disc i).center (D.disc i).center} ⊆
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON).target := by
    intro i z hz
    have hzdeep := D.puncturedBall_subset_three_restricted_targets i E
      (left_mem_compactificationInsertionEnds E O P a0) O hO hON P
      (fun x hx => old_mem_compactificationInsertionEnds E O P a0 hx)
      hUN a (new_mem_compactificationInsertionEnds E O P a0) hWN hz
    have hzmid :=
      (((chartAt ℂ (D.disc i).center).subtypeRestr hON).subtypeRestr hUN).subtypeRestr_target_subset
        hWN hzdeep
    exact ((chartAt ℂ (D.disc i).center).subtypeRestr hON).subtypeRestr_target_subset
      hUN hzmid
  have hetaV : ∀ i : ↑F, tsupport (p.intrinsicLaplacian
      (restrictedSurfaceLogCutoff (D.disc i) O t)) ⊆ V := by
    intro i x hx
    have hxF :=
      AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.tsupport_intrinsicLaplacian_restrictedSurfaceLogCutoff_subset
        p D ht i hx
    change x ∉ insert a0 P
    intro hxinsert
    rw [Finset.mem_insert] at hxinsert
    rcases hxinsert with hxa | hxP
    · exact hxF (hxa ▸ new_mem_compactificationInsertionEnds E O P a0)
    · exact hxF (old_mem_compactificationInsertionEnds E O P a0 hxP)
  have hgreen :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.intrinsicGreen_restrictedCutoff
      hON p hVU D ht hrt hball hetaV
  rw [hgreen, abs_neg]
  simpa only [F, U, V] using htbound
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
    p.domainAreaGain (finitePunctureDomain P)
        (finitePunctureDomain (insert a0 P)) Set.univ ≤
      ENNReal.ofReal (1 + 3 * (2 * Real.pi * ∫ u : ℝ,
        |AreaDeficit.transitionSecond u|)) := by
  let F := compactificationInsertionEnds E O P a0
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (insert a0 P)
  let μ := p.domainAreaGain U V
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hEF : E ⊆ F := left_mem_compactificationInsertionEnds E O P a0
  let B : ℝ := 1 + 3 * (2 * Real.pi * ∫ u : ℝ,
    |AreaDeficit.transitionSecond u|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound :=
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
  simpa only [B] using
    (measure_univ_le_of_eventually_bounded_riesz_cutoffs μ chi hchi
      hlim boundary hgreen hB hboundNat)

/-- The compactification estimate supplies one common insertion bound for
all finite puncture stages of the fixed finite-end complement. -/
theorem DiscCover.compactification_uniformGlobalPointInsertionBound
    (E : Finset X) (O : Opens X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    [ConnectedSpace O] [Infinite O]
    (p : DiscCover O) :
    p.UniformGlobalPointInsertionBound
      (ENNReal.ofReal (1 + 3 * (2 * Real.pi * ∫ u : ℝ,
        |AreaDeficit.transitionSecond u|))) := by
  intro P a0
  by_cases ha0 : a0 ∈ P
  · rw [Finset.insert_eq_of_mem ha0]
    simp
  · let U := finitePunctureDomain P
    let a : U := ⟨a0, ha0⟩
    letI : ConnectedSpace U := Subtype.connectedSpace
      (RiemannDynamics.isConnected_compl_finset P)
    letI : Infinite U := Set.Infinite.to_subtype P.finite_toSet.infinite_compl
    let q : DiscCover U := Classical.choice (p.nonempty_finitePuncture P)
    let W := finitePunctureDomain ({a} : Finset U)
    letI : ConnectedSpace W := Subtype.connectedSpace
      (RiemannDynamics.isConnected_compl_finset ({a} : Finset U))
    let s : DiscCover W := Classical.choice (q.nonempty_finitePuncture
      ({a} : Finset U))
    obtain ⟨D⟩ := exists_finitePunctureDiscs
      (compactificationInsertionEnds E O P a0)
    exact AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.compactification_pointInsertion_areaGain_finite
      E O hO hON p P a0 ha0 q s D

end FinitePunctureDiscs
end AreaDeficit.Surfaces
