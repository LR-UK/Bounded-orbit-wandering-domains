/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationEndCharts
import BoundedWanderingDomains.Surfaces.NestedBoundaryMass
import BoundedWanderingDomains.Surfaces.FinitePunctureTopology
import BoundedWanderingDomains.Surfaces.FiniteBoundaryMassAssembly
import BoundedWanderingDomains.CutoffEndLimits

/-! # The finite end set for one point insertion on an anchor complement -/

open Set Function Filter Metric MeasureTheory TopologicalSpace
  InnerProductSpace Laplacian
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X] [DecidableEq X]

/-- Ambient compactification ends consisting of fixed anchors, old punctures,
and the newly inserted point. -/
noncomputable def compactificationInsertionEnds
    (E : Finset X) (O : Opens X) (P : Finset O) (a : O) : Finset X :=
  E ∪ P.image (Subtype.val : O → X) ∪ {(a : X)}

@[simp] theorem mem_compactificationInsertionEnds
    (E : Finset X) (O : Opens X) (P : Finset O) (a : O) (x : X) :
    x ∈ compactificationInsertionEnds E O P a ↔
      x ∈ E ∨ (∃ y ∈ P, (y : X) = x) ∨ (a : X) = x := by
  classical
  simp only [compactificationInsertionEnds, Finset.mem_union, Finset.mem_image,
    Finset.mem_singleton]
  aesop

theorem left_mem_compactificationInsertionEnds
    (E : Finset X) (O : Opens X) (P : Finset O) (a : O) :
    E ⊆ compactificationInsertionEnds E O P a := by
  intro x hx
  simp [compactificationInsertionEnds, hx]

theorem old_mem_compactificationInsertionEnds
    (E : Finset X) (O : Opens X) (P : Finset O) (a : O)
    {x : O} (hx : x ∈ P) :
    (x : X) ∈ compactificationInsertionEnds E O P a := by
  simp [compactificationInsertionEnds, hx]

theorem new_mem_compactificationInsertionEnds
    (E : Finset X) (O : Opens X) (P : Finset O) (a : O) :
    (a : X) ∈ compactificationInsertionEnds E O P a := by
  simp [compactificationInsertionEnds]

namespace FinitePunctureDiscs

/-- Every end other than the inserted point is absent from the old
finite-puncture subtype. -/
theorem oldEnd_not_mem_oldDomain
    (E : Finset X) (O : Opens X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E)
    (P : Finset O) (a : O)
    {i : ↑(compactificationInsertionEnds E O P a)}
    (hia : (i : X) ≠ (a : X)) :
    ∀ y : finitePunctureDomain P, ((y : O) : X) ≠ (i : X) := by
  intro y hy
  have hi := i.property
  rw [mem_compactificationInsertionEnds] at hi
  rcases hi with hiE | ⟨z, hzP, hzi⟩ | hia'
  · apply (hO ((y : O) : X)).mp (y : O).property
    exact hy.symm ▸ hiE
  · have hyz : (y : O) = z := Subtype.ext (hy.trans hzi.symm)
    exact y.property (hyz ▸ hzP)
  · exact hia hia'.symm

/-- Every old compactification end has vanishing ambient boundary mass for
one-point insertion. -/
theorem DiscCover.tendsto_compactification_oldEnd_boundary_zero
    (E : Finset X) (O : Opens X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hON : Nonempty O)
    [MeasurableSpace O] [BorelSpace O]
    [ConnectedSpace O] [Infinite O]
    (p : DiscCover O) (P : Finset O) (a0 : O) (ha0 : a0 ∉ P)
    (q : DiscCover (finitePunctureDomain P))
    (s : DiscCover (finitePunctureDomain
      ({(⟨a0, ha0⟩ : finitePunctureDomain P)} : Finset _)))
    (D : FinitePunctureDiscs (compactificationInsertionEnds E O P a0))
    (i : ↑(compactificationInsertionEnds E O P a0))
    (hia : (i : X) ≠ (a0 : X)) :
    let U := finitePunctureDomain P
    let a : U := ⟨a0, ha0⟩
    let W := finitePunctureDomain ({a} : Finset U)
    let V := finitePunctureDomain (insert a0 P)
    Tendsto (fun t : ℝ => ∫ z : ℂ,
      p.domainChartLogRatio U V
        ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
        Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t)) z) atTop (𝓝 0) := by
  let U := finitePunctureDomain P
  let a : U := ⟨a0, ha0⟩
  let W := finitePunctureDomain ({a} : Finset U)
  let V := finitePunctureDomain (insert a0 P)
  letI : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset P)
  letI : Infinite U := Set.Infinite.to_subtype P.finite_toSet.infinite_compl
  letI : ConnectedSpace W := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset ({a} : Finset U))
  letI : ConnectedSpace V := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset (insert a0 P))
  have hUN : Nonempty U := ⟨a⟩
  have hWN : Nonempty W := ⟨s.projection discZero⟩
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hWambient : ∀ x : U, x ∈ W ↔ (x : O) ∈ V := by
    intro x
    rw [show x ∈ W ↔ x ≠ a by
      simp only [W, mem_finitePunctureDomain, Finset.mem_singleton]]
    rw [show (x : O) ∈ V ↔ (x : O) ≠ a0 ∧ (x : O) ∉ P by
      simp only [V, mem_finitePunctureDomain, Finset.mem_insert, not_or]]
    constructor
    · intro hxa
      refine ⟨?_, x.property⟩
      intro hx
      exact hxa (Subtype.ext hx)
    · intro hx hxa
      exact hx.1 (congrArg Subtype.val hxa)
  have hWK : ∀ x : U, x ∈ W ↔ x ∉ ({a} : Set U) := by
    intro x
    simp [W, finitePunctureDomain]
  have hball := D.puncturedBall_subset_three_restricted_targets i E
    (left_mem_compactificationInsertionEnds E O P a0) O hO hON P
    (fun x hx => old_mem_compactificationInsertionEnds E O P a0 hx)
    hUN a (new_mem_compactificationInsertionEnds E O P a0) hWN
  have hescape := subtypeRestr_symm_tendsto_cocompact O hON U hUN W hWN
    (D.disc i).center (by
      intro y
      rw [D.center i]
      exact oldEnd_not_mem_oldDomain E O hO P a0 hia y)
    (D.disc i).radius_pos hball
  let x : ℂ → W := fun z =>
    (((((chartAt ℂ (D.disc i).center).subtypeRestr hON).subtypeRestr
      hUN).subtypeRestr hWN).symm z)
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON)
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON).source :=
    mdifferentiableOn_subtypeRestr hON
      (mdifferentiable_chart (I := 𝓘(ℂ)) (D.disc i).center).1
  exact p.tendsto_domainChart_old_boundary_mass_zero hVU hUN q
    (isCompact_singleton : IsCompact ({a} : Set U)) W hWK hWambient hWN s hc
    (D.disc i).radius_pos hball x hescape.1 hescape.2

/-- The distinguished newly inserted compactification end has uniformly
bounded ambient boundary mass. -/
theorem DiscCover.eventually_bounded_compactification_newEnd_boundary
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
    let a : U := ⟨a0, ha0⟩
    let W := finitePunctureDomain ({a} : Finset U)
    let V := finitePunctureDomain (insert a0 P)
    let j : ↑(compactificationInsertionEnds E O P a0) :=
      ⟨a0, new_mem_compactificationInsertionEnds E O P a0⟩
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop,
      |∫ z : ℂ, p.domainChartLogRatio U V
        ((chartAt ℂ (D.disc j).center).subtypeRestr hON) z *
        Δ (AreaDeficit.logCutoff
          (chartAt ℂ (D.disc j).center (D.disc j).center)
          (-2 * t) (-t)) z| ≤ B := by
  let U := finitePunctureDomain P
  let a : U := ⟨a0, ha0⟩
  let W := finitePunctureDomain ({a} : Finset U)
  let V := finitePunctureDomain (insert a0 P)
  let j : ↑(compactificationInsertionEnds E O P a0) :=
    ⟨a0, new_mem_compactificationInsertionEnds E O P a0⟩
  letI : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset P)
  letI : Infinite U := Set.Infinite.to_subtype P.finite_toSet.infinite_compl
  letI : ConnectedSpace W := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset ({a} : Finset U))
  letI : ConnectedSpace V := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset (insert a0 P))
  have hUN : Nonempty U := ⟨a⟩
  have hWN : Nonempty W := ⟨s.projection discZero⟩
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hWambient : ∀ x : U, x ∈ W ↔ (x : O) ∈ V := by
    intro x
    rw [show x ∈ W ↔ x ≠ a by
      simp only [W, mem_finitePunctureDomain, Finset.mem_singleton]]
    rw [show (x : O) ∈ V ↔ (x : O) ≠ a0 ∧ (x : O) ∉ P by
      simp only [V, mem_finitePunctureDomain, Finset.mem_insert, not_or]]
    constructor
    · intro hxa
      refine ⟨?_, x.property⟩
      intro hx
      exact hxa (Subtype.ext hx)
    · intro hx hxa
      exact hx.1 (congrArg Subtype.val hxa)
  have hball := D.puncturedBall_subset_three_restricted_targets j E
    (left_mem_compactificationInsertionEnds E O P a0) O hO hON P
    (fun x hx => old_mem_compactificationInsertionEnds E O P a0 hx)
    hUN a (new_mem_compactificationInsertionEnds E O P a0) hWN
  let c := (chartAt ℂ (D.disc j).center).subtypeRestr hON
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON
      (mdifferentiable_chart (I := 𝓘(ℂ)) (D.disc j).center).1
  have hasource : a0 ∈ c.source := by
    simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
      D.center j] using (mem_chart_source ℂ (a0 : X))
  have ha : chartAt ℂ (D.disc j).center (D.disc j).center ∈
      (c.subtypeRestr hUN).target := by
    have hmap := c.map_subtype_source hUN (x := a) hasource
    have hcval : c a0 = chartAt ℂ (D.disc j).center (a0 : X) := by
      simp only [c, OpenPartialHomeomorph.subtypeRestr_coe,
        Set.domRestrict_apply]
    rw [hcval] at hmap
    have hj : (j : X) = a0 := rfl
    simpa only [D.center j, hj] using hmap
  exact p.eventually_bounded_domainChart_new_boundary_mass hVU hUN q W
    hWambient hWN s hc ha (D.disc j).radius_pos hball

/-- The sum of all raw compactification-end boundary terms for one point
insertion has one eventual bound. -/
theorem DiscCover.eventually_bounded_compactification_boundary_sum
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
      |∑ i : ↑(compactificationInsertionEnds E O P a0), ∫ z : ℂ,
        p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
          Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * t) (-t)) z| ≤ B := by
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (insert a0 P)
  let F := compactificationInsertionEnds E O P a0
  let j : ↑F := ⟨a0, new_mem_compactificationInsertionEnds E O P a0⟩
  let u : ↑F → ℝ → ℝ := fun i t => ∫ z : ℂ,
    p.domainChartLogRatio U V
      ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
      Δ (AreaDeficit.logCutoff
        (chartAt ℂ (D.disc i).center (D.disc i).center)
        (-2 * t) (-t)) z
  obtain ⟨B, hB, hnew⟩ :=
    AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.eventually_bounded_compactification_newEnd_boundary
      E O hO hON p P a0 ha0 q s D
  have hold : ∀ i ∈ (Finset.univ.erase j),
      Tendsto (u i) atTop (𝓝 0) := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hia : (i : X) ≠ (a0 : X) := by
      intro hval
      apply hij
      apply Subtype.ext
      exact hval
    exact AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.tendsto_compactification_oldEnd_boundary_zero
      E O hO hON p P a0 ha0 q s D i hia
  have hnew' : ∀ i ∈ ({j} : Finset ↑F),
      ∀ᶠ t : ℝ in atTop, |u i t| ≤ B := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    subst i
    exact hnew
  have hsum := eventually_bounded_old_new_boundary_sum
    (Finset.univ.erase j) ({j} : Finset ↑F) u u (fun _ => B) hold hnew'
  refine ⟨1 + B, by linarith, ?_⟩
  simpa only [u, F, U, V, Finset.sum_singleton,
    Finset.sum_erase_add _ _ (Finset.mem_univ j)] using hsum

/-- For all sufficiently deep readings, every raw end pairing in the finite
compactification family is integrable. -/
theorem DiscCover.eventually_integrable_compactification_boundary
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
      ∀ i : ↑(compactificationInsertionEnds E O P a0), Integrable
        (fun z : ℂ => p.domainChartLogRatio U V
          ((chartAt ℂ (D.disc i).center).subtypeRestr hON) z *
          Δ (AreaDeficit.logCutoff
            (chartAt ℂ (D.disc i).center (D.disc i).center)
            (-2 * t) (-t)) z) := by
  let U := finitePunctureDomain P
  let a : U := ⟨a0, ha0⟩
  let W := finitePunctureDomain ({a} : Finset U)
  let V := finitePunctureDomain (insert a0 P)
  letI : ConnectedSpace U := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset P)
  letI : Infinite U := Set.Infinite.to_subtype P.finite_toSet.infinite_compl
  letI : ConnectedSpace W := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset ({a} : Finset U))
  letI : ConnectedSpace V := Subtype.connectedSpace
    (RiemannDynamics.isConnected_compl_finset (insert a0 P))
  have hUN : Nonempty U := ⟨a⟩
  have hWN : Nonempty W := ⟨s.projection discZero⟩
  have hVU : V ≤ U := by
    intro x hx hxP
    exact hx (Finset.mem_insert_of_mem hxP)
  have hWambient : ∀ x : U, x ∈ W ↔ (x : O) ∈ V := by
    intro x
    rw [show x ∈ W ↔ x ≠ a by
      simp only [W, mem_finitePunctureDomain, Finset.mem_singleton]]
    rw [show (x : O) ∈ V ↔ (x : O) ≠ a0 ∧ (x : O) ∉ P by
      simp only [V, mem_finitePunctureDomain, Finset.mem_insert, not_or]]
    constructor
    · intro hxa
      exact ⟨fun hx => hxa (Subtype.ext hx), x.property⟩
    · intro hx hxa
      exact hx.1 (congrArg Subtype.val hxa)
  have hrad : ∀ᶠ t : ℝ in atTop,
      ∀ i : ↑(compactificationInsertionEnds E O P a0),
        -Real.log (D.disc i).radius < t :=
    ((Filter.eventually_all_finite Set.finite_univ).2 fun i _ =>
      eventually_gt_atTop (-Real.log (D.disc i).radius)).mono
        (fun _ h i => h i (mem_univ i))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hrad] with t ht htr
  intro i
  have hball := D.puncturedBall_subset_three_restricted_targets i E
    (left_mem_compactificationInsertionEnds E O P a0) O hO hON P
    (fun x hx => old_mem_compactificationInsertionEnds E O P a0 hx)
    hUN a (new_mem_compactificationInsertionEnds E O P a0) hWN
  let c := (chartAt ℂ (D.disc i).center).subtypeRestr hON
  have hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source :=
    mdifferentiableOn_subtypeRestr hON
      (mdifferentiable_chart (I := 𝓘(ℂ)) (D.disc i).center).1
  apply AreaDeficit.integrable_mul_laplacian_logCutoff
    (chartAt ℂ (D.disc i).center (D.disc i).center) (by linarith)
  intro z hzlower hzupper
  apply (p.domainChartLogRatio_contDiffAt hVU hc ?_).continuousAt
  apply AreaDeficit.Surfaces.DiscCover.mem_domainChartSet_of_mem_nested_target
    hUN W hWambient hWN c
  apply hball
  constructor
  · rw [mem_ball, dist_eq_norm]
    calc
      ‖z - chartAt ℂ (D.disc i).center (D.disc i).center‖
          ≤ Real.exp (-t) := hzupper
      _ < (D.disc i).radius := by
        rw [← Real.exp_log (D.disc i).radius_pos]
        exact Real.exp_lt_exp.mpr (by linarith [htr i])
  · rw [mem_singleton_iff]
    intro hz
    rw [hz, sub_self, norm_zero] at hzlower
    exact (not_le_of_gt (Real.exp_pos _)) hzlower

end FinitePunctureDiscs
end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.FinitePunctureDiscs.DiscCover.tendsto_compactification_oldEnd_boundary_zero



