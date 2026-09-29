module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.FinitePunctureInsertion
public import BoundedWanderingDomains.Surfaces.DomainAreaSubtype
public import BoundedWanderingDomains.Surfaces.HyperbolicAreaFinite

@[expose] public section

/-! # From a global one-point cost to bounded finite insertion

This file isolates the exact global analytic estimate still needed for the
finite-type compact-surface argument.  Once adding one point costs at most a
fixed amount on the whole surface, the finite-set estimate follows by
telescoping, with no subtraction of infinite measures.
-/

open Set MeasureTheory
open scoped Manifold ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [DecidableEq M]

/-- A uniform whole-surface cost for adding one point to an arbitrary
finite-puncture model.  The intended sharp constant is `2 * π`. -/
def UniformGlobalPointInsertionBound (p : DiscCover M) (C : ℝ≥0∞) : Prop :=
  ∀ (P : Finset M) (a : M),
    p.domainAreaGain (finitePunctureDomain P)
      (finitePunctureDomain (insert a P)) Set.univ ≤ C

omit [LocallyCompactSpace M] in
/-- The global one-point property is intrinsic and hence independent of the
chosen universal disc cover. -/
theorem uniformGlobalPointInsertionBound_independent
    (p r : DiscCover M) {C : ℝ≥0∞}
    (h : p.UniformGlobalPointInsertionBound C) :
    r.UniformGlobalPointInsertionBound C := by
  intro P a
  rw [r.domainAreaGain_independent p]
  exact h P a

omit [LocallyCompactSpace M] in
/-- If the whole ambient surface lies in one planar chart with two omitted
coordinate values, the sharp planar theorem gives the global `2π` one-point
bound directly.  This is the normalized punctured-sphere case. -/
theorem uniformGlobalPointInsertionBound_of_global_chart
    (p : DiscCover M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c.symm c.target)
    (hMc : (Set.univ : Set M) ⊆ c.source)
    {b d : ℂ} (hbd : b ≠ d)
    (hb : b ∉ domainChartSet (⊤ : TopologicalSpace.Opens M) c)
    (hd : d ∉ domainChartSet (⊤ : TopologicalSpace.Opens M) c) :
    p.UniformGlobalPointInsertionBound (ENNReal.ofReal (2 * Real.pi)) := by
  intro P a
  let U := finitePunctureDomain P
  have hUc : (U : Set M) ⊆ c.source := fun x _ => hMc (mem_univ x)
  have hbU : b ∉ domainChartSet U c := fun h => hb ⟨h.1, mem_univ _⟩
  have hdU : d ∉ domainChartSet U c := fun h => hd ⟨h.1, mem_univ _⟩
  have hsharp := p.chart_point_removal_gain U hc hci hUc
    (hMc (mem_univ a)) hbd hbU hdU
  have hdom : punctureDomain U a = finitePunctureDomain (insert a P) := by
    ext x
    simp [U, punctureDomain, finitePunctureDomain, and_comm]
  simpa only [hdom] using hsharp

omit [LocallyCompactSpace M] in
/-- For one-point insertion, total area is exactly old total area plus the
global gain.  Both model measures ignore the finite deleted set, so the
on-domain identity extends to `univ`. -/
theorem finitePunctureDomain_area_insert_eq_add_gain
    (p : DiscCover M) (P : Finset M) (a : M) :
    p.domainArea (finitePunctureDomain (insert a P)) Set.univ =
      p.domainArea (finitePunctureDomain P) Set.univ +
        p.domainAreaGain (finitePunctureDomain P)
          (finitePunctureDomain (insert a P)) Set.univ := by
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (insert a P)
  have hVU : V ≤ U := by
    intro x hx
    exact fun hxP => hx (Finset.mem_insert_of_mem hxP)
  let : NullSingletonClass p.hyperbolicArea := p.hyperbolicArea_noAtoms
  let : NullSingletonClass (p.domainArea U) := by
    unfold domainArea
    infer_instance
  let : NullSingletonClass (p.domainArea V) := by
    unfold domainArea
    infer_instance
  have hOldVae : (V : Set M) =ᵐ[p.domainArea U] Set.univ := by
    apply ae_eq_univ.mpr
    have hz : p.domainArea U ((insert a P : Finset M) : Set M) = 0 :=
      (insert a P).finite_toSet.measure_zero (p.domainArea U)
    simpa [V, finitePunctureDomain] using hz
  have hVae : (V : Set M) =ᵐ[p.domainArea V] Set.univ := by
    apply ae_eq_univ.mpr
    have hz : p.domainArea V ((insert a P : Finset M) : Set M) = 0 :=
      (insert a P).finite_toSet.measure_zero (p.domainArea V)
    simpa [V, finitePunctureDomain] using hz
  have hEq := p.domainArea_eq_add_gain_on hVU V.isOpen.measurableSet
    (show (V : Set M) ⊆ V from fun _ hx => hx)
  have hgain : p.domainAreaGain U V (V : Set M) =
      p.domainAreaGain U V Set.univ := by
    simpa only [univ_inter] using p.domainAreaGain_inter U V Set.univ
  change p.domainArea V Set.univ =
    p.domainArea U Set.univ + p.domainAreaGain U V Set.univ
  rw [← measure_congr hVae, ← measure_congr hOldVae, ← hgain]
  exact hEq

omit [LocallyCompactSpace M] in
/-- Therefore a uniform one-point increment of total area implies the
uniform global gain estimate, provided the old finite-puncture models have
finite total mass. -/
theorem uniformGlobalPointInsertionBound_of_totalArea_increment
    (p : DiscCover M) {C : ℝ≥0∞}
    (hfinite : ∀ P : Finset M,
      p.domainArea (finitePunctureDomain P) Set.univ ≠ ⊤)
    (hincrement : ∀ (P : Finset M) (a : M),
      p.domainArea (finitePunctureDomain (insert a P)) Set.univ ≤
        p.domainArea (finitePunctureDomain P) Set.univ + C) :
    p.UniformGlobalPointInsertionBound C := by
  intro P a
  have h := hincrement P a
  rw [p.finitePunctureDomain_area_insert_eq_add_gain P a] at h
  exact ENNReal.le_of_add_le_add_left (hfinite P) h

omit [LocallyCompactSpace M] in
/-- Conversely, a global gain bound is already the corresponding total-area
increment bound.  Thus, on finite-area finite-puncture models, the global
one-point estimate and the Gauss--Bonnet-style total-area increment are
equivalent formulations of the same remaining analytic statement. -/
theorem totalArea_increment_of_uniformGlobalPointInsertionBound
    (p : DiscCover M) {C : ℝ≥0∞}
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    ∀ (P : Finset M) (a : M),
      p.domainArea (finitePunctureDomain (insert a P)) Set.univ ≤
        p.domainArea (finitePunctureDomain P) Set.univ + C := by
  intro P a
  rw [p.finitePunctureDomain_area_insert_eq_add_gain P a]
  exact add_le_add_right (hpoint P a) _

omit [LocallyCompactSpace M] in
/-- Exact equivalence between the whole-surface point-removal estimate and
the one-puncture total-area increment, when all old finite-puncture models
have finite total area. -/
theorem uniformGlobalPointInsertionBound_iff_totalArea_increment
    (p : DiscCover M) {C : ℝ≥0∞}
    (hfinite : ∀ P : Finset M,
      p.domainArea (finitePunctureDomain P) Set.univ ≠ ⊤) :
    p.UniformGlobalPointInsertionBound C ↔
      ∀ (P : Finset M) (a : M),
        p.domainArea (finitePunctureDomain (insert a P)) Set.univ ≤
          p.domainArea (finitePunctureDomain P) Set.univ + C := by
  constructor
  · exact p.totalArea_increment_of_uniformGlobalPointInsertionBound
  · exact p.uniformGlobalPointInsertionBound_of_totalArea_increment hfinite

omit [LocallyCompactSpace M] in
/-- A uniform one-point whole-surface estimate telescopes to a bound for
inserting any finite set. -/
theorem global_finitePuncture_gain_le_of_pointInsertion
    (p : DiscCover M) {C : ℝ≥0∞}
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    ∀ (P E : Finset M),
      p.domainAreaGain (finitePunctureDomain P)
          (finitePunctureDomain (P ∪ E)) Set.univ ≤
        (E.card : ℝ≥0∞) * C := by
  intro P E
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih =>
      calc
        p.domainAreaGain (finitePunctureDomain P)
            (finitePunctureDomain (P ∪ insert a E)) Set.univ ≤
            p.domainAreaGain (finitePunctureDomain P)
                (finitePunctureDomain (P ∪ E)) Set.univ +
              p.domainAreaGain (finitePunctureDomain (P ∪ E))
                (finitePunctureDomain (insert a (P ∪ E))) Set.univ := by
                  simpa only [Finset.union_insert] using
                    p.domainAreaGain_triangle
                      (finitePunctureDomain P)
                      (finitePunctureDomain (P ∪ insert a E))
                      (finitePunctureDomain (P ∪ E)) MeasurableSet.univ
        _ ≤ (E.card : ℝ≥0∞) * C + C :=
          add_le_add ih (hpoint (P ∪ E) a)
        _ = ((insert a E).card : ℝ≥0∞) * C := by
          rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one,
            add_mul, one_mul]

omit [LocallyCompactSpace M] in
/-- The measure form used by the global cancellation package. -/
theorem uniform_global_finitePuncture_insertion_area_le_of_pointInsertion
    (p : DiscCover M) (q : ℕ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hpoint : p.UniformGlobalPointInsertionBound C) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      ∀ (P E : Finset M), E.card ≤ q →
        ∀ A : Set M, MeasurableSet A →
          p.domainArea (finitePunctureDomain (P ∪ E)) A ≤
            p.domainArea (finitePunctureDomain P) A + D := by
  refine ⟨(q : ℝ≥0∞) * C,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) hC, ?_⟩
  intro P E hEq A hA
  refine (p.domainArea_le_add_gain (finitePunctureDomain P)
    (finitePunctureDomain (P ∪ E)) hA).trans ?_
  have hgain :
      p.domainAreaGain (finitePunctureDomain P)
          (finitePunctureDomain (P ∪ E)) A ≤ (q : ℝ≥0∞) * C :=
    (measure_mono (subset_univ A)).trans
      ((p.global_finitePuncture_gain_le_of_pointInsertion hpoint P E).trans (by
        gcongr))
  exact add_le_add_right hgain _

end AreaDeficit.Surfaces.DiscCover
