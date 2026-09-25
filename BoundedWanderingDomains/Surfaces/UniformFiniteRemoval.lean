/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactFiniteRemoval
import BoundedWanderingDomains.Surfaces.DomainArea
import BoundedWanderingDomains.Surfaces.SmallChartDomain

/-! # Uniform finite-puncture budgets on compact surface sets

The sharp `2π` chart estimate is combined with two fixed localisation
budgets.  The resulting point-removal constant is locally uniform in the
puncture.  A finite cover near the measured compact set and one remote
estimate then make it uniform on the whole surface. -/

open Set Function Filter MeasureTheory Metric
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A chart core gives a point-removal budget uniform for all punctures in
the smaller core.  The larger core separates the remaining measured set
from every such puncture. -/
theorem compact_point_removal_gain_on_core (p : DiscCover M)
    {L C₀ C₁ : Set M} (hL : IsCompact L) (hC₀ : IsCompact C₀)
    (hC₁ : IsCompact C₁) (hC₀C₁ : C₀ ⊆ interior C₁)
    (D : TopologicalSpace.Opens M) (hC₁D : C₁ ⊆ D)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c.symm c.target)
    (hDc : (D : Set M) ⊆ c.source)
    {b d : ℂ} (hbd : b ≠ d)
    (hb : b ∉ domainChartSet D c) (hd : d ∉ domainChartSet D c) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ a ∈ C₀, ∀ U : TopologicalSpace.Opens M,
      p.domainAreaGain U (punctureDomain U a) L ≤ B := by
  obtain ⟨B₀,hB₀,hlocal⟩ := p.compact_localization_domainAreaGain D hC₁ hC₁D
  let R := L \ interior C₁
  have hR : IsCompact R := hL.diff isOpen_interior
  have hRC₀ : Disjoint R C₀ := disjoint_left.mpr (by
    intro x hxR hxC₀
    exact hxR.2 (hC₀C₁ hxC₀))
  obtain ⟨B₁,hB₁,hremote⟩ := p.compact_localization_domainAreaGain
    ⟨C₀ᶜ,hC₀.isClosed.isOpen_compl⟩ hR
      (fun x hxR hxC₀ => disjoint_left.mp hRC₀ hxR hxC₀)
  refine ⟨(B₀ + ENNReal.ofReal (2 * Real.pi)) + B₁,
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hB₀,ENNReal.ofReal_ne_top⟩,hB₁⟩,?_⟩
  intro a ha U
  let V := punctureDomain U a
  let W := U ⊓ D
  let Z := punctureDomain W a
  have hZV : Z ≤ V := fun _ hx => ⟨hx.1.1,hx.2⟩
  have hC₁Z : C₁ ∩ V ⊆ Z := by
    rintro x ⟨hxC₁,hxV⟩
    exact ⟨⟨hxV.1,hC₁D hxC₁⟩,hxV.2⟩
  have hWc : (W : Set M) ⊆ c.source := fun _ hx => hDc hx.2
  have hbW : b ∉ domainChartSet W c := fun h => hb ⟨h.1,h.2.2⟩
  have hdW : d ∉ domainChartSet W c := fun h => hd ⟨h.1,h.2.2⟩
  have hsharp := p.chart_point_removal_gain W hc hci hWc
    (hDc (hC₁D (interior_subset (hC₀C₁ ha)))) hbd hbW hdW
  have hnear : p.domainAreaGain U V C₁ ≤
      B₀ + ENNReal.ofReal (2 * Real.pi) := by
    calc
      p.domainAreaGain U V C₁ ≤
          p.domainAreaGain U W C₁ + p.domainAreaGain W Z C₁ :=
        p.domainAreaGain_localize U V W Z hZV hC₁.measurableSet hC₁Z
      _ ≤ B₀ + ENNReal.ofReal (2 * Real.pi) :=
        add_le_add (hlocal U) ((measure_mono (subset_univ C₁)).trans hsharp)
  let T : TopologicalSpace.Opens M := U ⊓ ⟨C₀ᶜ,hC₀.isClosed.isOpen_compl⟩
  have hTV : T ≤ V := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxa
    exact hx.2 (hxa ▸ ha)
  have hRVT : R ∩ V ⊆ T := by
    rintro x ⟨hxR,hxV⟩
    refine ⟨hxV.1,?_⟩
    intro hxC₀
    exact hxR.2 (hC₀C₁ hxC₀)
  have hfar : p.domainAreaGain U V R ≤ B₁ :=
    (p.domainAreaGain_mono_right_on U T V hTV hR.measurableSet hRVT).trans
      (hremote U)
  calc
    p.domainAreaGain U V L ≤ p.domainAreaGain U V (C₁ ∪ R) := by
      apply measure_mono
      intro x hx
      by_cases hxC₁ : x ∈ C₁
      · exact Or.inl hxC₁
      · exact Or.inr ⟨hx,fun hi => hxC₁ (interior_subset hi)⟩
    _ ≤ p.domainAreaGain U V C₁ + p.domainAreaGain U V R := measure_union_le _ _
    _ ≤ _ := add_le_add hnear hfar

/-- One finite point-removal budget works simultaneously for every puncture
and every old open domain.  The bound depends only on the measured compact
set and the ambient surface. -/
theorem uniform_compact_point_removal_gain (p : DiscCover M)
    {L : Set M} (hL : IsCompact L) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (a : M) (U : TopologicalSpace.Opens M),
      p.domainAreaGain U (punctureDomain U a) L ≤ B := by
  classical
  obtain ⟨Q,hQ,hLQ,_⟩ :=
    exists_compact_between hL isOpen_univ (subset_univ L)
  let c : Q → OpenPartialHomeomorph M ℂ := fun x => chartAt ℂ (x : M)
  have hsmall (x : Q) := exists_small_chart_domain
    (c := c x) (mem_chart_source ℂ (x : M))
  choose D hxD hDc b d hbd hb hd using hsmall
  have houter (x : Q) : ∃ C₁ : Set M, IsCompact C₁ ∧
      (x : M) ∈ interior C₁ ∧ C₁ ⊆ D x :=
    exists_compact_subset (D x).isOpen (hxD x)
  choose C₁ hC₁ hxC₁ hC₁D using houter
  have hinner (x : Q) : ∃ C₀ : Set M, IsCompact C₀ ∧
      (x : M) ∈ interior C₀ ∧ C₀ ⊆ interior (C₁ x) :=
    exists_compact_subset isOpen_interior (hxC₁ x)
  choose C₀ hC₀ hxC₀ hC₀C₁ using hinner
  have hcover : Q ⊆ ⋃ x : Q, interior (C₀ x) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hxC₀ ⟨y,hy⟩⟩
  obtain ⟨I,hQI⟩ := hQ.elim_finite_subcover
    (fun x : Q => interior (C₀ x)) (fun _ => isOpen_interior) hcover
  have hlocal (x : Q) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ a ∈ C₀ x, ∀ U : TopologicalSpace.Opens M,
        p.domainAreaGain U (punctureDomain U a) L ≤ B :=
    p.compact_point_removal_gain_on_core hL (hC₀ x) (hC₁ x)
      (hC₀C₁ x) (D x) (hC₁D x)
      (mdifferentiable_chart (I := 𝓘(ℂ)) (x : M)).1
      (mdifferentiable_chart (I := 𝓘(ℂ)) (x : M)).2
      (hDc x) (hbd x) (hb x) (hd x)
  choose B hB hbound using hlocal
  obtain ⟨R,hR,hfar⟩ := p.compact_localization_domainAreaGain
    ⟨interior Q,isOpen_interior⟩ hL hLQ
  refine ⟨R + ∑ x ∈ I, B x,
    ENNReal.add_ne_top.mpr ⟨hR,ENNReal.sum_ne_top.mpr (fun x _ => hB x)⟩,?_⟩
  intro a U
  by_cases haQ : a ∈ Q
  · obtain ⟨x,hxI,hax⟩ := mem_iUnion₂.mp (hQI haQ)
    exact (hbound x a (interior_subset hax) U).trans
      (le_add_of_le_right (Finset.single_le_sum
        (fun _ _ => bot_le) hxI))
  · let T : TopologicalSpace.Opens M := U ⊓ ⟨interior Q,isOpen_interior⟩
    let V := punctureDomain U a
    have hTV : T ≤ V := by
      intro x hx
      refine ⟨hx.1,?_⟩
      intro hxa
      exact haQ (hxa ▸ interior_subset hx.2)
    have hLVT : L ∩ V ⊆ T := by
      rintro x ⟨hxL,hxV⟩
      exact ⟨hxV.1,hLQ hxL⟩
    exact (p.domainAreaGain_mono_right_on U T V hTV hL.measurableSet hLVT).trans
      ((hfar U).trans (le_add_right (le_refl R)))

/-- The uniform point budget adds under successive removals.  Hence the
constant for a finite exceptional set depends only on its cardinality. -/
theorem uniform_compact_finite_removal_gain (p : DiscCover M)
    (q : ℕ) {L : Set M} (hL : IsCompact L) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (E : Finset M), E.card ≤ q →
      ∀ U : TopologicalSpace.Opens M,
        p.domainAreaGain U (finiteRemovalDomain U E) L ≤ B := by
  classical
  obtain ⟨C,hC,hpoint⟩ := p.uniform_compact_point_removal_gain hL
  have hfinite : ∀ (E : Finset M) (U : TopologicalSpace.Opens M),
      p.domainAreaGain U (finiteRemovalDomain U E) L ≤ (E.card : ℝ≥0∞) * C := by
    intro E
    induction E using Finset.induction_on with
    | empty =>
        intro U
        simp
    | @insert a E ha ih =>
        intro U
        rw [finiteRemovalDomain_insert]
        calc
          p.domainAreaGain U (punctureDomain (finiteRemovalDomain U E) a) L ≤
              p.domainAreaGain U (finiteRemovalDomain U E) L +
                p.domainAreaGain (finiteRemovalDomain U E)
                  (punctureDomain (finiteRemovalDomain U E) a) L :=
            p.domainAreaGain_triangle U _ (finiteRemovalDomain U E) hL.measurableSet
          _ ≤ (E.card : ℝ≥0∞) * C + C :=
            add_le_add (ih U) (hpoint a (finiteRemovalDomain U E))
          _ = ((insert a E).card : ℝ≥0∞) * C := by
            rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, add_mul,
              one_mul]
  refine ⟨(q : ℝ≥0∞) * C, ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) hC, ?_⟩
  intro E hEq U
  refine (hfinite E U).trans ?_
  gcongr

/-- Fixed-hyperbolic-ambient form of the paper's compact area-gain lemma:
after deleting a fixed remote compact obstacle and at most q further points,
the gain on L is bounded independently of the old open domain and of the
points.  The supplied ambient disc cover is fixed before the constant. -/
theorem uniform_compact_finite_remote_removal_gain (p : DiscCover M)
    (q : ℕ) {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (E : Finset M), E.card ≤ q →
      ∀ U : TopologicalSpace.Opens M,
        p.domainAreaGain U
          (finiteRemovalDomain U E ⊓ ⟨Kᶜ,hK.isClosed.isOpen_compl⟩) L ≤ B := by
  obtain ⟨B,hB,hfinite⟩ := p.uniform_compact_finite_removal_gain q hL
  obtain ⟨C,hC,hremote⟩ := p.compact_localization_domainAreaGain
    ⟨Kᶜ,hK.isClosed.isOpen_compl⟩ hL
      (fun x hxL hxK => disjoint_left.mp hLK hxL hxK)
  refine ⟨B + C, ENNReal.add_ne_top.mpr ⟨hB,hC⟩, ?_⟩
  intro E hEq U
  exact (p.domainAreaGain_triangle U _ (finiteRemovalDomain U E)
    hL.measurableSet).trans (add_le_add (hfinite E hEq U)
      (hremote (finiteRemovalDomain U E)))

/-- Area-mass formulation of the uniform gain theorem. -/
theorem uniform_compact_finite_remote_area (p : DiscCover M)
    (q : ℕ) {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (E : Finset M), E.card ≤ q →
      ∀ (U : TopologicalSpace.Opens M) (A : Set M), MeasurableSet A →
        A ⊆ L →
        p.domainArea
          (finiteRemovalDomain U E ⊓ ⟨Kᶜ,hK.isClosed.isOpen_compl⟩) A ≤
          p.domainArea U A + B := by
  obtain ⟨B,hB,hgain⟩ :=
    p.uniform_compact_finite_remote_removal_gain q hK hL hLK
  refine ⟨B,hB,?_⟩
  intro E hEq U A hA hAL
  exact (p.domainArea_le_add_gain U _ hA).trans
    (add_le_add_right ((measure_mono hAL).trans (hgain E hEq U)) _)

/-- On one fixed hyperbolic ambient surface the constant is independent of
the chosen universal disc cover. -/
theorem uniform_compact_finite_remote_removal_gain_all_covers
    (p₀ : DiscCover M) (q : ℕ) {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L) (hLK : Disjoint L K) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (p : DiscCover M) (E : Finset M), E.card ≤ q →
      ∀ U : TopologicalSpace.Opens M,
        p.domainAreaGain U
          (finiteRemovalDomain U E ⊓ ⟨Kᶜ,hK.isClosed.isOpen_compl⟩) L ≤ B := by
  obtain ⟨B,hB,hbound⟩ :=
    p₀.uniform_compact_finite_remote_removal_gain q hK hL hLK
  refine ⟨B,hB,?_⟩
  intro p E hEq U
  rw [p.domainAreaGain_independent p₀]
  exact hbound E hEq U

end AreaDeficit.Surfaces.DiscCover
