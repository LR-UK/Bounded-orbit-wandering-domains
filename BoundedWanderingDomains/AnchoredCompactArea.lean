/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.AnchoredCompactComparison
import BoundedWanderingDomains.CompactDeficit
import BoundedWanderingDomains.CompactCutoff

/-!
# Area gain for finite punctures away from a compact obstacle

The bound is uniform over all finite old punctures and finite new punctures
contained in a fixed compact set. This is the finite-model core of the
compact-removal theorem.
-/

open Set MeasureTheory Filter InnerProductSpace Laplacian
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

/-- One fixed cutoff and one compact separating neighbourhood give an area
bound independent of both finite puncture sets. The cutoff is allowed to
meet old punctures, which are handled by `density_deficit_on_set`. -/
theorem FinitePunctureMetricInput.uniform_finite_compact_gain
    (G : FinitePunctureMetricInput)
    {C K V W : Set ℂ} (hC : IsCompact C) (hK : IsCompact K)
    (hCK : Disjoint C K) (hV : IsOpen V) (hVC : V ⊆ C)
    (hW : MeasurableSet W)
    {a b : ℂ} (hab : a ≠ b)
    (chi : ℂ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (hc : HasCompactSupport chi) (hchi0 : ∀ x, 0 ≤ chi x)
    (hsupp : tsupport chi ⊆ V) (hchiW : ∀ x ∈ W, 1 ≤ chi x) :
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ ∀ (P Q : Finset ℂ),
      a ∈ P → b ∈ P → (↑Q : Set ℂ) ⊆ K →
      (∫⁻ x in W \ (↑P : Set ℂ),
        ENNReal.ofReal ((G.density (P ∪ Q) x)^2) -
          ENNReal.ofReal ((G.density P x)^2)) ≤ T := by
  obtain ⟨M, hM, HM⟩ := G.uniform_log_gain_away_from_compact hC hK hCK hab
  refine ⟨ENNReal.ofReal (M * ∫ x : ℂ, |Δ chi x|), ENNReal.ofReal_ne_top, ?_⟩
  intro P Q ha hb hQ
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hPQ : 2 ≤ (P ∪ Q).card :=
    hP.trans (Finset.card_le_card Finset.subset_union_left)
  have hQavoid (x : ℂ) (hx : x ∈ V) : x ∉ Q := by
    intro hxQ
    exact Set.disjoint_left.mp hCK (hVC hx) (hQ hxQ)
  have hW' : MeasurableSet (W \ (↑P : Set ℂ)) :=
    hW.diff P.finite_toSet.measurableSet
  apply density_deficit_on_set P hV hW' hM hchi hc hchi0 hsupp
    (fun x hx => hchiW x hx.1) (fun x hx => hx.2)
  · intro x hxV hxP
    have hxQ : x ∉ P ∪ Q := by
      intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hxP h
      · exact hQavoid x hxV h
    exact ⟨G.positive (P ∪ Q) hPQ x hxQ,
      ((G.smooth (P ∪ Q) hPQ).contDiffAt
        ((P ∪ Q).finite_toSet.isClosed.isOpen_compl.mem_nhds hxQ))⟩
  · intro x hxV hxP
    exact ⟨G.positive P hP x hxP,
      ((G.smooth P hP).contDiffAt
        (P.finite_toSet.isClosed.isOpen_compl.mem_nhds hxP))⟩
  · intro x hxV hxP
    have hxQ : x ∉ P ∪ Q := by
      intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hxP h
      · exact hQavoid x hxV h
    exact G.curvature (P ∪ Q) hPQ x hxQ
  · intro x _ hxP
    exact G.curvature P hP x hxP
  · intro x hxV hxP
    apply HM P Q x ha hb hQ (hVC hxV)
    intro hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hxP h
    · exact hQavoid x hxV h

/-- Fatou transfers the cutoff estimate from finite punctures to the
complements of two closed sets. The finite exhaustions are explicit here;
their existence is a separate, purely topological step. -/
theorem FinitePunctureMetricInput.uniform_closed_compact_gain_of_exhaustions
    (G : FinitePunctureMetricInput)
    {C K V W A : Set ℂ} (hK : IsCompact K)
    (hCK : Disjoint C K) (hVC : V ⊆ C)
    (hW : MeasurableSet W) (hWV : W ⊆ V) (hA : IsClosed A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {P Q : ℕ → Finset ℂ} (hP : Monotone P) (hQ : Monotone Q)
    (hPa : a ∈ P 0) (hPb : b ∈ P 0)
    (hrepA : A = closure (⋃ n, (↑(P n) : Set ℂ)))
    (hrepK : K = closure (⋃ n, (↑(Q n) : Set ℂ)))
    (T : ℝ≥0∞)
    (hT : ∀ (P Q : Finset ℂ), a ∈ P → b ∈ P → (↑Q : Set ℂ) ⊆ K →
      (∫⁻ x in W \ (↑P : Set ℂ),
        ENNReal.ofReal ((G.density (P ∪ Q) x)^2) -
          ENNReal.ofReal ((G.density P x)^2)) ≤ T) :
      (∫⁻ z in W ∩ Aᶜ,
        ENNReal.ofReal ((closedComplementDensity (A ∪ K)
          (hA.union hK.isClosed) hab (Or.inl ha) (Or.inl hb) z)^2) -
        ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2)) ≤ T := by
  have hPsub (n : ℕ) : (↑(P n) : Set ℂ) ⊆ A := by
    intro z hz
    rw [hrepA]
    exact subset_closure (mem_iUnion.mpr ⟨n, hz⟩)
  have hQsub (n : ℕ) : (↑(Q n) : Set ℂ) ⊆ K := by
    intro z hz
    rw [hrepK]
    exact subset_closure (mem_iUnion.mpr ⟨n, hz⟩)
  have hPQ : Monotone (fun n => P n ∪ Q n) := by
    intro i j hij
    exact Finset.union_subset_union (hP hij) (hQ hij)
  have hrepNew : A ∪ K =
      closure (⋃ n, (↑(P n ∪ Q n) : Set ℂ)) := by
    have hsets : (⋃ n, (↑(P n ∪ Q n) : Set ℂ)) =
        (⋃ n, (↑(P n) : Set ℂ)) ∪ (⋃ n, (↑(Q n) : Set ℂ)) := by
      ext z
      simp only [mem_iUnion, Finset.mem_coe, Finset.mem_union, mem_union]
      constructor
      · rintro ⟨n, hn | hn⟩
        · exact Or.inl ⟨n, hn⟩
        · exact Or.inr ⟨n, hn⟩
      · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
        · exact ⟨n, Or.inl hn⟩
        · exact ⟨n, Or.inr hn⟩
    rw [hsets, closure_union, ← hrepA, ← hrepK]
  let D : Set ℂ := W ∩ Aᶜ
  have hD : MeasurableSet D := hW.inter hA.isOpen_compl.measurableSet
  have hzD : ∀ᵐ z : ℂ ∂volume.restrict D, z ∈ D := ae_restrict_mem hD
  have hnonK (z : ℂ) (hz : z ∈ D) : z ∉ K := by
    exact fun hk => Set.disjoint_left.mp hCK (hVC (hWV hz.1)) hk
  have hnew : ∀ᵐ z : ℂ ∂volume.restrict D,
      Tendsto (fun n => ENNReal.ofReal ((G.density (P n ∪ Q n) z)^2))
        Filter.atTop (𝓝 (ENNReal.ofReal ((closedComplementDensity (A ∪ K)
          (hA.union hK.isClosed) hab (Or.inl ha) (Or.inl hb) z)^2))) := by
    filter_upwards [hzD] with z hz
    have ht := G.density_tendsto_closedComplement hPQ hab
      (Finset.mem_union_left _ hPa) (Finset.mem_union_left _ hPb)
      (show z ∉ closure (⋃ n, (↑(P n ∪ Q n) : Set ℂ)) from
        hrepNew ▸ (fun hh : z ∈ A ∪ K => hh.elim hz.2 (hnonK z hz)))
    simpa only [← hrepNew] using ENNReal.tendsto_ofReal (ht.pow 2)
  have hold : ∀ᵐ z : ℂ ∂volume.restrict D,
      Tendsto (fun n => ENNReal.ofReal ((G.density (P n) z)^2)) Filter.atTop
        (𝓝 (ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2))) := by
    filter_upwards [hzD] with z hz
    have ht := G.density_tendsto_closedComplement hP hab hPa hPb
      (show z ∉ closure (⋃ n, (↑(P n) : Set ℂ)) from hrepA ▸ hz.2)
    simpa only [← hrepA] using ENNReal.tendsto_ofReal (ht.pow 2)
  have hcard (n : ℕ) : 2 ≤ (P n).card := by
    have htwo : ({a, b} : Finset ℂ).card = 2 := by simp [hab]
    rw [← htwo]
    exact Finset.card_le_card (Finset.insert_subset_iff.mpr
      ⟨(hP (Nat.zero_le n)) hPa,
        Finset.singleton_subset_iff.mpr ((hP (Nat.zero_le n)) hPb)⟩)
  have hmeas (n : ℕ) : Measurable (fun z => ENNReal.ofReal ((G.density (P n) z)^2)) :=
    ((G.measurable_density (hcard n)).pow_const 2).ennreal_ofReal
  have hmeasNew (n : ℕ) :
      Measurable (fun z => ENNReal.ofReal ((G.density (P n ∪ Q n) z)^2)) :=
    ((G.measurable_density ((hcard n).trans
      (Finset.card_le_card Finset.subset_union_left))).pow_const 2).ennreal_ofReal
  refine limiting_gain_bound
    (fun n => (hmeasNew n).aemeasurable)
    (fun n => (hmeas n).aemeasurable)
    hnew hold (Filter.Eventually.of_forall (fun z => Or.inr ENNReal.ofReal_ne_top)) ?_
  intro n
  calc
    (∫⁻ z in D, ENNReal.ofReal ((G.density (P n ∪ Q n) z)^2) -
        ENNReal.ofReal ((G.density (P n) z)^2)) ≤
      ∫⁻ z in W \ (↑(P n) : Set ℂ),
        ENNReal.ofReal ((G.density (P n ∪ Q n) z)^2) -
          ENNReal.ofReal ((G.density (P n) z)^2) := by
        apply lintegral_mono_set
        intro z hz
        exact ⟨hz.1, fun hp => hz.2 (hPsub n hp)⟩
    _ ≤ T := hT (P n) (Q n) ((hP (Nat.zero_le n)) hPa)
      ((hP (Nat.zero_le n)) hPb) (hQsub n)

/-- The finite exhaustions are supplied automatically for arbitrary closed
plane obstacles. The bound depends on the separating compact set and cutoff,
and is independent of the old closed obstacle. -/
theorem FinitePunctureMetricInput.uniform_closed_compact_gain
    (G : FinitePunctureMetricInput)
    {C K V W : Set ℂ} (hC : IsCompact C) (hK : IsCompact K)
    (hCK : Disjoint C K) (hV : IsOpen V) (hVC : V ⊆ C)
    (hW : MeasurableSet W) (hWV : W ⊆ V)
    {a b : ℂ} (hab : a ≠ b)
    (chi : ℂ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (hc : HasCompactSupport chi) (hchi0 : ∀ x, 0 ≤ chi x)
    (hsupp : tsupport chi ⊆ V) (hchiW : ∀ x ∈ W, 1 ≤ chi x) :
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ ∀ (A : Set ℂ) (hA : IsClosed A)
      (ha : a ∈ A) (hb : b ∈ A),
      (∫⁻ z in W ∩ Aᶜ,
        ENNReal.ofReal ((closedComplementDensity (A ∪ K)
          (hA.union hK.isClosed) hab (Or.inl ha) (Or.inl hb) z)^2) -
        ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2)) ≤ T := by
  obtain ⟨T, hTf, hT⟩ := G.uniform_finite_compact_gain hC hK hCK hV hVC
    hW hab chi hchi hc hchi0 hsupp hchiW
  refine ⟨T, hTf, ?_⟩
  intro A hA ha hb
  obtain ⟨P, hP, hPa, hPb, hrepA⟩ :=
    exists_finite_exhaustion_closed A hA ha hb
  obtain ⟨Q, hQ, hrepK⟩ := exists_finite_exhaustion_closed_unanchored K hK.isClosed
  exact G.uniform_closed_compact_gain_of_exhaustions hK hCK hVC hW hWV
    hA hab ha hb hP hQ hPa hPb hrepA hrepK T hT

/-- A finite area-gain bound for arbitrary closed old obstacles containing
two fixed anchors. Only the two disjoint compact sets and the anchors enter
the bound; the old obstacle can vary freely. -/
theorem uniform_closed_compact_gain_anchored
    {W K : Set ℂ} (hW : IsCompact W) (hK : IsCompact K)
    (hWK : Disjoint W K) {a b : ℂ} (hab : a ≠ b) :
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ ∀ (A : Set ℂ) (hA : IsClosed A)
      (ha : a ∈ A) (hb : b ∈ A),
      (∫⁻ z in W ∩ Aᶜ,
        ENNReal.ofReal ((closedComplementDensity (A ∪ K)
          (hA.union hK.isClosed) hab (Or.inl ha) (Or.inl hb) z)^2) -
        ENNReal.ofReal ((closedComplementDensity A hA hab ha hb z)^2)) ≤ T := by
  have hWK' : W ⊆ Kᶜ := by
    intro z hz hzK
    exact Set.disjoint_left.mp hWK hz hzK
  obtain ⟨V, hV, hWV, hVavoid, hVc⟩ :=
    exists_open_between_and_isCompact_closure hW hK.isClosed.isOpen_compl hWK'
  obtain ⟨chi, hchi, hc, hsupp, hchi0, hchiW⟩ :=
    exists_compact_cutoff hW hV hWV
  have hCK : Disjoint (closure V) K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    exact hVavoid hz hzK
  exact canonicalFinitePunctureMetricInput.uniform_closed_compact_gain
    hVc hK hCK hV subset_closure hW.measurableSet hWV hab
    chi hchi hc hchi0 hsupp hchiW

end AreaDeficit
