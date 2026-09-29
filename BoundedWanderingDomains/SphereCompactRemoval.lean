module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SpherePointRemoval
public import BoundedWanderingDomains.SpherePole
public import BoundedWanderingDomains.SphereChartCompact
public import BoundedWanderingDomains.AreaGainSubadditivity

@[expose] public section

/-!
# Uniform compact-removal area bound on the sphere

For disjoint compact sphere sets `K` and `L`, deleting `K` from any
hyperbolic sphere domain produces a uniformly bounded gain of curvature −1
hyperbolic area on `L`.  The constant is independent of the old domain.
-/

open Set Function OnePoint MeasureTheory Filter
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

private theorem inter_compl_union_eq_of_disjoint
    {X K A : Set (OnePoint ℂ)} (hXK : Disjoint X K) :
    X ∩ (A ∪ K)ᶜ = X ∩ Aᶜ := by
  ext z
  constructor
  · exact fun hz => ⟨hz.1, fun hzA => hz.2 (Or.inl hzA)⟩
  · rintro ⟨hzX, hzA⟩
    refine ⟨hzX, ?_⟩
    rintro (hzA' | hzK)
    · exact hzA hzA'
    · exact Set.disjoint_left.mp hXK hzX hzK

/-- Uniform bound for compact removal on arbitrary hyperbolic sphere
domains, expressed intrinsically through the chart-independent area gain. -/
theorem uniform_compact_gain_sphere
    {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ (A : Set (OnePoint ℂ)) (hA : IsClosed A)
        (D : SphereHyperbolicMetricData A),
        sphereHyperbolicAreaGain A hA (A ∪ K)
          (hA.union hK.isClosed) subset_union_left D L ≤ M := by
  by_cases hKe : K = ∅
  · subst K
    refine ⟨0, by simp, ?_⟩
    intro A hA D
    simp only [union_empty]
    unfold sphereHyperbolicAreaGain
    simp
  by_cases hLe : L = ∅
  · subst L
    refine ⟨0, by simp, ?_⟩
    intro A hA D
    unfold sphereHyperbolicAreaGain
    simp
  have hKn : K.Nonempty := nonempty_iff_ne_empty.mpr hKe
  have hLn : L.Nonempty := nonempty_iff_ne_empty.mpr hLe
  obtain ⟨p, hp⟩ := exists_sphere_pole_avoiding_compacts hK hL hKL hKn hLn
  have hpK : p ∉ K := fun h => hp (Or.inl h)
  have hpL : p ∉ L := fun h => hp (Or.inr h)
  obtain ⟨T, hTtop, hT⟩ := uniform_compact_gain_in_pole_chart
    hK hL hKL hpK hpL
  let cost : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  refine ⟨T + cost, ENNReal.add_ne_top.mpr ⟨hTtop, ENNReal.ofReal_ne_top⟩, ?_⟩
  intro A hA D
  let P : Set (OnePoint ℂ) := A ∪ {p}
  let B : Set (OnePoint ℂ) := A ∪ K
  let Q : Set (OnePoint ℂ) := P ∪ K
  have hP : IsClosed P := hA.union isClosed_singleton
  have hB : IsClosed B := hA.union hK.isClosed
  have hQ : IsClosed Q := hP.union hK.isClosed
  let F : SphereHyperbolicMetricData P := D.mono subset_union_left
  let E : SphereHyperbolicMetricData P := D.insertAt p
  have hLP : L ∩ Pᶜ = L ∩ Aᶜ := by
    apply inter_compl_union_eq_of_disjoint
    exact Set.disjoint_singleton_right.mpr hpL
  have hLB : L ∩ Bᶜ = L ∩ Aᶜ :=
    inter_compl_union_eq_of_disjoint hKL.symm
  have hLQ : L ∩ Qᶜ = L ∩ Pᶜ :=
    inter_compl_union_eq_of_disjoint hKL.symm
  let S : Set ℂ := (spherePoleChart D.pole) ⁻¹' (L ∩ Aᶜ)
  have hS : MeasurableSet S := by
    apply (hL.measurableSet.inter hA.measurableSet.compl).preimage
    exact Continuous.measurable (continuousOn_univ.mp (by
      simpa using (spherePoleChart D.pole).continuousOn))
  have hBQ : B ⊆ Q := by
    rintro z (hzA | hzK)
    · exact Or.inl (Or.inl hzA)
    · exact Or.inr hzK
  have hpoint : ∀ᵐ z : ℂ ∂volume.restrict S,
      hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
          (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
          (show D.anchorOne ∈ (spherePoleChart D.pole) ⁻¹' B from Or.inl D.anchorOne_mem)
          (show D.anchorTwo ∈ (spherePoleChart D.pole) ⁻¹' B from Or.inl D.anchorTwo_mem) z ≤
        hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' Q)
          (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
          (show D.anchorOne ∈ (spherePoleChart D.pole) ⁻¹' Q from Or.inl (Or.inl D.anchorOne_mem))
          (show D.anchorTwo ∈ (spherePoleChart D.pole) ⁻¹' Q from Or.inl (Or.inl D.anchorTwo_mem)) z := by
    filter_upwards [ae_restrict_mem hS] with z hz
    have hpre : (spherePoleChart D.pole) ⁻¹' B ⊆
        (spherePoleChart D.pole) ⁻¹' Q := preimage_mono hBQ
    have hzQ : z ∉ (spherePoleChart D.pole) ⁻¹' Q := by
      rintro (hzP | hzK)
      · rcases hzP with hzA | hzp
        · exact hz.2 hzA
        · exact hpL (by simpa only [mem_singleton_iff] using hzp ▸ hz.1)
      · exact Set.disjoint_left.mp hKL hzK hz.1
    exact hyperbolicAreaWeight_mono_any _ _
      (closed_sphere_set_in_pole_chart hB D.pole)
      (closed_sphere_set_in_pole_chart hQ D.pole) hpre
      D.anchor_ne D.anchor_ne (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem)
      (Or.inl (Or.inl D.anchorOne_mem)) (Or.inl (Or.inl D.anchorTwo_mem)) hzQ
  have hmeas : AEMeasurable (fun z =>
      hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' Q)
          (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
          (Or.inl (Or.inl D.anchorOne_mem)) (Or.inl (Or.inl D.anchorTwo_mem)) z -
        hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
          (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
          (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z)
      (volume.restrict S) := by
    exact ((((measurable_closedComplementDensity
      ((spherePoleChart D.pole) ⁻¹' Q)
      (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
      (Or.inl (Or.inl D.anchorOne_mem))
      (Or.inl (Or.inl D.anchorTwo_mem))).pow_const 2).ennreal_ofReal).sub
      (((measurable_closedComplementDensity
        ((spherePoleChart D.pole) ⁻¹' P)
        (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
        (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem)).pow_const 2).ennreal_ofReal)).aemeasurable
  have hsub := lintegral_gain_le_gain_add_gain
    (hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
      (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
      (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem))
    (hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' Q)
      (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
      (Or.inl (Or.inl D.anchorOne_mem)) (Or.inl (Or.inl D.anchorTwo_mem)))
    (hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
      (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
      (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem))
    (hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
      (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
      D.anchorOne_mem D.anchorTwo_mem) hpoint hmeas
  have hauxE : sphereHyperbolicAreaGain P hP Q hQ subset_union_left E L ≤ T := by
    have hEpole : E.pole = p := by
      dsimp only [E]
      exact SphereHyperbolicMetricData.insertAt_pole D p
    have hEone : E.anchorOne ∈ (spherePoleChart p) ⁻¹' P := by
      simpa only [hEpole] using E.anchorOne_mem
    have hEtwo : E.anchorTwo ∈ (spherePoleChart p) ⁻¹' P := by
      simpa only [hEpole] using E.anchorTwo_mem
    have ht := hT ((spherePoleChart p) ⁻¹' P)
      (closed_sphere_set_in_pole_chart hP p)
      E.anchor_ne hEone hEtwo
    unfold sphereHyperbolicAreaGain
    simpa only [hEpole, Q, hLQ, preimage_inter, preimage_compl, preimage_union] using ht
  have hauxF : sphereHyperbolicAreaGain P hP Q hQ subset_union_left F L ≤ T := by
    calc
      sphereHyperbolicAreaGain P hP Q hQ subset_union_left F L =
          sphereHyperbolicAreaGain P hP Q hQ subset_union_left E L :=
        sphereHyperbolicAreaGain_independent hP hQ subset_union_left
          hL.measurableSet F E
      _ ≤ T := hauxE
  have hpunct : sphereHyperbolicAreaGain A hA P hP subset_union_left D Set.univ ≤ cost := by
    by_cases hpA : p ∈ A
    · have hPA : P = A := by
        apply union_eq_left.mpr
        simpa only [singleton_subset_iff] using hpA
      have hzero : sphereHyperbolicAreaGain A hA P hP subset_union_left D Set.univ = 0 := by
        unfold sphereHyperbolicAreaGain
        simp only [hPA, tsub_self, lintegral_zero]
      exact hzero.le.trans bot_le
    · exact sphere_point_removal_gain_le_two_pi hA D hpA
  have hpunctS :
      (∫⁻ z in S,
        hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
            (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
            (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z -
          hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
            (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
            D.anchorOne_mem D.anchorTwo_mem z) ≤ cost := by
    calc
      _ ≤ ∫⁻ z in (spherePoleChart D.pole) ⁻¹' Pᶜ,
          hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
              (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
              (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z -
            hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
              (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
              D.anchorOne_mem D.anchorTwo_mem z := by
        apply lintegral_mono_set
        intro z hz
        have hzSphere : spherePoleChart D.pole z ∈ L ∩ Aᶜ := hz
        change spherePoleChart D.pole z ∉ P
        intro hzP
        rcases hzP with hzA | hzp
        · exact hzSphere.2 hzA
        · exact hpL (by simpa only [mem_singleton_iff] using hzp ▸ hzSphere.1)
      _ ≤ cost := by
        simpa only [sphereHyperbolicAreaGain, univ_inter, preimage_compl] using hpunct
  have hmain :
      sphereHyperbolicAreaGain A hA B hB subset_union_left D L ≤
        sphereHyperbolicAreaGain P hP Q hQ subset_union_left F L + cost := by
    have htargetEq : sphereHyperbolicAreaGain A hA B hB subset_union_left D L =
        (∫⁻ z in S,
      hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
          (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
          (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z -
        hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
          (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
          D.anchorOne_mem D.anchorTwo_mem z) := by
      unfold sphereHyperbolicAreaGain
      rw [hLB]
    have hauxEq :
        (∫⁻ z in S,
          hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' Q)
              (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
              (Or.inl (Or.inl D.anchorOne_mem)) (Or.inl (Or.inl D.anchorTwo_mem)) z -
            hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
              (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
              (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z) =
          sphereHyperbolicAreaGain P hP Q hQ subset_union_left F L := by
      unfold sphereHyperbolicAreaGain
      dsimp only [F, SphereHyperbolicMetricData.mono]
      rw [hLQ, hLP]
    calc
      sphereHyperbolicAreaGain A hA B hB subset_union_left D L =
          (∫⁻ z in S,
            hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
                (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
                (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z -
              hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
                (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
                D.anchorOne_mem D.anchorTwo_mem z) := htargetEq
      _ ≤ (∫⁻ z in S,
          hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' Q)
              (closed_sphere_set_in_pole_chart hQ D.pole) D.anchor_ne
              (Or.inl (Or.inl D.anchorOne_mem)) (Or.inl (Or.inl D.anchorTwo_mem)) z -
            hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
              (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
              (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z) +
          (∫⁻ z in S,
            hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' P)
                (closed_sphere_set_in_pole_chart hP D.pole) D.anchor_ne
                (Or.inl D.anchorOne_mem) (Or.inl D.anchorTwo_mem) z -
              hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
                (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
                D.anchorOne_mem D.anchorTwo_mem z) := hsub
      _ ≤ sphereHyperbolicAreaGain P hP Q hQ subset_union_left F L + cost := by
        apply add_le_add _ hpunctS
        exact hauxEq.le
  exact hmain.trans (add_le_add hauxF le_rfl)

end AreaDeficit
