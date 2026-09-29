module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.DerivedSetAreaContradiction
public import BoundedWanderingDomains.LocalCoveringArea

@[expose] public section

/-! # Derived singular accumulation from local finite models -/

open Set Metric Function Filter MeasureTheory OnePoint
open scoped Topology ENNReal

namespace AreaDeficit
open BoundedWanderingDomains

theorem not_disjoint_cluster_localSingularDerivedSet_of_finite_models
    {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n)) (hUV : ∀ n, U n ⊆ V)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hznext : ∀ n, f (z n) = z (n + 1))
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (Q : Finset ℂ)
    (hforward : ∀ j x, x ∈ V → x ∈ P j → f x ∈ (↑(P j) : Set ℂ) ∪ (↑Q : Set ℂ))
    (hcomp : ∀ n, connectedComponentIn
      (closure (⋃ j, (↑(P j) : Set ℂ)))ᶜ (z n) = U n) :
    ¬ Disjoint (sphericalDerivedSet (ComplexDynamics.singularValuesOn f V))
      (sphericalClusterSet (fun n => (z n : OnePoint ℂ))) := by
  classical
  intro hsep
  let S₀ := ComplexDynamics.singularValuesOn f V
  let S := S₀ ∪ (↑Q : Set ℂ)
  have hS : IsClosed S := (ComplexDynamics.isClosed_singularValuesOn f V).union Q.finite_toSet.isClosed
  obtain ⟨K, L, hK, hL, hKL, hDK, hCL⟩ :=
    exists_disjoint_compact_sphere_neighborhoods
      (isCompact_univ.of_isClosed_subset (isClosed_sphericalDerivedSet S₀) (subset_univ _))
      (isCompact_sphericalClusterSet _) hsep
  let ES := {w : ℂ | w ∈ S₀ ∧ (w : OnePoint ℂ) ∉ interior K}
  have hES : ES.Finite :=
    finite_planar_outside_spherical_derived_neighbourhood S₀ (interior K) isOpen_interior hDK
  let E := hES.toFinset ∪ Q
  have hSE : ∀ w ∈ S, (w : OnePoint ℂ) ∈ K ∨ w ∈ E := by
    intro w hw
    rcases hw with hw | hwQ
    · by_cases hwK : (w : OnePoint ℂ) ∈ interior K
      · exact Or.inl (interior_subset hwK)
      · exact Or.inr (Finset.mem_union_left Q (hES.mem_toFinset.mpr ⟨hw, hwK⟩))
    · exact Or.inr (Finset.mem_union_right hES.toFinset hwQ)
  obtain ⟨C, hC, hgain⟩ := uniform_singular_gain_finite_models hK hL hKL E hS hSE
  let H := ENNReal.ofReal (2 * Real.pi) * C
  have hH : H ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hUP : ∀ n j, Disjoint (U n) (↑(P j) : Set ℂ) := by
    intro n j
    apply disjoint_left.mpr
    intro w hw hwP
    rw [← hcomp n] at hw
    exact (connectedComponentIn_subset _ _ hw)
      (subset_closure (mem_iUnion.mpr ⟨j, hwP⟩))
  apply no_uniform_disc_area_bound H.toReal
  intro r hr hr1
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hshrink := eventually_chartDisc_subset_cluster_neighbourhood
    hU hu hub hz hu0 hdis isOpen_interior hCL hr hr1
  have hshrink' : ∀ᶠ n in atTop,
      ∀ w ∈ chartDisc (u n) (U n) r, (w : OnePoint ℂ) ∈ L := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hshrink
    refine eventually_atTop.mpr ⟨N + 1, ?_⟩
    intro n hn w hw
    have h := hN (n - 1) (by omega)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
    exact interior_subset (h ⟨w, hw, rfl⟩)
  have havoidS := eventually_chartDisc_avoid_of_cluster_disjoint_sphericalDerivedSet
    S₀ hU hu hub hz hu0 hdis hsep hr hr1
  have hinj : ∀ᶠ n in atTop, InjOn f (chartDisc (u n) (U n) r) := by
    filter_upwards [havoidS] with n hn
    have hsource := chartDisc_isOpen (hU n) (hu n) r
    have htarget := chartDisc_isOpen (hU (n+1)) (hu (n+1)) r
    have hsrcSC := chartDisc_isSimplyConnected (hU n) (hu n) (hub n) hr hr1
    have htgtSC := chartDisc_isSimplyConnected (hU (n+1)) (hu (n+1)) (hub (n+1)) hr hr1
    have hzD : z n ∈ chartDisc (u n) (U n) r := by
      refine ⟨hz n, ?_⟩
      simpa only [mem_preimage, hu0 n] using (mem_ball_self hr : (0 : ℂ) ∈ ball 0 r)
    have hm := mapsTo_chartDisc (hU n) (hu n) (hub n) (hu (n+1))
      (hub (n+1)).mapsTo (hf.differentiableOn.mono (hUV n)) (hfm n)
      (hz n) (hu0 n) (by rw [hznext n, hu0 (n+1)]) hr1
    apply covering_injOn_domain hsource hsrcSC htarget htgtSC hzD
      (inter_subset_left.trans (hUV n))
      (hf.continuousOn.mono (inter_subset_left.trans (hUV n))) hm
    apply (ComplexDynamics.isCoveringMapOn_compl_singularValuesOn f V).mono
    intro w hw hsing
    exact disjoint_left.mp hn hw hsing
  have havoidE := eventually_components_avoid_finite_set U hdis E
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hshrink'.and (hinj.and havoidE))
  let D := fun n => chartDisc (u n) (U n) r
  let W : Set ℂ := ⋃ n ≥ N, D n
  have hDo : ∀ n, IsOpen (D n) := fun n => chartDisc_isOpen (hU n) (hu n) r
  have hWo : IsOpen W := isOpen_iUnion fun n => isOpen_iUnion fun _ => hDo n
  have hBW : D N ⊆ W := fun w hw => mem_iUnion₂.mpr ⟨N, le_rfl, hw⟩
  have hDf : ∀ n, MapsTo f (D n) (D (n + 1)) := by
    intro n
    apply mapsTo_chartDisc (hU n) (hu n) (hub n) (hu (n + 1)) (hub (n + 1)).mapsTo
      (hf.differentiableOn.mono (hUV n)) (hfm n) (hz n) (hu0 n)
    · rw [hznext n]; exact hu0 (n + 1)
    · exact hr1
  have hiW : InjOn f W := by
    intro x hx y hy hxy
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.mp hy
    have hnm : n = m := by
      by_contra hne
      exact disjoint_left.mp (hdis (by omega : n + 1 ≠ m + 1))
        (hfm n hx.1) (hxy ▸ hfm m hy.1)
    subst m
    exact (hN n hn).2.1 hx hy hxy
  have himage : f '' W ⊆ W \ D N := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    refine ⟨mem_iUnion₂.mpr ⟨n + 1, by omega, hDf n hx⟩, ?_⟩
    intro hfx
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ N)) (hfm n hx.1) hfx.1
  have hWL : ∀ w ∈ W, (w : OnePoint ℂ) ∈ L := by
    intro w hw
    obtain ⟨n, hn, hw⟩ := mem_iUnion₂.mp hw
    exact (hN n hn).1 w hw
  have hWE : Disjoint W (↑E : Set ℂ) := by
    apply disjoint_left.mpr
    intro w hw hwE
    obtain ⟨n, hn, hw⟩ := mem_iUnion₂.mp hw
    exact disjoint_left.mp (hN n hn).2.2 hw.1 hwE
  have hWS : Disjoint W S := by
    apply disjoint_left.mpr
    intro w hw hwS
    rcases hSE w hwS with hwK | hwE
    · exact disjoint_left.mp hKL hwK (hWL w hw)
    · exact disjoint_left.mp hWE hw hwE
  have hWP : ∀ j, Disjoint W (↑(P j) : Set ℂ) := by
    intro j
    apply disjoint_left.mpr
    intro w hw hwP
    obtain ⟨n, _, hw⟩ := mem_iUnion₂.mp hw
    exact disjoint_left.mp (hUP n j) hw.1 hwP
  have hWV : W ⊆ V := by
    intro w hw
    obtain ⟨n, _, hw⟩ := mem_iUnion₂.mp hw
    exact hUV n hw.1
  have hbound : ∀ j, (∫⁻ x in D N,
      hyperbolicAreaWeight (↑(P j) : Set ℂ) (P j).finite_toSet.isClosed hab
        (hP (Nat.zero_le j) ha) (hP (Nat.zero_le j) hb) x) ≤ C := by
    intro j
    have hfj : IsCoveringMapOn (fun x : V => f x) ((↑(P j) : Set ℂ) ∪ S)ᶜ :=
      (ComplexDynamics.isCoveringMapOn_compl_singularValuesOn f V).mono
        (compl_subset_compl.mpr (subset_union_left.trans subset_union_right))
    apply finite_model_area_bound_local (P j) ((P j).finite_toSet.isClosed.union hS)
      subset_union_left hab (hP (Nat.zero_le j) ha) (hP (Nat.zero_le j) hb)
      hV hf hfj (fun w hwV hw => (hforward j w hwV hw).elim Or.inl (fun h => Or.inr (Or.inr h)))
      hWV (hDo N).measurableSet hWo.measurableSet hBW hiW himage
    · intro w hw
      have hfw := (himage ⟨w, hw, rfl⟩).1
      rintro (hfp | hfs)
      · exact disjoint_left.mp (hWP j) hfw hfp
      · exact disjoint_left.mp hWS hfw hfs
    · apply hgain (P j) hab (hP (Nat.zero_le j) ha) (hP (Nat.zero_le j) hb)
        (f '' W) (hWo.measurableSet.image_of_continuousOn_injOn (hf.continuousOn.mono hWV) hiW)
      · exact fun w hw => hWL w (himage hw).1
      · exact (hWP j).mono_left (himage.trans sdiff_subset)
      · exact hWE.mono_left (himage.trans sdiff_subset)
  have harea := intrinsic_chart_area_bound hP hab ha hb (z := z N) (u := u N)
    (by rw [hcomp N]; exact hu N) (by rw [hcomp N]; exact (hub N).mapsTo)
    (hDo N).measurableSet (by rw [hcomp N]; exact inter_subset_left) hbound
  have hformula := chart_disc_area (hU N) (hu N) (hub N) hr.le hr1
  change (∫⁻ x in chartDisc (u N) (U N) r,
    ENNReal.ofReal ((‖deriv (u N) x‖ * discDensity (u N x))^2)) ≤ H at harea
  rw [chartDisc, hformula] at harea
  rw [disc_area_lintegral hr.le hr1, ENNReal.ofReal_toReal hH]
  exact harea

end AreaDeficit
