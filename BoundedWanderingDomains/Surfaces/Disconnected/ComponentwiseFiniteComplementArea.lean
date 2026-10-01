module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseCuspArea
public import BoundedWanderingDomains.Surfaces.CoordinateDiskSelection
public import BoundedWanderingDomains.Surfaces.ComponentDomains

@[expose] public section

/-! # Finite area over compact sets after deleting finitely many points -/

open Set Function Metric MeasureTheory
open scoped Manifold Topology ENNReal

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [LocallyCompactSpace M]

/-- Finite-puncture area is finite above every compact subset of the ambient
manifold, including compact sets which contain the punctures. -/
theorem hyperbolicArea_compl_finset_preimage_compact_lt_top (F : Finset M)
    (O : TopologicalSpace.Opens M)
    (hO : ∀ x : M, x ∈ O ↔ x ∉ (↑F : Set M)) (hON : Nonempty O)
    (p : ComponentwiseDiscCover O) {K₀ : Set M} (hK₀ : IsCompact K₀) :
    p.hyperbolicArea (Subtype.val ⁻¹' K₀) < ⊤ := by
  classical
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let D : ↥F → RiemannDynamics.CoordDisk M := fun i =>
    Classical.choose (SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset
      (U := ((↑(F.erase i) : Set M)ᶜ))
      (F.erase i).finite_toSet.isClosed.isOpen_compl
      (by
        show (i : M) ∉ (↑(F.erase (i : M)) : Set M)
        simp))
  have hD : ∀ i : ↥F,
      (D i).center = (i : M) ∧
        (D i).closedCarrier ⊆ ((↑(F.erase i) : Set M)ᶜ) := by
    intro i
    exact Classical.choose_spec
      (SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset
        (U := ((↑(F.erase i) : Set M)ᶜ))
        (F.erase i).finite_toSet.isClosed.isOpen_compl
        (by
          show (i : M) ∉ (↑(F.erase (i : M)) : Set M)
          simp))
  let c : ↥F → OpenPartialHomeomorph M ℂ := fun i => chartAt ℂ (D i).center
  let N : ↥F → Set M := fun i =>
    (c i).symm '' ball (c i (D i).center) ((D i).radius / 2)
  let A : ↥F → Set O := fun i =>
    ((c i).subtypeRestr hON).symm ''
      (ball (c i (D i).center) ((D i).radius / 2) \ {c i (D i).center})
  have hball_target : ∀ i : ↥F,
      ball (c i (D i).center) (D i).radius \ {c i (D i).center} ⊆
        ((c i).subtypeRestr hON).target := by
    intro i z hz
    have hzt : z ∈ (c i).target := by
      apply (D i).closedBall_subset
      exact mem_closedBall.mpr (le_of_lt hz.1)
    have hyF : (c i).symm z ∉ (↑F : Set M) := by
      intro hy
      have hycarrier : (c i).symm z ∈ (D i).closedCarrier := by
        refine ⟨z, ?_, rfl⟩
        exact mem_closedBall.mpr (le_of_lt hz.1)
      have hyerase : (c i).symm z ∉ (↑(F.erase i) : Set M) :=
        hD i |>.2 hycarrier
      have hyi : (c i).symm z = (i : M) := by
        by_contra hne
        exact hyerase (by simpa [Finset.mem_erase, hne] using hy)
      apply hz.2
      calc
        z = c i ((c i).symm z) := ((c i).right_inv hzt).symm
        _ = c i (i : M) := congrArg (c i) hyi
        _ = c i (D i).center := congrArg (c i) (hD i |>.1.symm)
    let y : O := ⟨(c i).symm z, (hO _).mpr hyF⟩
    have hymem : (y : M) ∈ (c i).source := (c i).map_target hzt
    have hmap := (c i).map_subtype_source hON (x := y) hymem
    change c i (c i |>.symm z) ∈ ((c i).subtypeRestr hON).target at hmap
    simpa only [(c i).right_inv hzt] using hmap
  have hAfin : ∀ i ∈ (Finset.univ : Finset ↥F),
      p.hyperbolicArea (A i) < ⊤ := by
    intro i _
    exact p.hyperbolicArea_cusp_chart_finite
      (mdifferentiableOn_subtypeRestr hON
        (mdifferentiable_chart (I := 𝓘(ℂ)) (D i).center).1)
      (D i).radius_pos (hball_target i)
  have hNopen : ∀ i : ↥F, IsOpen (N i) := by
    intro i
    apply (c i).isOpen_image_symm_of_subset_target isOpen_ball
    intro z hz
    apply (D i).closedBall_subset
    exact mem_closedBall.mpr (le_trans (le_of_lt hz)
      (half_lt_self (D i).radius_pos).le)
  let K : Set M := K₀ \ (⋃ i : ↥F, N i)
  have hKcompact : IsCompact K := hK₀.diff (isOpen_iUnion hNopen)
  have hKO : K ⊆ (O : Set M) := by
    intro x hxK
    apply (hO x).mpr
    intro hxF
    let i : ↥F := ⟨x, hxF⟩
    apply hxK.2
    rw [mem_iUnion]
    refine ⟨i, ?_⟩
    refine ⟨c i (D i).center, mem_ball_self (half_pos (D i).radius_pos), ?_⟩
    calc
      (c i).symm (c i (D i).center) = (D i).center :=
        (c i).left_inv (mem_chart_source ℂ (D i).center)
      _ = (i : M) := hD i |>.1
      _ = x := rfl
  let L : Set O := Subtype.val ⁻¹' K
  have hLcompact : IsCompact L := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rw [image_preimage_eq_inter_range]
    convert hKcompact using 1
    exact (inter_eq_left.mpr fun x hx => ⟨⟨x, hKO hx⟩, rfl⟩)
  suffices hcover : (Subtype.val : O → M) ⁻¹' K₀ ⊆
      L ∪ ⋃ i ∈ (Finset.univ : Finset ↥F), A i by
    apply lt_of_le_of_lt (measure_mono hcover)
    apply lt_of_le_of_lt (measure_union_le _ _)
    apply lt_of_le_of_lt (add_le_add le_rfl (measure_biUnion_finset_le Finset.univ A))
    exact ENNReal.add_lt_top.mpr ⟨p.hyperbolicArea_compact_finite hLcompact,
      ENNReal.sum_lt_top.mpr hAfin⟩
  intro y hy
  by_cases hyK : (y : M) ∈ K
  · exact Or.inl hyK
  · right
    have hyN : (y : M) ∈ ⋃ i : ↥F, N i := by
      by_contra hn
      exact hyK ⟨hy, hn⟩
    rw [mem_iUnion] at hyN
    obtain ⟨i, z, hzball, hzy⟩ := hyN
    rw [mem_iUnion]
    refine ⟨i, ?_⟩
    rw [mem_iUnion]
    refine ⟨Finset.mem_univ i, ?_⟩
    have hzt : z ∈ (c i).target := by
      apply (D i).closedBall_subset
      exact mem_closedBall.mpr (le_trans (le_of_lt hzball)
        (half_lt_self (D i).radius_pos).le)
    have hzne : z ≠ c i (D i).center := by
      intro hzi
      have hyi : (y : M) = (i : M) := by
        rw [← hzy, hzi]
        rw [(c i).left_inv (mem_chart_source ℂ (D i).center), hD i |>.1]
      exact ((hO _).mp y.property) (hyi ▸ i.property)
    refine ⟨z, ⟨hzball, hzne⟩, ?_⟩
    have hzbig : z ∈ ball (c i (D i).center) (D i).radius \
        {c i (D i).center} :=
      ⟨(lt_trans hzball (half_lt_self (D i).radius_pos)), hzne⟩
    have hs := (c i).subtypeRestr_symm_apply hON (hball_target i hzbig)
    apply Subtype.ext
    simpa only [Function.comp_apply] using hs.trans hzy

end AreaDeficit.Surfaces.ComponentwiseDiscCover

