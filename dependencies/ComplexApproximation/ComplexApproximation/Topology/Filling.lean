import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Filling bounded complementary components

The filled set contains the original set and all bounded components of its
complement. Closed sets without such components have full compact intersections
with centred disks, which supplies the compact Runge sets in Arakelian's proof.

The exterior-connectivity argument was first developed in the application's
`EremenkosConjecture/PlaneTopology.lean`.
-/

open Set Metric Bornology
open scoped Topology

namespace ComplexApproximation

def NoBoundedComplementComponents (E : Set ℂ) : Prop :=
  ∀ z ∉ E, ¬ IsBounded (connectedComponentIn Eᶜ z)

def fill (E : Set ℂ) : Set ℂ :=
  {z | IsBounded (connectedComponentIn Eᶜ z)}

theorem subset_fill (E : Set ℂ) : E ⊆ fill E := by
  intro z hz
  change IsBounded (connectedComponentIn Eᶜ z)
  rw [connectedComponentIn_eq_empty (by simpa using hz)]
  exact isBounded_empty

theorem fill_mono {E F : Set ℂ} (h : E ⊆ F) : fill E ⊆ fill F := by
  intro z hz
  change IsBounded (connectedComponentIn Fᶜ z)
  change IsBounded (connectedComponentIn Eᶜ z) at hz
  exact hz.subset (connectedComponentIn_mono z (compl_subset_compl.mpr h))

theorem component_subset_compl_fill {E : Set ℂ} {z : ℂ} (hz : z ∉ fill E) :
    connectedComponentIn Eᶜ z ⊆ (fill E)ᶜ := by
  intro w hw hb
  exact hz (by simpa only [fill, mem_ofPred_eq, ← connectedComponentIn_eq hw] using hb)

theorem connectedComponentIn_compl_fill {E : Set ℂ} {z : ℂ} (hz : z ∉ fill E) :
    connectedComponentIn (fill E)ᶜ z = connectedComponentIn Eᶜ z := by
  apply Subset.antisymm
  · exact connectedComponentIn_mono z (compl_subset_compl.mpr (subset_fill E))
  · have hzE : z ∉ E := fun h => hz (subset_fill E h)
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hzE) (component_subset_compl_fill hz)

theorem isClosed_fill {E : Set ℂ} (hE : IsClosed E) : IsClosed (fill E) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hzE : z ∉ E := fun h => hz (subset_fill E h)
  exact Filter.mem_of_superset
    (hE.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hzE))
    (component_subset_compl_fill hz)

theorem noBoundedComplementComponents_fill (E : Set ℂ) :
    NoBoundedComplementComponents (fill E) := by
  intro z hz hb
  rw [connectedComponentIn_compl_fill hz] at hb
  exact hz hb

theorem fill_eq_self {E : Set ℂ} (hE : NoBoundedComplementComponents E) : fill E = E := by
  apply Subset.antisymm ?_ (subset_fill E)
  intro z hz
  by_contra hn
  exact hE z hn hz

theorem fill_fill (E : Set ℂ) : fill (fill E) = fill E :=
  fill_eq_self (noBoundedComplementComponents_fill E)

theorem isConnected_exterior (R : ℝ) (hR : 0 < R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  have hh : IsConnected {z : ℂ | Real.log R < z.re} :=
    (convex_halfSpace_re_gt (Real.log R)).isConnected
      ⟨((Real.log R + 1 : ℝ) : ℂ), by simp⟩
  have heq : Complex.exp '' {z : ℂ | Real.log R < z.re} = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change R < ‖Complex.exp w‖
      rw [Complex.norm_exp, ← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr hw
    · intro hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log R < (Complex.log z).re
      rw [Complex.log_re]
      exact Real.log_lt_log hR hz
  rw [← heq]
  exact hh.image Complex.exp Complex.continuous_exp.continuousOn

theorem not_isBounded_exterior (R : ℝ) : ¬ IsBounded {z : ℂ | R < ‖z‖} := by
  intro hb
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  let x := max R M + 1
  have hx : 0 < x := by dsimp [x]; linarith [le_max_right R M]
  have hnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx]
  have hmem : (x : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
    simp only [mem_ofPred_eq, hnorm]
    dsimp [x]
    linarith [le_max_left R M]
  have H := hbound (x : ℂ) hmem
  rw [hnorm] at H
  dsimp [x] at H
  linarith [le_max_right R M]

theorem isConnected_compl_of_unbounded_components (K : Set ℂ) (hK : IsBounded K)
    (hcomp : NoBoundedComplementComponents K) : IsConnected Kᶜ := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_pos_norm_le
  have hE := isConnected_exterior R hR
  have hEK : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := fun z hz hzK => (not_lt_of_ge (hKR z hzK)) hz
  obtain ⟨a, ha⟩ := hE.nonempty
  have hEC := hE.isPreconnected.subset_connectedComponentIn ha hEK
  have hC : connectedComponentIn Kᶜ a = Kᶜ := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro z hz
    have hfar : ∃ b ∈ connectedComponentIn Kᶜ z, R < ‖b‖ := by
      by_contra! H
      exact hcomp z hz (isBounded_iff_forall_norm_le.mpr ⟨R, H⟩)
    obtain ⟨b, hb, hbR⟩ := hfar
    have heq : connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ a :=
      (connectedComponentIn_eq hb).trans (connectedComponentIn_eq (hEC hbR)).symm
    rw [← heq]
    exact mem_connectedComponentIn hz
  rw [← hC]
  exact isConnected_connectedComponentIn_iff.mpr (hEK ha)

/-- Intersecting a set without bounded complementary components with a disk
gives a full set. Closedness is only needed for its compactness. -/
theorem isConnected_compl_inter_closedBall {E : Set ℂ}
    (hE : NoBoundedComplementComponents E) {R : ℝ} (hR : 0 < R) :
    IsConnected (E ∩ closedBall 0 R)ᶜ := by
  apply isConnected_compl_of_unbounded_components _
    ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset inter_subset_right)
  intro z hz hb
  by_cases hzE : z ∈ E
  · have hzR : R < ‖z‖ := by
      by_contra! H
      exact hz ⟨hzE, mem_closedBall_zero_iff.mpr H⟩
    have hsub : {w : ℂ | R < ‖w‖} ⊆ (E ∩ closedBall 0 R)ᶜ := by
      intro w hw hmem
      exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hmem.2)) hw
    exact not_isBounded_exterior R (hb.subset
      ((isConnected_exterior R hR).isPreconnected.subset_connectedComponentIn hzR hsub))
  · exact hE z hzE (hb.subset
      (connectedComponentIn_mono z (compl_subset_compl.mpr inter_subset_left)))

end ComplexApproximation
