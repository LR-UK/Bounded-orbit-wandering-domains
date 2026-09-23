import EremenkosConjecture.ContinuumNeighbourhoods
import EremenkosConjecture.FilledRayInterior
import EremenkosConjecture.QuantitativeGeometry
import FunctionTheory.Conformal.StripUniformity

open Set Metric Complex

namespace EremenkosConjecture

def ContinuumNeighbourhoods.openRegion {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (n : ℕ) : Set ℂ :=
  filledRayInterior (D.decoration n).carrier ζ (D.width n) (D.width n)

theorem ContinuumNeighbourhoods.openRegion_properties {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (n : ℕ) :
    IsOpen (D.openRegion n) ∧ IsConnected (D.openRegion n) ∧
      horizontalRay ζ ⊆ D.openRegion n :=
  filledRayInterior_properties _ _ (D.positive n) (D.positive n)

theorem ContinuumNeighbourhoods.region_connected {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X) (n : ℕ) :
    IsConnected (D.region n) :=
  (filledRayInset_properties (D.decoration n).compact (D.decoration n).connected
    (interior_subset ((D.decoration n).contains hζ)) (D.decoration n).contains
    (D.positive n) (D.positive n)).2.2.1

theorem ContinuumNeighbourhoods.region_subset_openRegion {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X) {i n : ℕ} (hin : i < n) :
    D.region n ⊆ D.openRegion i := by
  have hsub : D.region n ⊆ interior (D.region i) :=
    (D.region_antitone (Nat.succ_le_of_lt hin)).trans (D.geometry i).2.2
  apply (D.region_connected hζ n).isPreconnected.subset_connectedComponentIn
    (interior_subset ((D.geometry n).2.1 (Or.inl hζ))) hsub

theorem ContinuumNeighbourhoods.openRegion_subset {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (n : ℕ) :
    D.openRegion n ⊆ interior (D.region n) := connectedComponentIn_subset _ _

theorem ContinuumNeighbourhoods.core_subset_openRegion {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X) (n : ℕ) :
    X ∪ horizontalRay ζ ⊆ D.openRegion n :=
  ((D.geometry (n + 1)).2.1.trans interior_subset).trans
    (D.region_subset_openRegion hζ (Nat.lt_succ_self n))

/-- A common threshold beyond which every fixed neighbourhood has its
specified straight tail. -/
theorem ContinuumNeighbourhoods.exists_common_tail {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) :
    ∃ A : ℝ, ζ.re ≤ A ∧ ∀ n, ∀ z : ℂ, A < z.re →
      (z ∈ D.region n ↔ |z.im - ζ.im| ≤ D.width n) ∧
      (z ∈ D.openRegion n ↔ |z.im - ζ.im| < D.width n) := by
  have hCanti : Antitone (fun n => (D.decoration n).carrier) :=
    antitone_nat_of_succ_le (fun n => (D.nested_decoration n).trans interior_subset)
  obtain ⟨B, _, hB⟩ := (D.decoration 0).compact.isBounded.exists_pos_norm_le
  let A := max B ζ.re
  have hζA : ζ.re ≤ A := le_max_right _ _
  have ht (n : ℕ) (z : ℂ) (hz : A < z.re) :
      z ∈ D.region n ↔ |z.im - ζ.im| ≤ D.width n := by
    apply filledRayInset_tail_iff (A := A) ?_ hz
      (by linarith [D.positive n])
    intro w hw
    exact (re_le_norm w).trans ((hB w (hCanti (Nat.zero_le n) hw)).trans (le_max_left _ _))
  refine ⟨A, hζA, fun n z hz => ⟨ht n z hz, ?_⟩⟩
  exact filledRayInterior_tail_iff (D.positive n) (D.positive n) hζA (ht n) z hz

/-- Strict nesting leaves a uniform positive margin, including on the
unbounded straight tails. -/
theorem ContinuumNeighbourhoods.region_tube_openRegion {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X) {i n : ℕ} (hin : i < n) :
    HasUniformTube (D.region n) (D.openRegion i) := by
  obtain ⟨A, _, htail⟩ := D.exists_common_tail
  let δ := min (D.width i - D.width n) 1 / 2
  have hgap : 0 < D.width i - D.width n := sub_pos.mpr (D.decreasing hin)
  have hδ : 0 < δ := half_pos (lt_min hgap zero_lt_one)
  have hδgap : δ < D.width i - D.width n :=
    (half_lt_self (lt_min hgap zero_lt_one)).trans_le (min_le_left _ _)
  have hδ1 : δ < 1 :=
    (half_lt_self (lt_min hgap zero_lt_one)).trans_le (min_le_right _ _)
  have him : ∀ z ∈ D.region n, |z.im| ≤ r + |ζ.im| := by
    intro z hz
    have h := abs_add_le (z.im - ζ.im) ζ.im
    rw [sub_add_cancel] at h
    linarith [(D.region_bounds n z hz).2]
  obtain ⟨ε, hε, htube⟩ := FunctionTheory.exists_uniform_neighbourhood_of_strip_tail
    (R := A + 1) (D.geometry n).1.isClosed (fun z hz => (D.region_bounds n z hz).1)
    him (D.openRegion_properties i).1 (D.region_subset_openRegion hζ hin) hδ (by
      intro z hz hzA w hw
      have hd : ‖w - z‖ ≤ δ := mem_closedBall_iff_norm.mp hw
      have hre : |w.re - z.re| ≤ δ := by
        simpa only [sub_re] using (abs_re_le_norm (w - z)).trans hd
      have hwi : |w.im - z.im| ≤ δ := by
        simpa only [sub_im] using (abs_im_le_norm (w - z)).trans hd
      have hzi := (htail n z (by linarith)).1.mp hz
      apply (htail i w (by linarith [(abs_le.mp hre).1])).2.mpr
      have hi := abs_add_le (w.im - z.im) (z.im - ζ.im)
      rw [sub_add_sub_cancel] at hi
      linarith)
  exact ⟨ε, hε, fun z hz => ball_subset_closedBall.trans (htube z hz)⟩

/-- The boundary of an intermediate neighbourhood has a uniform margin
inside the surrounding band. Its image can therefore be sent into the
interior of the trapping disk with a fixed approximation tolerance. -/
theorem ContinuumNeighbourhoods.frontier_tube_band {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X)
    {i m n : ℕ} (him : i < m) (hmn : m < n) :
    HasUniformTube (frontier (D.region m)) (D.region i \ D.openRegion n) := by
  obtain ⟨a, ha, houter⟩ := D.region_tube_openRegion hζ him
  obtain ⟨b, hb, hinner⟩ := D.region_tube_openRegion hζ hmn
  refine ⟨min a b, lt_min ha hb, fun z hz w hw => ?_⟩
  change dist w z < min a b at hw
  refine ⟨?_, ?_⟩
  · have hzm : z ∈ D.region m := (D.geometry m).1.isClosed.frontier_subset hz
    exact interior_subset (D.openRegion_subset i (houter z hzm
      (show w ∈ ball z a from hw.trans_le (min_le_left _ _))))
  · intro hwn
    have hwreg : w ∈ D.region n := interior_subset (D.openRegion_subset n hwn)
    have hzw : z ∈ ball w b := by
      rw [mem_ball, dist_comm]
      exact hw.trans_le (min_le_right _ _)
    exact hz.2 (D.openRegion_subset m (hinner w hwreg hzw))

theorem ContinuumNeighbourhoods.decoration_subset_interior {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) {i n : ℕ} (hin : i < n) :
    (D.decoration n).carrier ⊆ interior (D.decoration i).carrier := by
  have hanti : Antitone (fun n => (D.decoration n).carrier) :=
    antitone_nat_of_succ_le (fun n => (D.nested_decoration n).trans interior_subset)
  exact (hanti (Nat.succ_le_of_lt hin)).trans (D.nested_decoration i)

end EremenkosConjecture
