import EremenkosConjecture.ContinuumNeighbourhoods
import EremenkosConjecture.ClosedStripNeighbourhoods

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

/-- A later member of the fixed neighbourhood family fits inside any chosen
open neighbourhood of the continuum and ray with a positive-width tail. -/
theorem ContinuumNeighbourhoods.exists_later_region_subset_open
    {X U : Set ℂ} {ζ : ℂ} {r R H : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hU : IsOpen U)
    (hXU : X ∪ horizontalRay ζ ⊆ U) (hH : 0 < H)
    (htailU : ∀ z : ℂ, R < z.re → |z.im - ζ.im| < H → z ∈ U)
    (start : ℕ) : ∃ n, start ≤ n ∧ D.region n ⊆ U := by
  have hCanti : Antitone (fun n => (D.decoration n).carrier) :=
    antitone_nat_of_succ_le (fun n => (D.nested_decoration n).trans interior_subset)
  obtain ⟨A, _, hA⟩ := (D.decoration 0).compact.isBounded.exists_pos_norm_le
  let T := max A ζ.re
  have htail : ∀ n, ∀ z ∈ D.region n, T < z.re → |z.im - ζ.im| ≤ D.width n := by
    intro n z hz hzr
    apply (filledRayInset_tail_iff (A := T) (C := (D.decoration n).carrier) ?_ hzr ?_).mp hz
    · intro w hw
      exact (Complex.re_le_norm w).trans
        ((hA w (hCanti (Nat.zero_le n) hw)).trans (le_max_left _ _))
    · have hzζ : ζ.re < z.re := (le_max_right A ζ.re).trans_lt hzr
      linarith [D.positive n]
  have him : ∀ n, ∀ z ∈ D.region n, |z.im| ≤ r + |ζ.im| := by
    intro n z hz
    have h := abs_add_le (z.im - ζ.im) ζ.im
    rw [sub_add_cancel] at h
    linarith [(D.region_bounds n z hz).2]
  obtain ⟨n, hn⟩ := exists_stage_subset_open_of_shrinking_straight_tails
    (fun n => (D.geometry n).1.isClosed) D.region_antitone
    (fun n z hz => (D.region_bounds n z hz).1) him htail D.limit_width hU
    (by simpa only [ContinuumNeighbourhoods.region, D.intersection] using hXU) hH htailU
  exact ⟨max n start, le_max_right _ _, (D.region_antitone (le_max_left _ _)).trans hn⟩

end EremenkosConjecture
