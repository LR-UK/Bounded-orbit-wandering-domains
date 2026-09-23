import ComplexDynamics.FatouComponents
import Mathlib.Topology.Connected.PathConnected

open Set

namespace ComplexDynamics

/-- If no path in `S` starting in `K` leaves `K`, its path components are
already the path components of `S`. -/
theorem pathComponentIn_eq_of_no_exit {K S : Set ℂ} (hKS : K ⊆ S)
    (hno : ∀ x ∈ K, ∀ y, JoinedIn S x y → y ∈ K) {x : ℂ} (hx : x ∈ K) :
    pathComponentIn S x = pathComponentIn K x := by
  apply Subset.antisymm
  · exact (isPathConnected_pathComponentIn (hKS hx)).subset_pathComponentIn
      (mem_pathComponentIn_self (hKS hx)) (fun y hy => hno x hx y hy)
  · exact pathComponentIn_mono hKS

/-- The corresponding intersection form, used for the Julia part of a compactum. -/
theorem pathComponentIn_eq_inter_of_no_exit {K S : Set ℂ}
    (hno : ∀ x ∈ K, ∀ y, JoinedIn S x y → y ∈ K) {x : ℂ} (hx : x ∈ K ∩ S) :
    pathComponentIn S x = pathComponentIn (K ∩ S) x := by
  apply pathComponentIn_eq_of_no_exit inter_subset_right
  · intro z hz y hy
    exact ⟨hno z hz.1 y hy, hy.target_mem⟩
  · exact hx

end ComplexDynamics
