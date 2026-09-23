import EremenkosConjecture.NestedFilledRayNeighbourhoods

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

/-- The concrete nested family used for recursive choices. The compact
decorations and widths are retained, so its bands can use the proved geometry. -/
structure ContinuumNeighbourhoods (X : Set ℂ) (ζ : ℂ) (r : ℝ) where
  decoration : ℕ → JordanCompactNeighbourhood X
  width : ℕ → ℝ
  first_decoration : (decoration 0).carrier ⊆ ball ζ r
  nested_decoration : ∀ n, (decoration (n + 1)).carrier ⊆ interior (decoration n).carrier
  intersection_decoration : (⋂ n, (decoration n).carrier) = X
  positive : ∀ n, 0 < width n
  decreasing : StrictAnti width
  first_width : width 0 < r
  limit_width : Tendsto width atTop (𝓝 0)
  geometry : ∀ n,
    ComplexApproximation.IsArakelian (filledRayInset (decoration n).carrier ζ (width n) (width n)) ∧
    X ∪ horizontalRay ζ ⊆ interior (filledRayInset (decoration n).carrier ζ (width n) (width n)) ∧
    filledRayInset (decoration (n + 1)).carrier ζ (width (n + 1)) (width (n + 1)) ⊆
      interior (filledRayInset (decoration n).carrier ζ (width n) (width n))
  intersection : (⋂ n, filledRayInset (decoration n).carrier ζ (width n) (width n)) =
    X ∪ horizontalRay ζ

theorem exists_continuumNeighbourhoods {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hmax : ∀ z ∈ X, z.re ≤ ζ.re)
    (hr : 0 < r) (hXr : X ⊆ ball ζ r) :
    Nonempty (ContinuumNeighbourhoods X ζ r) := by
  obtain ⟨C, t, hC, hn, hi, hp, hd, ht, hl, hg, he⟩ :=
    exists_nested_filled_ray_neighbourhoods hX hconn hfull hζ hmax isOpen_ball hXr hr
  exact ⟨⟨C, t, hC, hn, hi, hp, hd, ht, hl, hg, he⟩⟩

def ContinuumNeighbourhoods.region {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (n : ℕ) : Set ℂ :=
  filledRayInset (D.decoration n).carrier ζ (D.width n) (D.width n)

theorem ContinuumNeighbourhoods.region_antitone {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) : Antitone D.region :=
  antitone_nat_of_succ_le (fun n => (D.geometry n).2.2.trans interior_subset)

theorem ContinuumNeighbourhoods.region_bounds {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (n : ℕ) :
    ∀ z ∈ D.region n, ζ.re - r ≤ z.re ∧ |z.im - ζ.im| ≤ r := by
  have hCleft : ∀ z ∈ (D.decoration 0).carrier, ζ.re - r ≤ z.re := by
    intro z hz
    have hd := mem_ball_iff_norm.mp (D.first_decoration hz)
    have hre := (abs_le.mp (Complex.abs_re_le_norm (z - ζ))).1
    simp only [sub_re] at hre
    linarith
  have hCim : ∀ z ∈ (D.decoration 0).carrier, |z.im - ζ.im| ≤ r := by
    intro z hz
    have hd := mem_ball_iff_norm.mp (D.first_decoration hz)
    have hi : |z.im - ζ.im| ≤ ‖z - ζ‖ := by
      simpa only [sub_im] using Complex.abs_im_le_norm (z - ζ)
    exact hi.trans hd.le
  intro z hz
  exact filledRayInset_coordinate_bounds hCleft hCim
    (by linarith [D.first_width] : ζ.re - r ≤ ζ.re - D.width 0) D.first_width.le
    z (D.region_antitone (Nat.zero_le n) hz)

end EremenkosConjecture
