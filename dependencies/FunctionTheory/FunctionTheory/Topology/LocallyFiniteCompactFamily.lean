import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A family that escapes every norm ball is locally finite, including when
some of its members are empty. -/
theorem locallyFinite_of_uniform_norm_escape
    {E : Type*} [NormedAddCommGroup E] (K : ℕ → Set E)
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖) :
    LocallyFinite K := by
  intro x
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape (‖x‖ + 1))
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), (Set.finite_Iio N).subset ?_⟩
  rintro n ⟨z, hzK, hzx⟩
  change n < N
  by_contra hn
  have hz := hN n (by omega) z hzK
  have hnorm := norm_le_norm_sub_add z x
  have hd : ‖z - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hzx
  linarith

/-- Uniformly bounded thickenings of an escaping family still escape. -/
theorem uniform_norm_escape_cthickening
    {E : Type*} [NormedAddCommGroup E] (K : ℕ → Set E)
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖)
    (r : ℕ → ℝ) (hr : ∀ n, r n ≤ 1) :
    ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ cthickening (r n) (K n), R < ‖z‖ := by
  intro R
  filter_upwards [hescape (R + 2)] with n hn
  intro z hz
  have H := cthickening_subset_thickening' (by norm_num : (0 : ℝ) < 2)
    ((hr n).trans_lt (by norm_num)) (K n) hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp H
  have hnw := hn w hw
  have hnorm := norm_le_norm_sub_add w z
  have hd : ‖w - z‖ < 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hzw
  linarith

/-- A locally finite family of disjoint compact sets admits disjoint closed
thickenings inside any prescribed open neighbourhoods. Radii can be bounded
by one, which is useful when preserving escape to infinity. -/
theorem exists_disjoint_closed_thickenings
    {E ι : Type*} [PseudoMetricSpace E] [T2Space E]
    (K U : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hfinite : LocallyFinite K) (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i) ∧ (∀ i, r i ≤ 1) ∧
      (∀ i, cthickening (r i) (K i) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (cthickening (r i) (K i))
        (cthickening (r j) (K j))) := by
  classical
  let O : ι → Set E := fun i => ⋃ j : {j : ι // j ≠ i}, K j
  have hO : ∀ i, IsClosed (O i) := by
    intro i
    exact (hfinite.comp_injective (g := fun j : {j : ι // j ≠ i} => (j : ι))
      Subtype.val_injective).isClosed_iUnion (fun j => (hK j).isClosed)
  have hKO : ∀ i, Disjoint (K i) (O i) := by
    intro i
    apply disjoint_iUnion_right.mpr
    intro j
    exact hdis (Ne.symm j.property)
  choose a ha Hsep using (fun i => (hKO i).exists_cthickenings (hK i) (hO i))
  choose b hb HU using (fun i => (hK i).exists_cthickening_subset_open (hU i) (hKU i))
  let r : ι → ℝ := fun i => min (a i) (min (b i) 1)
  have hra : ∀ i, r i ≤ a i := fun i => min_le_left _ _
  have hrb : ∀ i, r i ≤ b i := fun i =>
    (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : ∀ i, r i ≤ 1 := fun i =>
    (min_le_right _ _).trans (min_le_right _ _)
  have Hother : ∀ i j, i ≠ j → K i ⊆ O j := by
    intro i j hij z hz
    exact mem_iUnion.mpr ⟨⟨i, hij⟩, hz⟩
  refine ⟨r, (fun i => lt_min (ha i) (lt_min (hb i) zero_lt_one)),
    hr1, (fun i => (cthickening_mono (hrb i) (K i)).trans (HU i)), ?_⟩
  intro i j hij
  rcases le_total (r i) (r j) with h | h
  · apply (Hsep j).symm.mono
    · exact (cthickening_mono (h.trans (hra j)) (K i)).trans
        (cthickening_subset_of_subset (a j) (Hother i j hij))
    · exact cthickening_mono (hra j) (K j)
  · apply (Hsep i).mono
    · exact cthickening_mono (hra i) (K i)
    · exact (cthickening_mono (h.trans (hra i)) (K j)).trans
        (cthickening_subset_of_subset (a i) (Hother j i hij.symm))

/-- Escaping disjoint compact sets have relatively compact open
neighbourhoods with disjoint closures that also escape to infinity. -/
theorem exists_disjoint_escaping_open_neighborhoods
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (K U : ℕ → Set E) (hK : ∀ n, IsCompact (K n))
    (hdis : Pairwise (fun n m => Disjoint (K n) (K m)))
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖)
    (hU : ∀ n, IsOpen (U n)) (hKU : ∀ n, K n ⊆ U n) :
    ∃ W : ℕ → Set E,
      (∀ n, IsOpen (W n)) ∧ (∀ n, K n ⊆ W n) ∧
      (∀ n, IsCompact (closure (W n))) ∧
      (∀ n, closure (W n) ⊆ U n) ∧
      Pairwise (fun n m => Disjoint (closure (W n)) (closure (W m))) ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closure (W n), R < ‖z‖ := by
  obtain ⟨r, hr, hr1, hsub, hpair⟩ := exists_disjoint_closed_thickenings K U hK
    (locallyFinite_of_uniform_norm_escape K hescape) hdis hU hKU
  refine ⟨fun n => thickening (r n) (K n), (fun _ => isOpen_thickening),
    (fun n => self_subset_thickening (hr n) (K n)), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hK n).cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening _ _)
  · intro n
    exact (closure_thickening_subset_cthickening _ _).trans (hsub n)
  · intro n m hnm
    exact (hpair hnm).mono (closure_thickening_subset_cthickening _ _)
      (closure_thickening_subset_cthickening _ _)
  · intro R
    filter_upwards [uniform_norm_escape_cthickening K hescape r hr1 R] with n hn
    exact fun z hz => hn z (closure_thickening_subset_cthickening _ _ hz)

end FunctionTheory
