import EremenkosConjecture.PlaneTopology
import Runge.PolynomialSeparation

/-!
# Full compact neighbourhoods

Polynomial separation constructs full compact neighbourhoods inside any given
open neighbourhood of a full compact set. This proves the neighbourhood part
of Lemma 2.9 without invoking the Riemann mapping theorem.
-/

open Set Metric Polynomial

namespace EremenkosConjecture

theorem exists_full_compact_neighbourhood (K U : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ IsConnected Lᶜ ∧ K ⊆ interior L ∧ L ⊆ U := by
  classical
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
  let R := r + 1
  let E : Set ℂ := closedBall 0 R ∩ Uᶜ
  have hE : IsCompact E := (isCompact_closedBall 0 R).inter_right hU.isClosed_compl
  have hsep : ∀ a : E, ∃ p : Polynomial ℂ, p.eval (a : ℂ) = 1 ∧
      ∀ z ∈ K, ‖p.eval z‖ < 1 / 2 := by
    intro a
    exact Runge.exists_polynomial_separator K hK hfull a (fun ha => a.property.2 (hKU ha))
  choose p hp hpK using hsep
  let V : E → Set ℂ := fun a => {z | (3 / 4 : ℝ) < ‖(p a).eval z‖}
  have hV : ∀ a, IsOpen (V a) := fun a => isOpen_lt continuous_const (p a).continuous.norm
  have hcover : E ⊆ ⋃ a, V a := by
    intro a ha
    apply mem_iUnion.mpr
    refine ⟨⟨a, ha⟩, ?_⟩
    change (3 / 4 : ℝ) < ‖(p ⟨a, ha⟩).eval a‖
    rw [hp ⟨a, ha⟩, norm_one]
    norm_num
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover V hV hcover
  let L : Set ℂ := closedBall 0 R ∩ ⋂ a : s, {z | ‖(p a).eval z‖ ≤ (3 / 4 : ℝ)}
  have hLc : IsCompact L := (isCompact_closedBall 0 R).inter_right
    (isClosed_iInter fun a : s => isClosed_le (p a).continuous.norm continuous_const)
  have hLU : L ⊆ U := by
    intro z hz
    by_contra hzU
    have hzE : z ∈ E := ⟨hz.1, hzU⟩
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hs hzE)
    have hle : ‖(p a).eval z‖ ≤ (3 / 4 : ℝ) := mem_iInter.mp hz.2 ⟨a, ha⟩
    change (3 / 4 : ℝ) < ‖(p a).eval z‖ at hza
    exact (not_lt_of_ge hle) hza
  have hLf : IsConnected Lᶜ := by
    apply isConnected_compl_of_polynomial_separation L hLc
    intro z hz
    by_cases hzball : z ∈ closedBall (0 : ℂ) R
    · have hex : ∃ a : s, (3 / 4 : ℝ) < ‖(p a).eval z‖ := by
        by_contra! H
        exact hz ⟨hzball, mem_iInter.mpr H⟩
      obtain ⟨a, ha⟩ := hex
      exact ⟨p a, 3 / 4, fun w hw => mem_iInter.mp hw.2 a, ha⟩
    · refine ⟨X, R, ?_, ?_⟩
      · intro w hw
        simpa only [eval_X, mem_closedBall, dist_zero_right] using hw.1
      · simpa only [eval_X, mem_closedBall, dist_zero_right, not_le] using hzball
  refine ⟨L, hLc, hLf, ?_, hLU⟩
  let O : Set ℂ := ball 0 R ∩ ⋂ a : s, {z | ‖(p a).eval z‖ < (3 / 4 : ℝ)}
  have hOo : IsOpen O := isOpen_ball.inter (isOpen_iInter_of_finite fun a : s =>
    isOpen_lt (p a).continuous.norm continuous_const)
  have hOL : O ⊆ L := by
    intro z hz
    refine ⟨ball_subset_closedBall hz.1, mem_iInter.mpr fun a => ?_⟩
    exact (show ‖(p a).eval z‖ < (3 / 4 : ℝ) from mem_iInter.mp hz.2 a).le
  intro z hz
  have hzO : z ∈ O := by
    constructor
    · rw [mem_ball, dist_zero_right]
      have H := hKr z hz
      dsimp [R]
      linarith
    · apply mem_iInter.mpr
      intro a
      exact (hpK a z hz).trans (by norm_num)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hOo.mem_nhds hzO) hOL)

/-- A full compact neighbourhood of `K`, with no boundary regularity imposed. -/
structure FullCompactNeighbourhood (K : Set ℂ) where
  carrier : Set ℂ
  isCompact : IsCompact carrier
  isFull : IsConnected carrierᶜ
  containsInterior : K ⊆ interior carrier

private noncomputable def chooseFullNeighbourhood (K U : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) : FullCompactNeighbourhood K :=
  let h := exists_full_compact_neighbourhood K U hK hfull hU hKU
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1⟩

private theorem chooseFullNeighbourhood_subset (K U : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    (chooseFullNeighbourhood K U hK hfull hU hKU).carrier ⊆ U :=
  (exists_full_compact_neighbourhood K U hK hfull hU hKU).choose_spec.2.2.2

/-- The nested-full-compact part of Lemma 2.9. The optional finite-Jordan-curve
boundary refinement is not part of this statement. -/
theorem exists_nested_full_compact_neighbourhoods (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) :
    ∃ L : ℕ → Set ℂ, (∀ n, IsCompact (L n) ∧ IsConnected (L n)ᶜ) ∧
      (∀ n, K ⊆ interior (L n)) ∧ (∀ n, L (n + 1) ⊆ interior (L n)) ∧
      (⋂ n, L n) = K := by
  let initial := chooseFullNeighbourhood K (thickening 1 K) hK hfull isOpen_thickening
    (self_subset_thickening zero_lt_one K)
  have hpos (n : ℕ) : 0 < (1 / (n + 2 : ℝ)) := by positivity
  let step : ℕ → FullCompactNeighbourhood K → FullCompactNeighbourhood K := fun n V =>
    chooseFullNeighbourhood K (interior V.carrier ∩ thickening (1 / (n + 2 : ℝ)) K)
      hK hfull (isOpen_interior.inter isOpen_thickening)
      (fun z hz => ⟨V.containsInterior hz, self_subset_thickening (hpos n) K hz⟩)
  let S : ℕ → FullCompactNeighbourhood K := Nat.rec initial step
  have hstep (n : ℕ) : (S (n + 1)).carrier ⊆
      interior (S n).carrier ∩ thickening (1 / (n + 2 : ℝ)) K := by
    exact chooseFullNeighbourhood_subset K _ hK hfull _ _
  refine ⟨fun n => (S n).carrier, fun n => ⟨(S n).isCompact, (S n).isFull⟩,
    fun n => (S n).containsInterior, fun n => (hstep n).trans inter_subset_left, ?_⟩
  apply Subset.antisymm
  · intro z hz
    rw [← hK.isClosed.closure_eq]
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hn' : (1 / (n + 2 : ℝ)) < ε :=
      (by apply one_div_le_one_div_of_le; positivity; norm_cast; omega :
        (1 / (n + 2 : ℝ)) ≤ 1 / (n + 1 : ℝ)).trans_lt hn
    have hzthin := (hstep n (mem_iInter.mp hz (n + 1))).2
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hzthin
    exact ⟨w, hw, hzw.trans hn'⟩
  · intro z hz
    exact mem_iInter.mpr fun n => interior_subset ((S n).containsInterior hz)

/-- The nested neighbourhoods can start inside any prescribed open
neighbourhood. -/
theorem exists_nested_full_compact_neighbourhoods_within (K U : Set ℂ)
    (hK : IsCompact K) (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : ℕ → Set ℂ, (∀ n, IsCompact (L n) ∧ IsConnected (L n)ᶜ) ∧
      (∀ n, K ⊆ interior (L n)) ∧ (∀ n, L (n + 1) ⊆ interior (L n)) ∧
      (⋂ n, L n) = K ∧ L 0 ⊆ U := by
  obtain ⟨L, hL, hKL, hnest, hcap⟩ := exists_nested_full_compact_neighbourhoods K hK hfull
  have hanti : Antitone L := antitone_nat_of_succ_le (fun n => (hnest n).trans interior_subset)
  have hdir : Directed (· ⊇ ·) L := fun i j =>
    ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  have hnhds : U ∈ nhdsSet (⋂ n, L n) := by rw [hcap]; exact hU.mem_nhdsSet.mpr hKU
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact hdir (fun n => (hL n).1) hnhds
  refine ⟨fun n => L (N + n), fun n => hL _, fun n => hKL _,
    fun n => by simpa only [Nat.add_assoc] using hnest (N + n), ?_, by simpa using hN⟩
  rw [← hcap]
  apply Subset.antisymm
  · intro z hz
    exact mem_iInter.mpr (fun n => hanti (by omega : n ≤ N + n) (mem_iInter.mp hz n))
  · intro z hz
    exact mem_iInter.mpr (fun n => mem_iInter.mp hz (N + n))

end EremenkosConjecture
