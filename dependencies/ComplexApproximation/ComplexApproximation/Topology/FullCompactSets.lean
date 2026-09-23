import ComplexApproximation.Topology.Filling
import ComplexApproximation.Topology.Nonseparation
import Runge.PolynomialSeparation
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Full compact sets and their neighbourhoods

These general results were originally proved in the Eremenko application:
PlaneTopology, FullNeighbourhoods, DisjointFullUnions and DryLand. They are
collected here for reuse in the wandering-dynamics constructions. The
neighbourhood proof uses polynomial Runge separation, so it belongs above
ComplexApproximation in the dependency graph. The original public
EremenkosConjecture declarations remain available.
-/

open Set Metric Polynomial Function Bornology
open scoped Topology

namespace ComplexApproximation

/-- Polynomial separation rules out all bounded complementary components,
by the maximum-modulus principle. -/
theorem isConnected_compl_of_polynomial_separation (K : Set ℂ) (hK : IsCompact K)
    (hsep : ∀ z ∉ K, ∃ p : Polynomial ℂ, ∃ C : ℝ,
      (∀ w ∈ K, ‖p.eval w‖ ≤ C) ∧ C < ‖p.eval z‖) : IsConnected Kᶜ := by
  apply isConnected_compl_of_unbounded_components K hK.isBounded
  intro z hz hbounded
  obtain ⟨p, C, hp, hpz⟩ := hsep z hz
  have hfront : frontier (connectedComponentIn Kᶜ z) ⊆ K := by
    simpa only [compl_compl] using frontier_component_subset_compl hK.isClosed.isOpen_compl hz
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le hbounded
    (p.differentiable.diffContOnCl) (fun w hw => hp w (hfront hw))
    (subset_closure (mem_connectedComponentIn hz))
  exact (not_lt_of_ge hbound) hpz

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

/-- Disjoint full compacta have full union (the disjoint case of Janiszewski). -/
theorem isConnected_compl_union_disjoint (A B : Set ℂ) (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsConnected Aᶜ) (hBc : IsConnected Bᶜ) (hAB : Disjoint A B) :
    IsConnected (A ∪ B)ᶜ := by
  obtain ⟨R, hR, hbound⟩ := (hA.union hB).isBounded.exists_pos_norm_le
  refine ⟨?_, ComplexApproximation.isPreconnected_compl_union_disjoint A B
    hA.isClosed hB.isClosed hAB hAc.isPreconnected hBc.isPreconnected⟩
  refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
  intro hz
  have H := hbound _ hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at H
  linarith

theorem isConnected_compl_finite_disjoint_union {ι : Type*} (s : Finset ι) (K : ι → Set ℂ)
    (hcompact : ∀ i ∈ s, IsCompact (K i)) (hfull : ∀ i ∈ s, IsConnected (K i)ᶜ)
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (K i) (K j)) :
    IsConnected (⋃ i ∈ s, K i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isConnected_univ : IsConnected (univ : Set ℂ))
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    apply isConnected_compl_union_disjoint _ _ (hcompact i (Finset.mem_insert_self _ _))
      (s.isCompact_biUnion (fun j hj => hcompact j (Finset.mem_insert_of_mem hj)))
      (hfull i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hcompact j (Finset.mem_insert_of_mem hj))
        (fun j hj => hfull j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hdisjoint j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)))
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hdisjoint i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      (fun H => hi (H.symm ▸ hj))


/-- Fullness persists when a compact neighbourhood is replaced by the
closure of its interior. This gives an open neighbourhood with full closure. -/
theorem isConnected_compl_closure_interior {L : Set ℂ}
    (hL : IsClosed L) (hfull : IsConnected Lᶜ) :
    IsConnected (closure (interior L))ᶜ := by
  apply hfull.subset_closure
  · exact compl_subset_compl.mpr (closure_minimal interior_subset hL)
  · rw [closure_compl]
    exact compl_subset_compl.mpr subset_closure

/-- A full compact set has arbitrarily small relatively compact open
neighbourhoods with full closure. No connectedness of the compact is needed. -/
theorem exists_open_full_compact_neighbourhood (K U : Set ℂ)
    (hK : IsCompact K) (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧
      IsConnected (closure V)ᶜ ∧ closure V ⊆ U := by
  obtain ⟨L, hLc, hLf, hKL, hLU⟩ := exists_full_compact_neighbourhood K U hK hfull hU hKU
  have hsub : closure (interior L) ⊆ L := closure_minimal interior_subset hLc.isClosed
  exact ⟨interior L, isOpen_interior, hKL, hLc.of_isClosed_subset isClosed_closure hsub,
    isConnected_compl_closure_interior hLc.isClosed hLf, hsub.trans hLU⟩

end ComplexApproximation
