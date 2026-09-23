import EremenkosConjecture.ComplexJordanNeighbourhood

open Set Metric

namespace EremenkosConjecture

/-- A regular full Jordan neighbourhood of a prescribed continuum. -/
structure JordanCompactNeighbourhood (K : Set ℂ) where
  carrier : Set ℂ
  compact : IsCompact carrier
  connected : IsConnected carrier
  full : IsConnected carrierᶜ
  contains : K ⊆ interior carrier
  jordan : IsComplexJordanCurve (frontier carrier)
  connectedInterior : IsConnected (interior carrier)
  regular : carrier = closure (interior carrier)

private theorem exists_jordanNeighbourhood (K U : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : JordanCompactNeighbourhood K, L.carrier ⊆ U := by
  obtain ⟨L, hc, hn, hf, hKL, hLU, hJ, hi, hr⟩ :=
    exists_jordan_compact_neighbourhood K U hK hconn hfull hU hKU
  exact ⟨⟨L, hc, hn, hf, hKL, hJ, hi, hr⟩, hLU⟩

private noncomputable def chooseJordanNeighbourhood (K U : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    JordanCompactNeighbourhood K :=
  (exists_jordanNeighbourhood K U hK hconn hfull hU hKU).choose

private theorem chooseJordanNeighbourhood_subset (K U : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    (chooseJordanNeighbourhood K U hK hconn hfull hU hKU).carrier ⊆ U :=
  (exists_jordanNeighbourhood K U hK hconn hfull hU hKU).choose_spec

/-- The Jordan-curve refinement of Lemma 2.9 for a full continuum, with the
initial neighbourhood contained in an arbitrary prescribed open set. -/
theorem exists_nested_jordan_neighbourhoods_within (K U : Set ℂ)
    (hK : IsCompact K) (hconn : IsConnected K) (hfull : IsConnected Kᶜ)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : ℕ → JordanCompactNeighbourhood K,
      (∀ n, (L (n + 1)).carrier ⊆ interior (L n).carrier) ∧
      (⋂ n, (L n).carrier) = K ∧ (L 0).carrier ⊆ U := by
  let initial := chooseJordanNeighbourhood K U hK hconn hfull hU hKU
  have hpos (n : ℕ) : 0 < (1 / (n + 2 : ℝ)) := by positivity
  let step : ℕ → JordanCompactNeighbourhood K → JordanCompactNeighbourhood K := fun n V =>
    chooseJordanNeighbourhood K (interior V.carrier ∩ thickening (1 / (n + 2 : ℝ)) K)
      hK hconn hfull (isOpen_interior.inter isOpen_thickening)
      (fun z hz => ⟨V.contains hz, self_subset_thickening (hpos n) K hz⟩)
  let S : ℕ → JordanCompactNeighbourhood K := Nat.rec initial step
  have hstep (n : ℕ) : (S (n + 1)).carrier ⊆
      interior (S n).carrier ∩ thickening (1 / (n + 2 : ℝ)) K := by
    exact chooseJordanNeighbourhood_subset K _ hK hconn hfull _ _
  refine ⟨S, fun n => (hstep n).trans inter_subset_left, ?_,
    chooseJordanNeighbourhood_subset K U hK hconn hfull hU hKU⟩
  apply Subset.antisymm
  · intro z hz
    rw [← hK.isClosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hn' : (1 / (n + 2 : ℝ)) < ε :=
      (by apply one_div_le_one_div_of_le; positivity; norm_cast; omega :
        (1 / (n + 2 : ℝ)) ≤ 1 / (n + 1 : ℝ)).trans_lt hn
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp
      ((hstep n (mem_iInter.mp hz (n + 1))).2)
    exact ⟨w, hw, hzw.trans hn'⟩
  · exact fun z hz => mem_iInter.mpr fun n => interior_subset ((S n).contains hz)

end EremenkosConjecture
