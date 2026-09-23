import EremenkosConjecture.FilledRayIntersection
import EremenkosConjecture.FilledRayArakelian
import EremenkosConjecture.NestedJordanNeighbourhoods
import EremenkosConjecture.ContinuumRayGeometry

open Set Metric Complex Filter
open scoped Topology

namespace EremenkosConjecture

/-- An actual sequence of nested filled closed neighbourhoods of a full
continuum with its attached rightmost ray. Every member is Arakelian, every
successor lies strictly inside its predecessor, and the intersection is
exactly the continuum and ray. -/
theorem exists_nested_filled_ray_neighbourhoods
    {X N : Set ℂ} {ζ : ℂ} {κ : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hmax : ∀ z ∈ X, z.re ≤ ζ.re)
    (hN : IsOpen N) (hXN : X ⊆ N) (hκ : 0 < κ) :
    ∃ (C : ℕ → JordanCompactNeighbourhood X) (t : ℕ → ℝ),
      (C 0).carrier ⊆ N ∧
      (∀ n, (C (n + 1)).carrier ⊆ interior (C n).carrier) ∧
      (⋂ n, (C n).carrier) = X ∧
      (∀ n, 0 < t n) ∧ StrictAnti t ∧ t 0 < κ ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ n, ComplexApproximation.IsArakelian (filledRayInset (C n).carrier ζ (t n) (t n)) ∧
        X ∪ horizontalRay ζ ⊆ interior (filledRayInset (C n).carrier ζ (t n) (t n)) ∧
        filledRayInset (C (n + 1)).carrier ζ (t (n + 1)) (t (n + 1)) ⊆
          interior (filledRayInset (C n).carrier ζ (t n) (t n))) ∧
      (⋂ n, filledRayInset (C n).carrier ζ (t n) (t n)) = X ∪ horizontalRay ζ := by
  obtain ⟨C, hstep, hinter, hCN⟩ := exists_nested_jordan_neighbourhoods_within X N
    hX hconn hfull hN hXN
  have hCanti : Antitone (fun n => (C n).carrier) :=
    antitone_nat_of_succ_le (fun n => (hstep n).trans interior_subset)
  let t : ℕ → ℝ := fun n => (κ / 2) / ((n : ℝ) + 1)
  have ht n : 0 < t n := div_pos (half_pos hκ) (by positivity)
  have htstrict : StrictAnti t := by
    apply strictAnti_nat_of_succ_lt
    intro n
    apply div_lt_div_of_pos_left (half_pos hκ) (by positivity)
    norm_cast
    omega
  have ht0 : t 0 < κ := by simpa [t] using half_lt_self hκ
  have htlim : Tendsto t atTop (𝓝 0) := by
    simpa only [t, mul_zero, mul_one_div] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hArak n := isArakelian_filledRayInset (ζ := ζ) (C n).compact (ht n).le (ht n).le
  refine ⟨C, t, hCN, hstep, hinter, ht, htstrict, ht0, htlim, ?_, ?_⟩
  · intro n
    have hp := filledRayInset_properties (C n).compact (C n).connected
      (interior_subset ((C n).contains hζ)) (C n).contains (ht n) (ht n)
    refine ⟨hArak n, hp.2.2.2, ?_⟩
    apply filledRayInset_subset_interior (C (n + 1)).compact.isClosed
      ((hstep n).trans (interior_mono (fun z hz => ComplexApproximation.subset_fill _ (Or.inl hz))))
      ?_ (hArak n).noBoundedComplementComponents
    intro z hz
    apply interior_mono (fun w hw => ComplexApproximation.subset_fill _ (Or.inr hw))
    apply mem_interior_closedHalfStrip_of_strict
    · linarith [hz.1, htstrict (Nat.lt_succ_self n)]
    · exact hz.2.trans_lt (htstrict (Nat.lt_succ_self n))
  · have hfullE : ComplexApproximation.NoBoundedComplementComponents
        ((⋂ n, (C n).carrier) ∪ horizontalRay ζ) := by
      rw [hinter]
      exact noBoundedComplementComponents_union_horizontalRay hX hfull hζ hmax
    simpa only [hinter] using iInter_filledRayInset_eq
      (fun n => (C n).compact) hCanti htstrict.antitone htstrict.antitone
      (fun n => (ht n).le) (fun n => (ht n).le) htlim htlim hfullE

end EremenkosConjecture
