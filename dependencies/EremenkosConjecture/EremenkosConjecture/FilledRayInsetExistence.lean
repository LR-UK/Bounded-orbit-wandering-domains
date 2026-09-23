import EremenkosConjecture.FilledRayInsets
import EremenkosConjecture.ContinuumUniformTube
import EremenkosConjecture.ComplexJordanNeighbourhood

open Set Metric Complex

namespace EremenkosConjecture

/-- Inside a preceding filled closed neighbourhood with a straight tail,
choose a new filled closed inset around the continuum and ray. Its tail can
be arbitrarily thin, and its compact decoration lies in any prescribed open
neighbourhood of the continuum. All filling stays strictly inside the parent. -/
theorem exists_filled_ray_inset
    {X F N : Set ℂ} {ζ : ℂ} {R H κ : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hN : IsOpen N) (hXN : X ⊆ N)
    (hF : ComplexApproximation.NoBoundedComplementComponents F)
    (hXF : X ∪ horizontalRay ζ ⊆ interior F) (hH : 0 < H)
    (htail : ∀ z : ℂ, R < z.re → |z.im - ζ.im| < H → z ∈ interior F)
    (hκ : 0 < κ) :
    ∃ (C : Set ℂ) (t : ℝ), IsCompact C ∧ IsConnected C ∧
      IsConnected (interior C) ∧ X ⊆ interior C ∧ C ⊆ N ∧
      0 < t ∧ t < κ ∧
      IsClosed (filledRayInset C ζ t t) ∧
      ComplexApproximation.NoBoundedComplementComponents (filledRayInset C ζ t t) ∧
      IsConnected (filledRayInset C ζ t t) ∧
      X ∪ horizontalRay ζ ⊆ interior (filledRayInset C ζ t t) ∧
      filledRayInset C ζ t t ⊆ interior F := by
  obtain ⟨C, hCc, hCconn, _, hXC, hCW, _, hCi, _⟩ :=
    exists_jordan_compact_neighbourhood X (N ∩ interior F) hX hconn hfull
      (hN.inter isOpen_interior) (fun z hz => ⟨hXN hz, hXF (Or.inl hz)⟩)
  obtain ⟨ε, hε, htube⟩ := exists_uniform_tube_of_compact_union_horizontalRay
    hX isOpen_interior hXF hH htail
  obtain ⟨d, hd, hstrip⟩ := exists_closed_halfStrip_subset_of_uniform_tube hε
    (fun z hz => htube z (Or.inr hz))
  let t := min d κ / 2
  have ht : 0 < t := half_pos (lt_min hd hκ)
  have htd : t ≤ d := (half_lt_self (lt_min hd hκ)).le.trans (min_le_left _ _)
  have htκ : t < κ := (half_lt_self (lt_min hd hκ)).trans_le (min_le_right _ _)
  have hsmall : closedHalfStrip ζ t t ⊆ interior F := by
    intro z hz
    exact hstrip ⟨by linarith [hz.1], hz.2.trans htd⟩
  have hprops := filledRayInset_properties hCc hCconn (interior_subset (hXC hζ)) hXC ht ht
  exact ⟨C, t, hCc, hCconn, hCi, hXC, fun z hz => (hCW hz).1, ht, htκ,
    hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2,
    filledRayInset_subset_interior hCc.isClosed (fun z hz => (hCW hz).2) hsmall hF⟩

end EremenkosConjecture
