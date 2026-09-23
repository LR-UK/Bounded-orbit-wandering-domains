import EremenkosConjecture.ContinuumRayGeometry
import EremenkosConjecture.DiscGeometry

/-! # Arakelian geometry of a continuum with an attached ray

The set used in Theorem 1.2 is Arakelian. A disk centred at the attachment
point, together with the ray, has no holes, and bounds the holes produced
by adjoining any disk to the original set. Large compact truncations are
full continua and hence admit the already constructed Jordan neighbourhoods.
-/

open Set Metric Complex Bornology

namespace EremenkosConjecture

theorem closedBall_union_horizontalRay_eq_shift (ζ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    closedBall ζ r ∪ horizontalRay ζ =
      closedBall ζ r ∪ horizontalRay (ζ + (r : ℂ)) := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · by_cases h : z.re ≤ ζ.re + r
      · left
        have heq : z - ζ = ((z.re - ζ.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [hz.2]
        rw [mem_closedBall, dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hz.1)]
        linarith
      · right
        exact ⟨by simpa using (le_of_not_ge h), by simpa using hz.2⟩
  · rintro (hz | hz)
    · exact Or.inl hz
    · right
      have hre : ζ.re + r ≤ z.re := by simpa using hz.1
      exact ⟨by linarith, by simpa using hz.2⟩

theorem noBoundedComplementComponents_closedBall_union_horizontalRay
    (ζ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ComplexApproximation.NoBoundedComplementComponents
      (closedBall ζ r ∪ horizontalRay ζ) := by
  rw [closedBall_union_horizontalRay_eq_shift ζ hr]
  apply noBoundedComplementComponents_union_horizontalRay (isCompact_closedBall _ _)
    (isConnected_compl_closedBall _ _)
  · simpa only [mem_closedBall, dist_self_add_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr] using le_rfl (a := r)
  · intro z hz
    have h := (Complex.re_le_norm (z - ζ)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [sub_re, add_re, ofReal_re] at h ⊢
    linarith

theorem isArakelian_union_horizontalRay {X : Set ℂ} {ζ : ℂ}
    (hX : IsCompact X) (hfull : IsConnected Xᶜ) (hζ : ζ ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ ζ.re) :
    ComplexApproximation.IsArakelian (X ∪ horizontalRay ζ) := by
  refine ⟨hX.isClosed.union (isClosed_horizontalRay ζ),
    noBoundedComplementComponents_union_horizontalRay hX hfull hζ hmax, ?_⟩
  intro R
  obtain ⟨C, hC, hbound⟩ := hX.isBounded.exists_pos_norm_le
  let r := C + |R| + ‖ζ‖ + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hXball : X ⊆ closedBall ζ r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le z ζ).trans (by dsimp [r]; linarith [hbound z hz, abs_nonneg R])
  have hRball : closedBall (0 : ℂ) R ⊆ closedBall ζ r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have hnorm := mem_closedBall_zero_iff.mp hz
    exact (norm_sub_le z ζ).trans (by dsimp [r]; linarith [le_abs_self R])
  have hsub : (X ∪ horizontalRay ζ) ∪ closedBall 0 R ⊆
      closedBall ζ r ∪ horizontalRay ζ := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl (hXball hz)
    · exact Or.inr hz
    · exact Or.inl (hRball hz)
  have hfill := ComplexApproximation.fill_mono hsub
  rw [ComplexApproximation.fill_eq_self
    (noBoundedComplementComponents_closedBall_union_horizontalRay ζ hr)] at hfill
  apply isBounded_closedBall.subset
  intro z hz
  rcases hfill hz.1 with h | h
  · exact h
  · exact False.elim (hz.2 (Or.inr h))

theorem full_connected_compact_ray_truncation {X : Set ℂ} {ζ : ℂ} {R : ℝ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : ζ ∈ X) (hmax : ∀ x ∈ X, x.re ≤ ζ.re) (hR : 0 < R)
    (hXR : X ⊆ closedBall 0 R) :
    IsCompact ((X ∪ horizontalRay ζ) ∩ closedBall 0 R) ∧
      IsConnected ((X ∪ horizontalRay ζ) ∩ closedBall 0 R) ∧
      IsConnected (((X ∪ horizontalRay ζ) ∩ closedBall 0 R)ᶜ) := by
  have hconv : Convex ℝ (horizontalRay ζ) := by
    have heq : horizontalRay ζ = {z : ℂ | ζ.re ≤ z.re} ∩
        ({z : ℂ | z.im ≤ ζ.im} ∩ {z : ℂ | ζ.im ≤ z.im}) := by
      ext z
      simp only [horizontalRay, mem_setOf_eq, mem_inter_iff, le_antisymm_iff]
    rw [heq]
    exact (convex_halfSpace_re_ge ζ.re).inter
      ((convex_halfSpace_im_le ζ.im).inter (convex_halfSpace_im_ge ζ.im))
  have hζR : ζ ∈ horizontalRay ζ ∩ closedBall 0 R := ⟨mem_horizontalRay ζ, hXR hζ⟩
  have heq : (X ∪ horizontalRay ζ) ∩ closedBall 0 R =
      X ∪ (horizontalRay ζ ∩ closedBall 0 R) := by
    ext z
    constructor
    · rintro ⟨hz | hz, hball⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hz, hball⟩
    · rintro (hz | hz)
      · exact ⟨Or.inl hz, hXR hz⟩
      · exact ⟨Or.inr hz.1, hz.2⟩
  refine ⟨(isCompact_closedBall 0 R).inter_left (hX.isClosed.union (isClosed_horizontalRay ζ)),
    ?_, ComplexApproximation.isConnected_compl_inter_closedBall
      (noBoundedComplementComponents_union_horizontalRay hX hfull hζ hmax) hR⟩
  rw [heq]
  exact hconn.union ⟨ζ, hζ, hζR⟩ ((hconv.inter (convex_closedBall _ _)).isConnected ⟨ζ, hζR⟩)

end EremenkosConjecture
