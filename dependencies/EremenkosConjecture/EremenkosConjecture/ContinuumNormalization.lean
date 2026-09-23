import EremenkosConjecture.ContinuumCounterexampleCriterion
import ComplexDynamics.Conjugacy
import ComplexDynamics.Scaling

/-! # Affine coordinate changes for prescribed escaping components

The general-continuum construction may first be carried out after shrinking
and translating the compact set. These lemmas transport the exact connected
component conclusion back through those coordinate changes.
-/

open Set Function ComplexDynamics Polynomial

namespace EremenkosConjecture

noncomputable def affineCoordinates (a : ℂ) (ha : a ≠ 0) (b : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

@[simp] theorem affineCoordinates_apply (a : ℂ) (ha : a ≠ 0) (b z : ℂ) :
    affineCoordinates a ha b z = a * z + b := rfl

@[simp] theorem affineCoordinates_symm_apply (a : ℂ) (ha : a ≠ 0) (b z : ℂ) :
    (affineCoordinates a ha b).symm z = a⁻¹ * (z - b) := rfl

theorem transcendentalEntire_conjugate_affine {f : ℂ → ℂ}
    (hf : IsTranscendentalEntire f) (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    IsTranscendentalEntire (conjugate (affineCoordinates a ha b) f) := by
  let g := conjugate (affineCoordinates a ha b) f
  have hg (z : ℂ) : g z = a * f (a⁻¹ * (z - b)) + b := rfl
  have hgentire : IsEntire g :=
    ((hf.1.comp ((differentiable_id.sub_const b).const_mul a⁻¹)).const_mul a).add_const b
  refine ⟨hgentire, ?_⟩
  rintro ⟨p, hp⟩
  apply hf.2
  refine ⟨C a⁻¹ * (p.comp (C a * X + C b) - C b), fun z => ?_⟩
  have h := hp (a * z + b)
  change a * f (a⁻¹ * (a * z + b - b)) + b = p.eval (a * z + b) at h
  simp only [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul] at h
  simp only [eval_mul, eval_C, eval_sub, eval_comp, eval_add, eval_X]
  rw [← h, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem escapingComponent_affine_image {f : ℂ → ℂ} {X : Set ℂ} {z : ℂ}
    (hz : z ∈ escapingSet f) (hX : connectedComponentIn (escapingSet f) z = X)
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    connectedComponentIn (escapingSet (conjugate (affineCoordinates a ha b) f))
      (a * z + b) = (fun w => a * w + b) '' X := by
  have h := (affineCoordinates a ha b).image_connectedComponentIn hz
  rw [hX, image_escapingSet_conjugate] at h
  exact h.symm

theorem exists_escapingComponent_affine_image {X : Set ℂ}
    (hX : ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      ∃ z ∈ escapingSet f, connectedComponentIn (escapingSet f) z = X)
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = (fun w => a * w + b) '' X := by
  obtain ⟨f, hf, z, hz, hcomp⟩ := hX
  refine ⟨conjugate (affineCoordinates a ha b) f,
    transcendentalEntire_conjugate_affine hf a ha b, a * z + b, ?_,
    escapingComponent_affine_image hz hcomp a ha b⟩
  exact (mem_escapingSet_conjugate_iff (affineCoordinates a ha b) f z).mpr hz

/-- A compact set can be shrunk into any prescribed disk while a point of
maximal real part is sent to its centre. The multiplier is positive real. -/
theorem exists_compact_normalization_at_rightmost_point {X : Set ℂ}
    (hX : IsCompact X) (hne : X.Nonempty) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ ∈ X, ∃ a : ℝ, 0 < a ∧
      MapsTo (fun z => (a : ℂ) * (z - ζ) + c) X (Metric.ball c ε) ∧
      ∀ z ∈ X, ((a : ℂ) * (z - ζ) + c).re ≤ c.re := by
  obtain ⟨ζ, hζ, hmax⟩ := hX.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨R, hR, hbound⟩ :=
    (hX.image (continuous_id.sub continuous_const)).isBounded.exists_pos_norm_le
  let a : ℝ := ε / (R + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have haR : a * (R + 1) = ε := by dsimp [a]; field_simp
  refine ⟨ζ, hζ, a, ha, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_mul]
    have hnorm : ‖(a : ℂ)‖ = a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [hnorm]
    have hb : ‖z - ζ‖ ≤ R := hbound _ (mem_image_of_mem (fun w => w - ζ) hz)
    nlinarith
  · intro z hz
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re]
    have hm : z.re ≤ ζ.re := hmax hz
    nlinarith

/-- The normalized image is still compact, connected and full. This uses only
the explicit affine homeomorphism, without a conformal boundary-extension theorem. -/
theorem exists_full_continuum_in_disk {X : Set ℂ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : ℂ) (ha : a ≠ 0) (b : ℂ),
      IsCompact (affineCoordinates a ha b '' X) ∧
      IsConnected (affineCoordinates a ha b '' X) ∧
      IsConnected (affineCoordinates a ha b '' X)ᶜ ∧
      affineCoordinates a ha b '' X ⊆ Metric.ball c ε ∧
      c ∈ affineCoordinates a ha b '' X ∧
      ∀ z ∈ affineCoordinates a ha b '' X, z.re ≤ c.re := by
  obtain ⟨ζ, hζ, a, ha, hmap, hmax⟩ :=
    exists_compact_normalization_at_rightmost_point hX hconn.nonempty c hε
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  let b : ℂ := c - a * ζ
  let H := affineCoordinates (a : ℂ) hane b
  have hH (z : ℂ) : H z = (a : ℂ) * (z - ζ) + c := by
    change (a : ℂ) * z + (c - a * ζ) = _
    ring
  refine ⟨a, hane, b, hX.image H.continuous,
    hconn.image H H.continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · rw [← H.image_compl]
    exact hfull.image H H.continuous.continuousOn
  · rintro z ⟨w, hw, rfl⟩
    change H w ∈ Metric.ball c ε
    rw [hH]
    exact hmap hw
  · refine ⟨ζ, hζ, ?_⟩
    change H ζ = c
    simp [hH]
  · rintro z ⟨w, hw, rfl⟩
    change (H w).re ≤ c.re
    rw [hH]
    exact hmax w hw

/-- Transfer a construction on a normalized image back to the exact original
set. The conclusion is an equality of connected components with that set. -/
theorem exists_escapingComponent_of_affine_image {X : Set ℂ}
    (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (hX : ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = (fun w => a * w + b) '' X) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      ∃ z ∈ escapingSet f, connectedComponentIn (escapingSet f) z = X := by
  obtain ⟨f, hf, z, hz, hcomp⟩ :=
    exists_escapingComponent_affine_image hX a⁻¹ (inv_ne_zero ha) (-a⁻¹ * b)
  refine ⟨f, hf, z, hz, ?_⟩
  have hinverse : (fun w : ℂ => a⁻¹ * (a * w + b) + -a⁻¹ * b) = id := by
    funext w
    dsimp
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    ring
  simpa only [image_image, hinverse, image_id] using hcomp

/-- It suffices to construct every full continuum in a fixed disk whose
centre is a rightmost point. This is a reduction, with the local construction
explicitly supplied as a hypothesis. -/
theorem continuum_realization_of_normalized_disk_case (c : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ Y : Set ℂ, IsCompact Y → IsConnected Y → IsConnected Yᶜ →
      Y ⊆ Metric.ball c ε → c ∈ Y → (∀ z ∈ Y, z.re ≤ c.re) →
      ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
        connectedComponentIn (escapingSet f) z = Y)
    (X : Set ℂ) (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      ∃ z ∈ escapingSet f, connectedComponentIn (escapingSet f) z = X := by
  obtain ⟨a, ha, b, hc, hn, hfull', hball, hbase, hmax⟩ :=
    exists_full_continuum_in_disk hX hconn hfull c hε
  exact exists_escapingComponent_of_affine_image a ha b
    (hlocal (affineCoordinates a ha b '' X) hc hn hfull' hball hbase hmax)

end EremenkosConjecture
