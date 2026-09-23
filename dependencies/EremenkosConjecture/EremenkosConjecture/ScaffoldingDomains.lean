import EremenkosConjecture.ScaffoldingBranches

/-! # Connected strip inverse domains and their unbounded real parts -/

open Set Metric Function Complex

namespace EremenkosConjecture.Scaffolding

theorem targetStrip_eq_inter (j : ℕ) : targetStrip j =
    {z : ℂ | (height j + 7) / 4 < z.im} ∩ {z : ℂ | z.im < (height j + 11) / 4} := by
  ext z
  change (height j + 7 < 4 * z.im ∧ 4 * z.im < height j + 11) ↔
    ((height j + 7) / 4 < z.im ∧ z.im < (height j + 11) / 4)
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem targetStrip_center (j : ℕ) (x : ℝ) : (⟨x, (height j + 9) / 4⟩ : ℂ) ∈ targetStrip j := by
  change height j + 7 < 4 * ((height j + 9) / 4) ∧
    4 * ((height j + 9) / 4) < height j + 11
  constructor <;> linarith

theorem isConnected_targetStrip (j : ℕ) : IsConnected (targetStrip j) := by
  refine ⟨⟨⟨0, (height j + 9) / 4⟩, targetStrip_center j 0⟩, ?_⟩
  rw [targetStrip_eq_inter]
  exact ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected

theorem not_bddAbove_re_targetStrip (j : ℕ) : ¬ BddAbove (Complex.re '' targetStrip j) := by
  rintro ⟨M, hM⟩
  have H := hM ⟨(⟨M + 1, (height j + 9) / 4⟩ : ℂ), targetStrip_center j (M + 1), rfl⟩
  change M + 1 ≤ M at H
  linarith

theorem not_bddBelow_re_targetStrip (j : ℕ) : ¬ BddBelow (Complex.re '' targetStrip j) := by
  rintro ⟨M, hM⟩
  have H := hM ⟨(⟨M - 1, (height j + 9) / 4⟩ : ℂ), targetStrip_center j (M - 1), rfl⟩
  change M ≤ M - 1 at H
  linarith

theorem bddAbove_re_image_of_close_affine {f : ℂ → ℂ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    {A : Set ℂ} (hA : A ⊆ sourceStrips) (hb : BddAbove (Complex.re '' A)) :
    BddAbove (Complex.re '' (f '' A)) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨5 * M + 1 / 100, ?_⟩
  rintro x ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  have H := (abs_re_le_norm (f z - 5 * z)).trans (hclose z (hA hz))
  have H' : |(f z).re - 5 * z.re| ≤ 1 / 100 := by simpa using H
  have hm : z.re ≤ M := hM (mem_image_of_mem _ hz)
  have he := (abs_le.mp H').2
  linarith

theorem bddBelow_re_image_of_close_affine {f : ℂ → ℂ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    {A : Set ℂ} (hA : A ⊆ sourceStrips) (hb : BddBelow (Complex.re '' A)) :
    BddBelow (Complex.re '' (f '' A)) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨5 * M - 1 / 100, ?_⟩
  rintro x ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  have H := (abs_re_le_norm (f z - 5 * z)).trans (hclose z (hA hz))
  have H' : |(f z).re - 5 * z.re| ≤ 1 / 100 := by simpa using H
  have hm : M ≤ z.re := hM (mem_image_of_mem _ hz)
  have he := (abs_le.mp H').1
  linarith

/-- The remaining domain assertions of Lemma 4.1: connectivity and real parts
unbounded in both directions. -/
theorem strip_chart_domain_properties {f : ℂ → ℂ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (j : ℕ) (e : OpenPartialHomeomorph ℂ ℂ) (heT : e.target = targetStrip j)
    (he : ∀ z, e z = (f^[j]) z)
    (horbit : ∀ k < j, MapsTo (f^[k]) e.source (sourceStrip k)) :
    IsConnected e.source ∧ ¬ BddAbove (Complex.re '' e.source) ∧
      ¬ BddBelow (Complex.re '' e.source) := by
  have himage : (f^[j]) '' e.source = targetStrip j := by
    rw [show (f^[j]) = e from funext (fun z => (he z).symm), e.image_source_eq_target, heT]
  have hA (k : ℕ) (hk : k < j) : (f^[k]) '' e.source ⊆ sourceStrips := by
    rintro w ⟨z, hz, rfl⟩
    exact mem_iUnion.mpr ⟨k, horbit k hk hz⟩
  refine ⟨?_, ?_, ?_⟩
  · have H : IsConnected (e.symm '' e.target) :=
      (heT.symm ▸ isConnected_targetStrip j).image e.symm e.continuousOn_symm
    have hi : e.symm '' e.target = e.source := e.symm.image_source_eq_target
    rwa [hi] at H
  · intro hb
    have H (k : ℕ) (hk : k ≤ j) : BddAbove (Complex.re '' ((f^[k]) '' e.source)) := by
      induction k with
      | zero => simpa using hb
      | succ k ih =>
          rw [iterate_succ', image_comp]
          exact bddAbove_re_image_of_close_affine hclose (hA k (by omega)) (ih (by omega))
    exact not_bddAbove_re_targetStrip j (himage ▸ H j le_rfl)
  · intro hb
    have H (k : ℕ) (hk : k ≤ j) : BddBelow (Complex.re '' ((f^[k]) '' e.source)) := by
      induction k with
      | zero => simpa using hb
      | succ k ih =>
          rw [iterate_succ', image_comp]
          exact bddBelow_re_image_of_close_affine hclose (hA k (by omega)) (ih (by omega))
    exact not_bddBelow_re_targetStrip j (himage ▸ H j le_rfl)

end EremenkosConjecture.Scaffolding
