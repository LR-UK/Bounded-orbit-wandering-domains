import EremenkosConjecture.ContinuumReferenceOrbits

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

structure ContinuumOrbitProperty {X : Set ℂ}
    (D : ContinuumNeighbourhoods X rayBase (1 / 16)) (j depth : ℕ) (F : ℂ → ℂ) : Prop where
  barrier : MapsTo (F^[returnTime j + 1]) (frontier (D.region (depth + 1))) trappingDisk
  returnMap : MapsTo (F^[returnTime j + 1]) (X ∪ horizontalRay rayBase) (sourceStrip 0)
  excursion : MapsTo (F^[returnTime (j + 1)]) (X ∪ horizontalRay rayBase) (targetStrip (j + 1))
  bounded : ∀ x : ℝ, 1 / ((j : ℝ) + 1) ≤ x → x ≤ (j : ℝ) + 1 →
    |((F^[returnTime j + 1]) (rayBase + x)).re| ≤ 1
  escape : ∀ z ∈ X, ∀ k : ℕ, returnTime j + 1 ≤ k → k ≤ returnTime (j + 1) →
    (j : ℝ) ≤ |((F^[k]) z).re|

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

theorem ContinuumReference.orbitProperty_of_close_iterates (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {F : ℂ → ℂ}
    (hbarrier : MapsTo (F^[returnTime j + 1]) (frontier (D.region (S.depth + 1))) trappingDisk)
    (hclose : ∀ k ≤ returnTime (j + 1), ∀ z ∈ D.openRegion (R.depth + 2),
      dist ((F^[k]) z) ((P.reference.g^[k]) z) < 1 / 100) :
    ContinuumOrbitProperty D j S.depth F := by
  have hcore := D.core_subset_openRegion hζ (R.depth + 2)
  have hcoreC : X ∪ horizontalRay rayBase ⊆ D.region R.depth :=
    (D.geometry R.depth).2.1.trans interior_subset
  have hreturn {z : ℂ} (hz : z ∈ X ∪ horizontalRay rayBase) :
      (P.reference.g^[returnTime j + 1]) z = R.ψ z := by
    simpa only [Nat.add_zero, iterate_zero, id_eq] using
      P.iterate_eq_return (k := 0) (by omega) (hcoreC hz)
  have hn : returnTime j + 1 ≤ returnTime (j + 1) := by rw [returnTime_succ]; omega
  refine ⟨hbarrier, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply ball_inset_subset_source (R.orbit 0 (by omega) (R.contains hz))
    have he := hclose (returnTime j + 1) hn z (hcore hz)
    rw [hreturn hz] at he
    exact he.trans_le (by norm_num)
  · intro z hz
    have he := hclose (returnTime (j + 1)) le_rfl z (hcore hz)
    rw [dist_eq_norm] at he
    have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt he)
    simp only [Complex.sub_im] at hi
    have ht := P.target_margin z (hcoreC hz)
    constructor <;> linarith [ht.1, ht.2, hi.1, hi.2]
  · intro x hxlo hxhi
    have hx : 0 ≤ x := (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)).le.trans hxlo
    have hz : rayBase + (x : ℂ) ∈ X ∪ horizontalRay rayBase :=
      Or.inr ⟨by change rayBase.re ≤ rayBase.re + x; linarith, by simp⟩
    have he := hclose (returnTime j + 1) hn _ (hcore hz)
    rw [hreturn hz, dist_eq_norm] at he
    have hre := (Complex.abs_re_le_norm _).trans_lt he
    simp only [Complex.sub_re] at hre
    have ha := abs_sub_abs_le_abs_sub ((F^[returnTime j + 1]) (rayBase + x)).re
      (R.ψ (rayBase + x)).re
    linarith [R.boundedReturn x hxlo hxhi]
  · intro z hz k hklo hkhi
    let i := k - (returnTime j + 1)
    have hi : i ≤ j + 1 := by dsimp [i]; rw [returnTime_succ] at hkhi; omega
    have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
    have hg : (P.reference.g^[k]) z = (S.f^[i]) (R.ψ z) :=
      hki ▸ P.iterate_eq_return hi (hcoreC (Or.inl hz))
    have he := hclose k hkhi z (hcore (Or.inl hz))
    rw [hg, dist_eq_norm] at he
    have hre := (Complex.abs_re_le_norm _).trans_lt he
    simp only [Complex.sub_re] at hre
    have ha := abs_sub_abs_le_abs_sub ((S.f^[i]) (R.ψ z)).re ((F^[k]) z).re
    rw [abs_sub_comm] at ha
    linarith [R.continuumEscape z hz i hi]

end EremenkosConjecture
