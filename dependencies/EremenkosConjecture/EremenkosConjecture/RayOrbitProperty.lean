import EremenkosConjecture.RayReferenceOrbits

/-! # The dynamical assertions preserved at each inductive step -/

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

structure RayOrbitProperty (j : ℕ) (a b : ℝ) (F : ℂ → ℂ) : Prop where
  barrier : MapsTo (F^[returnTime j + 1]) (frontier (closedHalfStrip rayBase a b)) trappingDisk
  returnMap : MapsTo (F^[returnTime j + 1]) (horizontalRay rayBase) (sourceStrip 0)
  excursion : MapsTo (F^[returnTime (j + 1)]) (horizontalRay rayBase) (targetStrip (j + 1))
  bounded : ∀ x : ℝ, 1 / ((j : ℝ) + 1) ≤ x → x ≤ (j : ℝ) + 1 →
    |((F^[returnTime j + 1]) (rayBase + x)).re| ≤ 1
  endpoint : ∀ k : ℕ, returnTime j + 1 ≤ k → k ≤ returnTime (j + 1) →
    (j : ℝ) ≤ |((F^[k]) rayBase).re|

namespace RayReturnChannel

def buffer {f : ℂ → ℂ} {j : ℕ} {a b : ℝ} (R : RayReturnChannel f j a b) : Set ℂ :=
  openHalfStrip rayBase (R.η / 4) (b / 8)

def nextRegion {f : ℂ → ℂ} {j : ℕ} {a b : ℝ} (R : RayReturnChannel f j a b) : Set ℂ :=
  closedHalfStrip rayBase (R.η / 32) (b / 32)

theorem buffer_tube_inner {f : ℂ → ℂ} {j : ℕ} {a b : ℝ}
    (R : RayReturnChannel f j a b) (hb : 0 < b) : HasUniformTube R.buffer R.inner :=
  (hasUniformTube_halfStrip (ζ := rayBase) (show R.η / 4 < R.η / 2 by linarith [R.η_pos])
    (show b / 8 < b / 4 by linarith)).mono (openHalfStrip_subset_closed _ _ _) Subset.rfl

theorem nextRegion_tube_buffer {f : ℂ → ℂ} {j : ℕ} {a b : ℝ}
    (R : RayReturnChannel f j a b) (hb : 0 < b) : HasUniformTube R.nextRegion R.buffer :=
  hasUniformTube_closed_openHalfStrip (by linarith [R.η_pos]) (by linarith)

theorem ray_subset_buffer {f : ℂ → ℂ} {j : ℕ} {a b : ℝ}
    (R : RayReturnChannel f j a b) (hb : 0 < b) : horizontalRay rayBase ⊆ R.buffer := by
  intro z hz
  exact ⟨by linarith [hz.1, R.η_pos], by simpa only [hz.2, sub_self, abs_zero] using
    (show 0 < b / 8 by positivity)⟩

end RayReturnChannel

namespace RayReference

variable {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R)

theorem orbitProperty_of_close_iterates {F : ℂ → ℂ}
    (hbarrier : MapsTo (F^[returnTime j + 1]) (frontier S.core) trappingDisk)
    (hclose : ∀ k ≤ returnTime (j + 1), ∀ z ∈ R.buffer,
      dist ((F^[k]) z) ((P.g^[k]) z) < 1 / 100) : RayOrbitProperty j S.a S.b F := by
  have hray := R.ray_subset_buffer S.b_pos
  have hrayC := R.ray_subset_inner S.b_pos.le
  have hreturn {z : ℂ} (hz : z ∈ horizontalRay rayBase) :
      (P.g^[returnTime j + 1]) z = R.ψ z := by
    simpa only [Nat.add_zero, iterate_zero, id_eq] using P.iterate_eq_return (k := 0) (by omega) (hrayC hz)
  have hfinal {z : ℂ} (hz : z ∈ horizontalRay rayBase) :
      (P.g^[returnTime (j + 1)]) z = (S.f^[j + 1]) (R.ψ z) := by
    have he := P.iterate_eq_return (k := j + 1) le_rfl (hrayC hz)
    convert he using 1 <;> congr 1 <;> simp only [returnTime_succ] <;> omega
  have hn : returnTime j + 1 ≤ returnTime (j + 1) := by rw [returnTime_succ]; omega
  refine ⟨hbarrier, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply ball_inset_subset_source (R.orbit 0 (by omega)
      (R.inner_subset_domain S.b_small (hrayC hz)))
    have he := hclose (returnTime j + 1) hn z (hray hz)
    rw [hreturn hz] at he
    exact he.trans_le (by norm_num)
  · intro z hz
    have he := hclose (returnTime (j + 1)) le_rfl z (hray hz)
    rw [hfinal hz, dist_eq_norm] at he
    have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt he)
    simp only [Complex.sub_im] at hi
    have ht := R.target z (R.inner_subset_domain S.b_small (hrayC hz))
    constructor <;> linarith [ht.1, ht.2, hi.1, hi.2]
  · intro x hxlo hxhi
    have hx : 0 ≤ x := (by positivity : 0 < 1 / ((j : ℝ) + 1)).le.trans hxlo
    have hz : rayBase + (x : ℂ) ∈ horizontalRay rayBase :=
      ⟨by change rayBase.re ≤ rayBase.re + x; linarith, by simp⟩
    have he := hclose (returnTime j + 1) hn _ (hray hz)
    rw [hreturn hz, dist_eq_norm] at he
    have hre := (Complex.abs_re_le_norm _).trans_lt he
    simp only [Complex.sub_re] at hre
    have ha := abs_sub_abs_le_abs_sub ((F^[returnTime j + 1]) (rayBase + x)).re (R.ψ (rayBase + x)).re
    linarith [R.boundedReturn x hxlo hxhi]
  · intro k hklo hkhi
    let i := k - (returnTime j + 1)
    have hi : i ≤ j + 1 := by dsimp [i]; rw [returnTime_succ] at hkhi; omega
    have hki : k = returnTime j + 1 + i := by dsimp [i]; omega
    have hg : (P.g^[k]) rayBase = (S.f^[i]) (R.ψ rayBase) :=
      hki ▸ P.iterate_eq_return hi (hrayC (mem_horizontalRay _))
    have he := hclose k hkhi rayBase (hray (mem_horizontalRay _))
    rw [hg, dist_eq_norm] at he
    have hre := (Complex.abs_re_le_norm _).trans_lt he
    simp only [Complex.sub_re] at hre
    have ha := abs_sub_abs_le_abs_sub ((S.f^[i]) (R.ψ rayBase)).re ((F^[k]) rayBase).re
    rw [abs_sub_comm] at ha
    linarith [R.endpoint i hi]

end RayReference

end EremenkosConjecture
