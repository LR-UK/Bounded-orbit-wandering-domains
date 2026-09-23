import EremenkosConjecture.DiscGeometry

/-! # Finite schedules of control and target disks with variable radii -/

open Set Metric

namespace EremenkosConjecture

def variableControlDisc (r : ℝ) : Set ℂ := closedBall (-3) r
def variableTargetDisc (a : ℝ) : Set ℂ := ball (a : ℂ) 1

theorem variableTargetDisc_re_bounds {a : ℝ} {z : ℂ} (hz : z ∈ variableTargetDisc a) :
    a - 1 < z.re ∧ z.re < a + 1 := by
  have hnorm : ‖z - (a : ℂ)‖ < 1 := by
    simpa only [variableTargetDisc, mem_ball, dist_eq_norm] using hz
  have H := (Complex.abs_re_le_norm (z - (a : ℂ))).trans_lt hnorm
  simp only [Complex.sub_re, Complex.ofReal_re] at H
  obtain ⟨h₁, h₂⟩ := abs_lt.mp H
  constructor <;> linarith

theorem variableControlDisc_re_bound {r : ℝ} {z : ℂ} (hz : z ∈ variableControlDisc r) :
    z.re ≤ r - 3 := by
  have hnorm : ‖z - (-3 : ℂ)‖ ≤ r := by
    simpa only [variableControlDisc, mem_closedBall, dist_eq_norm] using hz
  have H := (le_abs_self (z - (-3 : ℂ)).re).trans ((Complex.abs_re_le_norm _).trans hnorm)
  change z.re - (-3) ≤ r at H
  linarith

theorem variableTargetDisc_subset_control_interior {a r : ℝ} (ha : 0 ≤ a) (har : a + 4 ≤ r) :
    variableTargetDisc a ⊆ interior (variableControlDisc r) := by
  intro z hz
  have hz' : dist z (a : ℂ) < 1 := hz
  have hc : dist (a : ℂ) (-3) = a + 3 := by
    rw [dist_eq_norm]
    have heq : (a : ℂ) - (-3) = ((a + 3 : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have H := dist_triangle z (a : ℂ) (-3)
  rw [hc] at H
  exact ball_subset_interior_closedBall (show z ∈ ball (-3) r from (by
    change dist z (-3) < r
    linarith))

theorem translate_mem_variableTargetDisc {a b : ℝ} {z : ℂ}
    (hz : z ∈ variableTargetDisc a) : z + ((b - a : ℝ) : ℂ) ∈ variableTargetDisc b := by
  change dist (z + ((b - a : ℝ) : ℂ)) (b : ℂ) < 1
  have heq : (b : ℂ) = (a : ℂ) + ((b - a : ℝ) : ℂ) := by push_cast; ring
  rw [heq, dist_add_right]
  exact hz

structure DiscSchedule (n : ℕ) where
  radius : ℕ → ℝ
  initial : radius 0 = 1
  gap : ∀ j < n, radius j + 5 < radius (j + 1)

namespace DiscSchedule

variable {n : ℕ}

def center (S : DiscSchedule n) (j : ℕ) : ℝ := if j = 0 then 0 else S.radius j

theorem radius_mono (S : DiscSchedule n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    S.radius i ≤ S.radius j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases hi : i = j + 1
    · subst i; rfl
    · have H := ih (by omega) (by omega)
      have Hg := S.gap j (by omega)
      linarith

theorem radius_lower (S : DiscSchedule n) {j : ℕ} (hj : j ≤ n) :
    1 + 5 * j ≤ S.radius j := by
  induction j with
  | zero => simp [S.initial]
  | succ j ih =>
    have H := ih (by omega)
    have Hg := S.gap j (by omega)
    push_cast
    linarith

theorem center_nonneg (S : DiscSchedule n) {j : ℕ} (hj : j ≤ n) : 0 ≤ S.center j := by
  by_cases hj0 : j = 0
  · simp [center, hj0]
  · simp only [center, if_neg hj0]
    have H := S.radius_lower hj
    have hj' : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith

theorem center_radius (S : DiscSchedule n) {j : ℕ} (hj : j ≤ n) :
    S.radius j ≤ S.center j + 1 := by
  by_cases hj0 : j = 0
  · simp [center, hj0, S.initial]
  · simp [center, hj0]

theorem target_subset_control_interior (S : DiscSchedule n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    variableTargetDisc (S.center i) ⊆ interior (variableControlDisc (S.radius j)) := by
  apply variableTargetDisc_subset_control_interior (S.center_nonneg (by omega))
  by_cases hi : i = 0
  · simp only [center, hi, ite_true, zero_add]
    have H := S.radius_lower hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    linarith
  · simp only [center, if_neg hi]
    have Hg := S.gap i (by omega)
    have Hm := S.radius_mono (by omega : i + 1 ≤ j) hj
    linarith

theorem disjoint_targets (S : DiscSchedule n) {i j : ℕ}
    (hi : i ≤ n) (hj : j ≤ n) (hne : i ≠ j) :
    Disjoint (variableTargetDisc (S.center i)) (variableTargetDisc (S.center j)) := by
  have hgap {k l : ℕ} (hkl : k < l) (hl : l ≤ n) : S.center k + 2 < S.center l := by
    have hl0 : l ≠ 0 := by omega
    simp only [center, if_neg hl0]
    by_cases hk0 : k = 0
    · simp only [hk0, ite_true, zero_add]
      have H := S.radius_lower hl
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
      linarith
    · simp only [if_neg hk0]
      have H := S.gap k (by omega)
      have Hm := S.radius_mono (by omega : k + 1 ≤ l) hl
      linarith
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨hi₁, hi₂⟩ := variableTargetDisc_re_bounds hzi
  obtain ⟨hj₁, hj₂⟩ := variableTargetDisc_re_bounds hzj
  rcases lt_or_gt_of_ne hne with h | h
  · have H := hgap h hj
    linarith
  · have H := hgap h hi
    linarith

def initialSchedule : DiscSchedule 0 := ⟨fun _ => 1, rfl, by simp⟩

noncomputable def extend (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r) :
    DiscSchedule (n + 1) where
  radius := Function.update S.radius (n + 1) r
  initial := by simpa using S.initial
  gap := by
    intro j hj
    by_cases hjn : j = n
    · subst j
      simpa using hr
    · have hjn' : j < n := by omega
      simpa [Function.update_of_ne (show j ≠ n + 1 by omega),
        Function.update_of_ne (show j + 1 ≠ n + 1 by omega)] using S.gap j hjn'

theorem extend_radius_old (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r)
    {j : ℕ} (hj : j ≤ n) : (S.extend r hr).radius j = S.radius j := by
  exact Function.update_of_ne (by omega) _ _

theorem extend_radius_new (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r) :
    (S.extend r hr).radius (n + 1) = r := Function.update_self _ _ _

theorem extend_center_old (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r)
    {j : ℕ} (hj : j ≤ n) : (S.extend r hr).center j = S.center j := by
  simp only [center, S.extend_radius_old r hr hj]

theorem extend_center_new (S : DiscSchedule n) (r : ℝ) (hr : S.radius n + 5 < r) :
    (S.extend r hr).center (n + 1) = r := by
  simp [center, S.extend_radius_new r hr]

theorem control_mono (S : DiscSchedule n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    variableControlDisc (S.radius i) ⊆ variableControlDisc (S.radius j) :=
  closedBall_subset_closedBall (S.radius_mono hij hj)

theorem initial_control_subset_interior (S : DiscSchedule n) (hn : 0 < n) :
    controlDisc 0 ⊆ interior (variableControlDisc (S.radius n)) := by
  have H := S.radius_lower le_rfl
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  intro z hz
  apply ball_subset_interior_closedBall
  have hz' : dist z (-3 : ℂ) ≤ 1 := by simpa [controlDisc] using hz
  change dist z (-3 : ℂ) < S.radius n
  linarith

theorem initial_control_subset (S : DiscSchedule n) :
    controlDisc 0 ⊆ variableControlDisc (S.radius n) := by
  have H := S.radius_mono (Nat.zero_le n) le_rfl
  rw [S.initial] at H
  simpa [controlDisc, variableControlDisc] using
    (closedBall_subset_closedBall H : closedBall (-3 : ℂ) 1 ⊆ closedBall (-3) (S.radius n))

end DiscSchedule
end EremenkosConjecture
