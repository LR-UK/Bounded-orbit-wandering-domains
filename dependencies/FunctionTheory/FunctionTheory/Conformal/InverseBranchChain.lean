import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- Compose a finite sequence of backward branches in orbit order. -/
def pullbackChain {α : Type*} (β : ℕ → α → α) : ℕ → α → α
  | 0 => id
  | n+1 => pullbackChain β n ∘ β n

theorem mapsTo_pullbackChain {α : Type*} {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j)) :
    MapsTo (pullbackChain β n) (D n) (D 0) := by
  induction n with
  | zero => exact fun _ hz => hz
  | succ n ih =>
    exact (ih (fun j hj => hb j (by omega))).comp (hb n (by omega))

theorem analyticOnNhd_pullbackChain {β : ℕ → ℂ → ℂ} {D : ℕ → Set ℂ} {n : ℕ}
    (ha : ∀ j < n, AnalyticOnNhd ℂ (β j) (D (j+1)))
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j)) :
    AnalyticOnNhd ℂ (pullbackChain β n) (D n) := by
  induction n with
  | zero => exact analyticOnNhd_id
  | succ n ih =>
    exact (ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))).comp
      (ha n (by omega)) (hb n (by omega))

/-- A finite backward chain is a right inverse of the corresponding iterate.
Only the finitely many indicated branch domains are involved. -/
theorem iterate_pullbackChain_rightInv {α : Type*} {f : α → α}
    {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hi : ∀ j < n, ∀ z ∈ D (j+1), f (β j z) = z) :
    ∀ z ∈ D n, f^[n] (pullbackChain β n z) = z := by
  induction n with
  | zero => intro z _; rfl
  | succ n ih =>
    intro z hz
    rw [pullbackChain, Function.comp_apply, Function.iterate_succ_apply']
    rw [ih (fun j hj => hb j (by omega)) (fun j hj => hi j (by omega))
      _ (hb n (by omega) hz)]
    exact hi n (by omega) z hz

/-- All intermediate points of the pulled-back orbit lie in their assigned
domains. This supplies the margins needed in finite-iterate approximation. -/
theorem iterate_pullbackChain_mem {α : Type*} {f : α → α}
    {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hi : ∀ j < n, ∀ z ∈ D (j+1), f (β j z) = z) :
    ∀ z ∈ D n, ∀ j ≤ n, f^[j] (pullbackChain β n z) ∈ D j := by
  induction n with
  | zero =>
    intro z hz j hj
    have hj0 : j=0 := by omega
    subst j
    exact hz
  | succ n ih =>
    intro z hz j hj
    by_cases hjn : j=n+1
    · subst j
      rw [iterate_pullbackChain_rightInv hb hi z hz]
      exact hz
    · change f^[j] (pullbackChain β n (β n z)) ∈ D j
      exact ih (fun k hk => hb k (by omega)) (fun k hk => hi k (by omega))
        _ (hb n (by omega) hz) j (by omega)

/-- Nonexpanding backward branches give a nonexpanding full backward chain. -/
theorem dist_pullbackChain_le {α : Type*} [PseudoMetricSpace α]
    {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hc : ∀ j < n, ∀ z ∈ D (j+1), ∀ w ∈ D (j+1),
      dist (β j z) (β j w) ≤ dist z w) :
    ∀ z ∈ D n, ∀ w ∈ D n,
      dist (pullbackChain β n z) (pullbackChain β n w) ≤ dist z w := by
  induction n with
  | zero => intro z _ w _; exact le_rfl
  | succ n ih =>
    intro z hz w hw
    exact (ih (fun j hj => hb j (by omega)) (fun j hj => hc j (by omega))
      _ (hb n (by omega) hz) _ (hb n (by omega) hw)).trans (hc n (by omega) z hz w hw)

/-- A new first step into a backward channel followed by an exit step
realises the desired model in exactly n+2 iterates. -/
theorem return_iterate_eq_of_pullback_head {α : Type*} {f φ ω : α → α}
    {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ} {z w : α}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hi : ∀ j < n, ∀ v ∈ D (j+1), f (β j v) = v)
    (hw : w ∈ D n) (hhead : f z = pullbackChain β n w)
    (hexit : f w = ω w) (hω : ω w = φ z) :
    f^[n+2] z = φ z := by
  calc
    f^[n+2] z = f (f^[n] (f z)) := by
      rw [show n+2 = (n+1)+1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply]
    _ = f w := by rw [hhead, iterate_pullbackChain_rightInv hb hi w hw]
    _ = φ z := hexit.trans hω

end FunctionTheory
