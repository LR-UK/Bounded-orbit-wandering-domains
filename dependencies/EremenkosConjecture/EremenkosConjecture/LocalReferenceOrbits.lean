import EremenkosConjecture.LocalReference

open Set Function

namespace EremenkosConjecture

open Scaffolding

variable {f ψ : ℂ → ℂ} {e : OpenPartialHomeomorph ℂ ℂ}
  {j : ℕ} {B C : Set ℂ} (P : LocalReference f ψ e j B C)

theorem LocalReference.iterate_eq_old {A : Set ℂ} {N k : ℕ} (hk : k ≤ N)
    (horbit : ∀ i < N, MapsTo (f^[i]) A (background j)) :
    EqOn (P.g^[k]) (f^[k]) A := by
  intro z hz
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih (by omega)]
      exact P.background_eq (horbit k (by omega) hz)

theorem LocalReference.iterate_eq_return {N m k : ℕ} (hk : k ≤ m)
    (horbit : ∀ i < N, MapsTo (f^[i]) C (background j))
    (he : EqOn (f^[N]) e C)
    (hreturn : ∀ i < m, MapsTo (fun z => (f^[i]) (ψ z)) C (background j)) :
    EqOn (P.g^[N + 1 + k]) (fun z => (f^[k]) (ψ z)) C := by
  intro z hz
  change (P.g^[N + 1 + k]) z = (f^[k]) (ψ z)
  induction k with
  | zero =>
      simp only [add_zero, iterate_zero, id_eq]
      rw [iterate_succ_apply', P.iterate_eq_old le_rfl horbit hz, he hz]
      exact P.return_eq z hz
  | succ k ih =>
      rw [show N + 1 + (k + 1) = (N + 1 + k) + 1 by omega,
        iterate_succ_apply', ih (by omega), iterate_succ_apply']
      exact P.background_eq (hreturn k (by omega) hz)

theorem LocalReference.mapsTo_controlSet {N m k : ℕ} (hk : k < N + 1 + m)
    (horbit : ∀ i < N, MapsTo (f^[i]) C (background j))
    (he : EqOn (f^[N]) e C)
    (hreturn : ∀ i < m, MapsTo (fun z => (f^[i]) (ψ z)) C (background j)) :
    MapsTo (P.g^[k]) C ((background j ∪ e '' B) ∪ e '' C) := by
  intro z hz
  by_cases hkN : k < N
  · rw [P.iterate_eq_old hkN.le horbit hz]
    exact Or.inl (Or.inl (horbit k hkN hz))
  · by_cases hkN' : k = N
    · rw [hkN', P.iterate_eq_old le_rfl horbit hz, he hz]
      exact Or.inr (mem_image_of_mem e hz)
    · let i := k - (N + 1)
      have hi : i < m := by dsimp [i]; omega
      have hki : k = N + 1 + i := by dsimp [i]; omega
      rw [hki, P.iterate_eq_return hi.le horbit he hreturn hz]
      exact Or.inl (Or.inl (hreturn i hi hz))

end EremenkosConjecture
