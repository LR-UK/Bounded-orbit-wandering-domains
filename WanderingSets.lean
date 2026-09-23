import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Tactic

open Set Function

namespace AreaDeficit

/-- The full forward orbit of a set. -/
def forwardOrbit (f : α → α) (B : Set α) : Set α := ⋃ n : ℕ, f^[n] '' B

/-- Pairwise disjoint forward images; injectivity is a separate condition. -/
def HasDisjointForwardImages (f : α → α) (B : Set α) : Prop :=
  Pairwise (fun n m : ℕ => Disjoint (f^[n] '' B) (f^[m] '' B))

theorem subset_forwardOrbit (f : α → α) (B : Set α) : B ⊆ forwardOrbit f B := by
  intro x hx
  exact mem_iUnion.mpr ⟨0, by simpa using hx⟩

theorem image_forwardOrbit_subset (f : α → α) (B : Set α) :
    f '' forwardOrbit f B ⊆ forwardOrbit f B := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, y, hy, rfl⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨n + 1, y, hy, by simp [iterate_succ_apply']⟩

theorem image_forwardOrbit_eq_sdiff {f : α → α} {B : Set α}
    (hB : HasDisjointForwardImages f B) :
    f '' forwardOrbit f B = forwardOrbit f B \ B := by
  ext x
  constructor
  · intro hx
    refine ⟨image_forwardOrbit_subset f B hx, ?_⟩
    rintro hxB
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨n, z, hz, rfl⟩ := mem_iUnion.mp hy
    have hh := hB (show n + 1 ≠ 0 by omega)
    exact Set.disjoint_left.mp hh
      (show f (f^[n] z) ∈ f^[n+1] '' B from ⟨z, hz, by simp [iterate_succ_apply']⟩)
      (by simpa using hxB)
  · rintro ⟨hx, hxB⟩
    obtain ⟨n, y, hy, rfl⟩ := mem_iUnion.mp hx
    cases n with
    | zero => exact False.elim (hxB (by simpa using hy))
    | succ n =>
      exact ⟨f^[n] y, mem_iUnion.mpr ⟨n, y, hy, rfl⟩, by simp [iterate_succ_apply']⟩

/-- Injectivity on all iterates of the initial set implies injectivity on its
full forward orbit, provided the successive images are disjoint. -/
theorem injOn_forwardOrbit {f : α → α} {B : Set α}
    (hB : HasDisjointForwardImages f B)
    (hi : ∀ n : ℕ, InjOn (f^[n]) B) : InjOn f (forwardOrbit f B) := by
  intro x hx y hy hxy
  obtain ⟨n, a, ha, rfl⟩ := mem_iUnion.mp hx
  obtain ⟨m, b, hb, rfl⟩ := mem_iUnion.mp hy
  have hab : f^[n+1] a = f^[m+1] b := by simpa [iterate_succ_apply'] using hxy
  have hnm : n = m := by
    by_contra hne
    have hd := hB (show n + 1 ≠ m + 1 by omega)
    exact Set.disjoint_left.mp hd ⟨a, ha, rfl⟩ ⟨b, hb, hab.symm⟩
  subst m
  have he := hi (n+1) ha hb hab
  exact congrArg (f^[n]) he

end AreaDeficit
