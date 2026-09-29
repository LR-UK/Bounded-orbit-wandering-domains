module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Simultaneously increasing the scale and time of distinct encounters -/

open Function

namespace SurfaceDynamics

theorem exists_increasing_distinct_selection
    {X : Type*} (P : ℕ → ℕ → X → Prop)
    (hP : ∀ m N : ℕ, ∀ E : Finset X, ∃ n, N ≤ n ∧ ∃ s, s ∉ E ∧ P m n s) :
    ∃ (μ φ : ℕ → ℕ) (s : ℕ → X),
      StrictMono μ ∧ StrictMono φ ∧ Injective s ∧ ∀ k, P (μ k) (φ k) (s k) := by
  classical
  let A := ℕ × ℕ × X
  let Q : A → Prop := fun a => P a.1 a.2.1 a.2.2
  let r : A → A → Prop := fun a b => a.1 < b.1 ∧ a.2.1 < b.2.1 ∧ a.2.2 ≠ b.2.2
  have hchoose : ∀ T : Finset A, (∀ a ∈ T, Q a) → ∃ b, Q b ∧ ∀ a ∈ T, r a b := by
    intro T _
    let m := T.sup (fun a => a.1) + 1
    let N := T.sup (fun a => a.2.1) + 1
    obtain ⟨n, hn, s, hs, hPs⟩ := hP m N (T.image (fun a => a.2.2))
    refine ⟨(m, n, s), hPs, ?_⟩
    intro a ha
    refine ⟨Nat.lt_succ_of_le (Finset.le_sup ha), ?_, ?_⟩
    · exact lt_of_lt_of_le
        (Nat.lt_succ_of_le (Finset.le_sup (f := fun a : A => a.2.1) ha)) hn
    · intro he
      exact hs (Finset.mem_image.mpr ⟨a, ha, he⟩)
  obtain ⟨a, ha, har⟩ := exists_seq_of_forall_finset_exists Q r hchoose
  refine ⟨fun k => (a k).1, fun k => (a k).2.1, fun k => (a k).2.2,
    fun i j hij => (har i j hij).1, fun i j hij => (har i j hij).2.1, ?_, ha⟩
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim ((har i j hlt).2.2 hij)
  · exact heq
  · exact False.elim ((har j i hgt).2.2 hij.symm)

end SurfaceDynamics
