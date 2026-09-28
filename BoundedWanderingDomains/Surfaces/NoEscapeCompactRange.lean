/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationEscape
import Mathlib.Topology.Compactness.SigmaCompact

open Set Function Filter Topology OnePoint

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SigmaCompactSpace X]

/-- Failure of every compact-escaping subsequence bounds the whole sequence
in a compact subset of the original space. -/
theorem compact_range_of_no_escaping_subsequence (u : ℕ → X)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : OnePoint X)) atTop (𝓝 (∞ : OnePoint X))) :
    ∃ K : Set X, IsCompact K ∧ ∀ n, u n ∈ K := by
  classical
  by_contra hn
  let K := CompactExhaustion.choice X
  have hout : ∀ n m : ℕ, ∃ k, m < k ∧ u k ∉ K n := by
    intro n m
    by_contra hh
    push Not at hh
    apply hn
    refine ⟨K n ∪ u '' (↑(Finset.range (m + 1)) : Set ℕ),
      (K.isCompact n).union ((Finset.finite_toSet _).image u).isCompact, ?_⟩
    intro k
    by_cases hk : m < k
    · exact Or.inl (hh k hk)
    · exact Or.inr ⟨k, by simpa using (show k < m + 1 by omega), rfl⟩
  choose pick hpick using hout
  let φ : ℕ → ℕ := Nat.rec (pick 0 0) (fun n k => pick (n + 1) k)
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ (fun n => (hpick (n + 1) (φ n)).1)
  have hφout : ∀ n, u (φ n) ∉ K n := by
    intro n
    cases n with
    | zero => exact (hpick 0 0).2
    | succ n => exact (hpick (n + 1) (φ n)).2
  apply hno
  refine ⟨φ, hφ, (tendsto_infty_iff_leaves_compacts _).mpr ?_⟩
  intro L hL
  obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hL
  filter_upwards [eventually_ge_atTop m] with n hn
  exact fun hu => hφout n (K.subset hn (hm hu))

end SurfaceDynamics
