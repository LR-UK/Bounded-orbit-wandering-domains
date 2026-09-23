import EremenkosConjecture.ScaffoldingReturnMap

open Set Filter Function
open scoped Topology

namespace EremenkosConjecture.Scaffolding

/-- Uniform leftward compression gives the large-real-part estimate on the
whole continuum through the return branch, including the whole return block. -/
theorem eventually_return_block_large_on_set
    {f : ℂ → ℂ} {ψ φ : ℕ → ℂ → ℂ} {X : Set ℂ} {j : ℕ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (horbit : ∀ n, ∀ k < j, MapsTo (fun z => (f^[k]) (ψ n z)) X (insetSourceStrip k))
    (hfinal : ∀ n, EqOn (fun z => (f^[j]) (ψ n z)) (φ n) X)
    (hleft : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ X, (φ n x).re < M)
    {R : ℝ} (hR : 1 / 2 ≤ R) :
    ∀ᶠ n in atTop, ∀ x ∈ X, ∀ k ≤ j, R ≤ |((f^[k]) (ψ n x)).re| := by
  filter_upwards [hleft (-(6 : ℝ) ^ j * (R + 1))] with n hn
  intro x hx
  exact return_map_large_real_parts hclose (horbit n) (hfinal n) hR hx (hn x hx)

/-- Equation (7.3), once the decorated-domain family and its return branches
have been constructed: the inequality is simultaneous for every point of X. -/
theorem eventually_return_map_real_part_gt
    {f : ℂ → ℂ} {ψ φ : ℕ → ℂ → ℂ} {X : Set ℂ} {j : ℕ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (horbit : ∀ n, ∀ k < j, MapsTo (fun z => (f^[k]) (ψ n z)) X (insetSourceStrip k))
    (hfinal : ∀ n, EqOn (fun z => (f^[j]) (ψ n z)) (φ n) X)
    (hleft : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ X, (φ n x).re < M)
    (R : ℝ) :
    ∀ᶠ n in atTop, ∀ x ∈ X, R < |(ψ n x).re| := by
  let R' := max 1 (R + 1)
  have hR' : 1 / 2 ≤ R' := by have := le_max_left (1 : ℝ) (R + 1); dsimp [R']; linarith
  filter_upwards [eventually_return_block_large_on_set hclose horbit hfinal hleft hR'] with n hn
  intro x hx
  have h := hn x hx 0 (Nat.zero_le j)
  simp only [iterate_zero, id_eq] at h
  have hRR' : R < R' := by have := le_max_right (1 : ℝ) (R + 1); dsimp [R']; linarith
  exact hRR'.trans_le h

end EremenkosConjecture.Scaffolding
