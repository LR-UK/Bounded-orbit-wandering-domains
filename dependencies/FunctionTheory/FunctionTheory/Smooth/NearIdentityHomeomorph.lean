import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic

open Set Metric
open scoped NNReal

namespace FunctionTheory

set_option autoImplicit false

/-- Adding a map with Lipschitz constant strictly below one to the identity
gives a global homeomorphism of a complete normed additive group. Surjectivity
is supplied by the contraction mapping theorem, not just local invertibility. -/
theorem exists_homeomorph_eq_add_of_lipschitz_lt_one
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    ∃ e : E ≃ₜ E, ∀ x, e x = x + u x := by
  classical
  let f : E → E := fun x => x + u x
  have hkR : (k : ℝ) < 1 := by exact_mod_cast hk
  have hc : 0 < 1 - (k : ℝ) := sub_pos.mpr hkR
  have hlower : ∀ x y, (1 - (k : ℝ)) * dist x y ≤ dist (f x) (f y) := by
    intro x y
    have heq : x - y = (f x - f y) - (u x - u y) := by dsimp [f]; abel
    have htri : dist x y ≤ dist (f x) (f y) + dist (u x) (u y) := by
      rw [dist_eq_norm, heq]
      simpa only [dist_eq_norm] using norm_sub_le (f x - f y) (u x - u y)
    have hLip := hu.dist_le_mul x y
    linarith
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := hlower x y
    rw [hxy, dist_self] at h
    apply dist_eq_zero.mp
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hsurj : Function.Surjective f := by
    intro y
    let g : E → E := fun x => y - u x
    have hLip : LipschitzWith k g := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [g, dist_sub_left] using hu.dist_le_mul a b
    have hg : ContractingWith k g := ⟨hk, hLip⟩
    let x := ContractingWith.fixedPoint g hg
    have hx : y - u x = x := hg.fixedPoint_isFixedPt
    exact ⟨x, eq_sub_iff_add_eq.mp hx.symm⟩
  let e : E ≃ E := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun _ => rfl⟩
  · exact continuous_id.add hu.continuous
  · apply Metric.continuous_iff.mpr
    intro x ε hε
    refine ⟨(1 - (k : ℝ)) * ε, mul_pos hc hε, ?_⟩
    intro y hy
    change dist (e.symm y) (e.symm x) < ε
    have h := hlower (e.symm y) (e.symm x)
    change (1 - (k : ℝ)) * dist (e.symm y) (e.symm x) ≤
      dist (e (e.symm y)) (e (e.symm x)) at h
    simp only [e.apply_symm_apply] at h
    nlinarith

end FunctionTheory
