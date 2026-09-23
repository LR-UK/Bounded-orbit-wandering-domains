import FunctionTheory.Conformal.InverseBranchChain
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic right inverse on an open domain forces the forward map
to be holomorphic at every point of its image. No regularity of the forward
map away from that image is assumed. -/
theorem analyticAt_of_holomorphic_right_inverse
    {f b : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hb : AnalyticOnNhd ℂ b V) (hfb : ∀ z ∈ V, f (b z) = z)
    {z : ℂ} (hz : z ∈ V) : AnalyticAt ℂ f (b z) := by
  have hinj : InjOn b V := by
    intro x hx y hy hxy
    calc
      x = f (b x) := (hfb x hx).symm
      _ = f (b y) := congrArg f hxy
      _ = y := hfb y hy
  have hd : deriv b z ≠ 0 :=
    TauCeti.deriv_ne_zero_of_injOn hb.differentiableOn hV hinj hz
  have heq : (fun w : ℂ => w) =ᶠ[𝓝 z] (f ∘ b) := by
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (hfb w hw).symm
  have hc : AnalyticAt ℂ (f ∘ b) z := analyticAt_id.congr heq
  exact (analyticAt_comp_iff_of_deriv_ne_zero (hb z hz) hd).mp hc

/-- Every intermediate point of a finite inverse-branch chain is a regular
point of the forward map. In particular, assigned finite values at poles
cannot create spurious finite return orbits. -/
theorem iterate_pullbackChain_analytic
    {f : ℂ → ℂ} {β : ℕ → ℂ → ℂ} {D : ℕ → Set ℂ} {n : ℕ}
    (hD : ∀ j ≤ n, IsOpen (D j))
    (ha : ∀ j < n, AnalyticOnNhd ℂ (β j) (D (j+1)))
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hi : ∀ j < n, ∀ z ∈ D (j+1), f (β j z) = z) :
    ∀ z ∈ D n, ∀ j < n, AnalyticAt ℂ f (f^[j] (pullbackChain β n z)) := by
  induction n with
  | zero => intro z hz j hj; omega
  | succ n ih =>
    intro z hz j hj
    by_cases hjn : j<n
    · exact ih (fun k hk => hD k (by omega)) (fun k hk => ha k (by omega))
        (fun k hk => hb k (by omega)) (fun k hk => hi k (by omega))
        _ (hb n (by omega) hz) j hjn
    · have hjeq : j=n := by omega
      subst j
      change AnalyticAt ℂ f (f^[n] (pullbackChain β n (β n z)))
      rw [iterate_pullbackChain_rightInv (fun k hk => hb k (by omega))
        (fun k hk => hi k (by omega)) _ (hb n (by omega) hz)]
      exact analyticAt_of_holomorphic_right_inverse (hD (n+1) le_rfl)
        (ha n (by omega)) (hi n (by omega)) hz

end FunctionTheory
