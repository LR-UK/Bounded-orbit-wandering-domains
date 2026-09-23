import HolomorphicLifting
import FunctionTheory.Conformal.SchottkyConfinement

open Set Metric Function

namespace AreaDeficit

/-- Uniform local lifts for omitted-values disc maps. The radius is chosen
before the map, the additional omitted set E, and the local covering.

The covering over the target disc minus E is an explicit hypothesis here;
`compact_analytic_covering` constructs it for proper local charts. This
theorem neither assumes nor constructs a universal hyperbolic covering. -/
theorem exists_uniform_local_lifting_radius
    {C : Set ℂ} (hC : IsCompact C) {a b : ℂ} (hab : a ≠ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ (f p : ℂ → ℂ) (K E : Set ℂ) (y : ℂ),
      AnalyticOnNhd ℂ p (ball (0 : ℂ) 1) →
      (∀ z ∈ ball (0 : ℂ) 1, p z ≠ a) →
      (∀ z ∈ ball (0 : ℂ) 1, p z ≠ b) →
      (∀ z ∈ ball (0 : ℂ) 1, p z ∉ E) →
      p 0 ∈ C → y ∈ K → f y = p 0 →
      AnalyticOnNhd ℂ f K →
      IsCoveringMapOn (fun z : K => f z) (ball (p 0) ε \ E) →
      (∀ z ∈ K, f z ∈ ball (p 0) ε \ E → deriv f z ≠ 0) →
      ∃ h : ℂ → ℂ, h 0 = y ∧ MapsTo h (ball (0 : ℂ) r) K ∧
        EqOn (f ∘ h) p (ball (0 : ℂ) r) ∧
        DifferentiableOn ℂ h (ball (0 : ℂ) r) ∧
        ∀ z ∈ ball (0 : ℂ) r, HasDerivAt h (deriv p z / deriv f (h z)) z := by
  obtain ⟨r, hr, hr1, H⟩ :=
    FunctionTheory.exists_uniform_radius_of_compact_centres_omit_pair hC hab hε
  refine ⟨r, hr, hr1, ?_⟩
  intro f p K E y hp ha hb hE hpC hy hfy hf hcov hreg
  have hsub : ball (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := ball_subset_ball hr1.le
  have hmap : MapsTo p (ball (0 : ℂ) r) (ball (p 0) ε \ E) :=
    fun z hz => ⟨H p hp ha hb hpC hz, hE z (hsub hz)⟩
  have hsc : IsSimplyConnected (ball (0 : ℂ) r) := by
    let : ContractibleSpace (ball (0 : ℂ) r) :=
      (convex_ball (0 : ℂ) r).contractibleSpace ⟨0, mem_ball_self hr⟩
    change SimplyConnectedSpace (ball (0 : ℂ) r)
    infer_instance
  exact exists_holomorphic_covering_lift isOpen_ball hsc (mem_ball_self hr)
    hy hfy hcov hf (hp.differentiableOn.mono hsub) hmap hreg

end AreaDeficit
