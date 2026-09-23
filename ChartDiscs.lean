import RiemannMappingFull
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

open Set Metric Function
open scoped Topology

namespace AreaDeficit

/-- A disc of Euclidean radius r in a normalized Riemann coordinate.
For curvature −1 its intrinsic radius is 2 artanh r. -/
def chartDisc (u : ℂ → ℂ) (U : Set ℂ) (r : ℝ) : Set ℂ := U ∩ u ⁻¹' ball 0 r

theorem chartDisc_isOpen {u : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (r : ℝ) : IsOpen (chartDisc u U r) :=
  hu.continuousOn.isOpen_inter_preimage hU isOpen_ball

/-- Forward inclusion of equal-radius intrinsic discs is proved by
Schwarz's lemma in the normalized Riemann coordinates. -/
theorem mapsTo_chartDisc {f u v : ℂ → ℂ} {U V : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    (hub : BijOn u U (ball 0 1)) (hv : DifferentiableOn ℂ v V)
    (hvm : MapsTo v V (ball 0 1))
    (hf : DifferentiableOn ℂ f U) (hfm : MapsTo f U V)
    (hz : z ∈ U) (hu0 : u z = 0) (hv0 : v (f z) = 0)
    {r : ℝ} (hr1 : r < 1) :
    MapsTo f (chartDisc u U r) (chartDisc v V r) := by
  let p := invFunOn u U
  have hpm : MapsTo p (ball 0 1) U := by
    intro w hw
    exact invFunOn_mem (hub.surjOn hw)
  have hpd : DifferentiableOn ℂ p (ball 0 1) := by
    simpa only [hub.image_eq] using hu.invFunOn hU hub.injOn
  let F := v ∘ f ∘ p
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hv.comp (hf.comp hpd hpm) (hfm.comp hpm)
  have hFm : MapsTo F (ball 0 1) (closedBall 0 1) :=
    (hvm.comp (hfm.comp hpm)).mono_right ball_subset_closedBall
  have hp0 : p 0 = z := by
    rw [← hu0]
    exact hub.injOn.leftInvOn_invFunOn hz
  have hF0 : F 0 = 0 := by simp only [F, Function.comp_apply, hp0, hv0]
  intro x hx
  refine ⟨hfm hx.1, ?_⟩
  have hxn : ‖u x‖ < r := mem_ball_zero_iff.mp hx.2
  have h := Complex.norm_le_norm_of_mapsTo_ball hFd hFm hF0 (hxn.trans hr1)
  have hpx : p (u x) = x := hub.injOn.leftInvOn_invFunOn hx.1
  simpa only [mem_preimage, mem_ball_zero_iff, F, Function.comp_apply, hpx] using h.trans_lt hxn

/-- An injective function on each member of a wandering disc sequence
is injective on their union because their images lie in disjoint next
components. No injectivity on entire components is used. -/
theorem injOn_disc_union {f : ℂ → ℂ} {U D : ℕ → Set ℂ}
    (hdisj : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hDU : ∀ n, D n ⊆ U n) (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hi : ∀ n, InjOn f (D n)) : InjOn f (⋃ n, D n) := by
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hy
  have hnm : n = m := by
    by_contra hne
    exact disjoint_left.mp (hdisj (by omega : n + 1 ≠ m + 1))
      (hfm n (hDU n hn)) (hxy ▸ hfm m (hDU m hm))
  subst m
  exact hi n hn hm hxy

/-- The discs do not depend on the choice of normalized Riemann map. -/
theorem chartDisc_eq {u v : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hub : BijOn u U (ball 0 1))
    (hv : DifferentiableOn ℂ v U) (hvb : BijOn v U (ball 0 1))
    (hz : z ∈ U) (hu0 : u z = 0) (hv0 : v z = 0) {r : ℝ} (hr1 : r < 1) :
    chartDisc u U r = chartDisc v U r := by
  apply Subset.antisymm
  · exact mapsTo_chartDisc (f := id) hU hu hub hv hvb.mapsTo
      differentiableOn_id (mapsTo_id U) hz hu0 hv0 hr1
  · exact mapsTo_chartDisc (f := id) hU hv hvb hu hub.mapsTo
      differentiableOn_id (mapsTo_id U) hz hv0 hu0 hr1

/-- Intrinsic disc injectivity, expressed without choosing a global
hyperbolic-distance API. A normalized chart may be chosen separately
for each radius and time; chartDisc_eq proves independence of this choice.
The quantifier order allows the starting time to depend on the radius. -/
def EventuallyInjectiveOnLargeDiscs (f : ℂ → ℂ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ, ∀ n ≥ N, ∃ u : ℂ → ℂ,
    DifferentiableOn ℂ u (U n) ∧ BijOn u (U n) (ball 0 1) ∧ u (z n) = 0 ∧
      InjOn f (chartDisc u (U n) r)

end AreaDeficit

#print axioms AreaDeficit.mapsTo_chartDisc
