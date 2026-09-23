import FunctionTheory.Conformal.JordanBoundary
import FunctionTheory.Conformal.CayleyCoordinates
import FunctionTheory.Conformal.ReflectionInjectivity

/-! # Conformal extension at a straight boundary point

If a Jordan domain agrees with the right halfplane near zero, normalize a disk
map so that one maps to zero. In Cayley coordinates it extends conformally
across zero and has positive real derivative there. Boundary injectivity is
deduced by reflection; no global boundary homeomorphism is assumed.
-/

open Set Metric Complex
open scoped ComplexConjugate

namespace FunctionTheory

theorem re_eq_zero_of_mem_frontier_of_halfplane_neighbourhood
    {Ω : Set ℂ} {r : ℝ} (hΩ : IsOpen Ω)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re)
    {w : ℂ} (hw : w ∈ frontier Ω) (hwr : w ∈ ball 0 r) : w.re = 0 := by
  have hcl : w ∈ closure (ball (0 : ℂ) r ∩ Ω) :=
    isOpen_ball.inter_closure ⟨hwr, frontier_subset_closure hw⟩
  have hsub : ball (0 : ℂ) r ∩ Ω ⊆ {z : ℂ | 0 ≤ z.re} :=
    fun z hz => ((hnear z hz.1).mp hz.2).le
  have hnonneg : 0 ≤ w.re :=
    closure_minimal hsub (isClosed_le continuous_const Complex.continuous_re) hcl
  have hnot : w ∉ Ω := (hΩ.frontier_eq ▸ hw).2
  exact le_antisymm (le_of_not_gt (fun h => hnot ((hnear w hwr).mpr h))) hnonneg

/-- Local conformal reflection of a disk map at a straight target boundary.
The closed-disk continuity can be supplied by Carathéodory's theorem. -/
theorem exists_positive_reflection_of_disc_map_at_one
    {Ω : Set ℂ} {G : ℂ → ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 < r)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re)
    (hGc : ContinuousOn G (closedBall 0 1))
    (hGd : DifferentiableOn ℂ G (ball 0 1)) (hGbij : BijOn G (ball 0 1) Ω)
    (hG1 : G 1 = 0) :
    ∃ (δ : ℝ) (F : ℂ → ℂ) (a : ℝ), 0 < δ ∧
      DifferentiableOn ℂ F (ball 0 δ) ∧ InjOn F (ball 0 δ) ∧
      EqOn F (fun z => G (cayleyCoordinate z))
        (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re}) ∧
      F 0 = 0 ∧ 0 < a ∧ deriv F 0 = (a : ℂ) ∧
      (∀ z ∈ ball 0 δ, F (-conj z) = -conj (F z)) ∧
      MapsTo F (ball 0 δ ∩ {z : ℂ | 0 < z.re}) {w : ℂ | 0 < w.re} := by
  let H : ℂ → ℂ := fun z => G (cayleyCoordinate z)
  have hc : ContinuousOn cayleyCoordinate {z : ℂ | 0 ≤ z.re} :=
    fun z hz => (differentiableAt_cayleyCoordinate
      (cayley_denominator_ne_zero hz)).continuousAt.continuousWithinAt
  have hHc : ContinuousOn H {z : ℂ | 0 ≤ z.re} :=
    hGc.comp hc fun _ hz => cayleyCoordinate_mem_closedBall hz
  have hH0 : H 0 = 0 := by simpa [H] using hG1
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuousWithinAt_iff.mp
    (hHc 0 (show (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re} by simp)) r hr
  have hsmall : ∀ z ∈ ball (0 : ℂ) δ, 0 ≤ z.re → H z ∈ ball 0 r := by
    intro z hz hzre
    simpa only [hH0, mem_ball] using hδr hzre (mem_ball.mp hz)
  have hfront : G '' sphere (0 : ℂ) 1 ⊆ frontier Ω := by
    have hGc' : ContinuousOn G (closure (ball (0 : ℂ) 1)) := by
      simpa only [closure_ball _ one_ne_zero] using hGc
    simpa only [frontier_ball _ one_ne_zero, hGbij.image_eq] using
      TauCeti.image_frontier_subset_frontier_image isOpen_ball hGd hGbij.injOn
        hGc' (fun _ _ => rfl)
  have hHhol : DifferentiableOn ℂ H (ball 0 δ ∩ {z : ℂ | 0 < z.re}) := by
    have hcd : DifferentiableOn ℂ cayleyCoordinate
        (ball 0 δ ∩ {z : ℂ | 0 < z.re}) :=
      fun z hz => (differentiableAt_cayleyCoordinate
        (cayley_denominator_ne_zero (show 0 < z.re from hz.2).le)).differentiableWithinAt
    exact hGd.comp hcd fun z hz => cayleyCoordinate_mem_ball hz.2
  have hHaxis : ∀ z ∈ ball (0 : ℂ) δ, z.re = 0 → (H z).re = 0 := by
    intro z hz hre
    apply re_eq_zero_of_mem_frontier_of_halfplane_neighbourhood hΩ hnear
    · exact hfront (mem_image_of_mem G (cayleyCoordinate_mem_sphere hre))
    · exact hsmall z hz (le_of_eq hre.symm)
  have hHpos : ∀ z ∈ ball (0 : ℂ) δ, 0 < z.re → 0 < (H z).re := by
    intro z hz hre
    exact (hnear (H z) (hsmall z hz hre.le)).mp
      (hGbij.mapsTo (cayleyCoordinate_mem_ball hre))
  have hHi : InjOn H (ball 0 δ ∩ {z : ℂ | 0 < z.re}) := by
    intro z hz w hw hzw
    exact cayleyCoordinate_injOn
      (cayley_denominator_ne_zero (show 0 < z.re from hz.2).le)
      (cayley_denominator_ne_zero (show 0 < w.re from hw.2).le)
      (hGbij.injOn (cayleyCoordinate_mem_ball hz.2) (cayleyCoordinate_mem_ball hw.2) hzw)
  have hsym : MapsTo (fun z : ℂ => -conj z) (ball 0 δ) (ball 0 δ) :=
    fun z hz => by simpa only [mem_ball, dist_zero_right, norm_neg, norm_conj] using hz
  obtain ⟨F, hFd, hFH, hFs⟩ := exists_holomorphic_reflection_across_imaginary_axis
    isOpen_ball hsym (hHc.mono inter_subset_right) hHhol hHaxis
  have hF0 : F 0 = 0 := (hFH ⟨mem_ball_self hδ, by simp⟩).trans hH0
  have hFpos : ∀ z ∈ ball (0 : ℂ) δ, 0 < z.re → 0 < (F z).re := by
    intro z hz hp
    rw [hFH ⟨hz, hp.le⟩]
    exact hHpos z hz hp
  have hFi : InjOn F (ball 0 δ) :=
    injOn_of_imaginary_reflection isOpen_ball (convex_ball (0 : ℂ) δ).isPreconnected
      (mem_ball_self hδ) hsym hFd hFs hF0 hFpos (by
        intro z hz w hw heq
        apply hHi hz hw
        rwa [hFH ⟨hz.1, (show 0 < z.re from hz.2).le⟩,
          hFH ⟨hw.1, (show 0 < w.re from hw.2).le⟩] at heq)
  obtain ⟨a, ha, hFa⟩ := deriv_positive_real_of_halfplane_map
    (isOpen_ball.mem_nhds (mem_ball_self hδ))
    (hFd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))) hF0
    (TauCeti.deriv_ne_zero_of_injOn hFd isOpen_ball hFi (mem_ball_self hδ))
    (fun z hz hz0 => by
      rw [hFH ⟨hz, le_of_eq hz0.symm⟩]
      exact hHaxis z hz hz0) hFpos
  exact ⟨δ, F, a, hδ, hFd, hFi, hFH, hF0, ha, hFa, hFs,
    fun z hz => hFpos z hz.1 hz.2⟩

/-- The geometric straight-boundary hypothesis now supplies a reflected
conformal map and its positive derivative; continuity is obtained from the
public Carathéodory theorem rather than added as an assumption. -/
theorem exists_boundary_normalized_disc_map_with_positive_reflection
    {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩJ : TauCeti.IsJordanCurve (frontier Ω))
    (hz₀ : z₀ ∈ Ω) (h0 : (0 : ℂ) ∈ frontier Ω) (hr : 0 < r)
    (hnear : ∀ w ∈ ball (0 : ℂ) r, w ∈ Ω ↔ 0 < w.re) :
    ∃ (G F : ℂ → ℂ) (δ a : ℝ),
      ContinuousOn G (closedBall 0 1) ∧ DifferentiableOn ℂ G (ball 0 1) ∧
      BijOn G (ball 0 1) Ω ∧ G 0 = z₀ ∧ G 1 = 0 ∧ 0 < δ ∧
      DifferentiableOn ℂ F (ball 0 δ) ∧ InjOn F (ball 0 δ) ∧
      EqOn F (fun z => G (cayleyCoordinate z)) (ball 0 δ ∩ {z : ℂ | 0 ≤ z.re}) ∧
      F 0 = 0 ∧ 0 < a ∧ deriv F 0 = (a : ℂ) := by
  obtain ⟨G, hGc, hGd, hGbij, hG0, hG1, -, -⟩ :=
    exists_boundary_normalized_disc_map hΩo hΩc hΩb hΩJ hz₀ h0
  obtain ⟨δ, F, a, hδ, hFd, hFi, hFH, hF0, ha, hFa, -, -⟩ :=
    exists_positive_reflection_of_disc_map_at_one hΩo hr hnear hGc hGd hGbij hG1
  exact ⟨G, F, δ, a, hGc, hGd, hGbij, hG0, hG1, hδ, hFd, hFi, hFH, hF0, ha, hFa⟩

end FunctionTheory
