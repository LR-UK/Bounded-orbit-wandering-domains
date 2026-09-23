import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import FunctionTheory.Conformal.RiemannMapping
import Mathlib.Analysis.Complex.Isometry

/-! # Boundary extension and a distinguished boundary point

Carathéodory continuity is the attributed public Tau Ceti theorem. The first
result records its boundary and closure images. The second normalizes a disk
map by an interior point and a prescribed boundary point, rather than by the
argument of its derivative. It does not assume boundary injectivity.
-/

open Set Metric Function

namespace FunctionTheory

theorem exists_continuous_extension_of_jordan_bijOn
    {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hbij : BijOn g (ball 0 1) Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩJ : TauCeti.IsJordanCurve (frontier Ω)) :
    ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧ EqOn G g (ball 0 1) ∧
      G '' closedBall 0 1 = closure Ω ∧ G '' sphere 0 1 = frontier Ω := by
  obtain ⟨G, hGc, hGg⟩ :=
    TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier
      one_pos hg hbij.injOn (hbij.image_eq.symm ▸ hΩb) (hbij.image_eq.symm ▸ hΩJ)
  have hGc' : ContinuousOn G (closure (ball (0 : ℂ) 1)) := by
    simpa only [closure_ball _ one_ne_zero] using hGc
  refine ⟨G, hGc, hGg, ?_, ?_⟩
  · simpa only [closure_ball _ one_ne_zero, hbij.image_eq] using
      TauCeti.image_closure_eq_closure_image isBounded_ball hGc' hGg
  · simpa only [frontier_ball _ one_ne_zero, hbij.image_eq] using
      TauCeti.image_frontier_eq_frontier_image isOpen_ball isBounded_ball
        hg hbij.injOn hGc' hGg

/-- A bounded simply connected Jordan domain admits a conformal disk map
continuous on the closed disk, taking zero to a chosen interior point and one
to a chosen boundary point. No unproved boundary homeomorphism is used. -/
theorem exists_boundary_normalized_disc_map {Ω : Set ℂ} {z₀ p : ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩJ : TauCeti.IsJordanCurve (frontier Ω))
    (hz₀ : z₀ ∈ Ω) (hp : p ∈ frontier Ω) :
    ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧
      DifferentiableOn ℂ G (ball 0 1) ∧ BijOn G (ball 0 1) Ω ∧
      G 0 = z₀ ∧ G 1 = p ∧
      G '' closedBall 0 1 = closure Ω ∧ G '' sphere 0 1 = frontier Ω := by
  have hΩne : Ω ≠ univ := by
    intro h
    exact NormedSpace.unbounded_univ ℝ ℂ (h ▸ hΩb)
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn hΩo hΩc hΩne hz₀
  let g := invFunOn f Ω
  have hg : DifferentiableOn ℂ g (ball 0 1) := by
    simpa only [hf.image_eq] using DifferentiableOn.invFunOn hf.differentiableOn hΩo hf.injOn
  have hbij : BijOn g (ball 0 1) Ω := BijOn.symm hf.bijOn.invOn_invFunOn.symm hf.bijOn
  have hg0 : g 0 = z₀ := by
    simpa only [hf.map_base] using hf.injOn.leftInvOn_invFunOn hz₀
  obtain ⟨G, hGc, hGg, hGcl, hGfr⟩ :=
    exists_continuous_extension_of_jordan_bijOn hg hbij hΩb hΩJ
  obtain ⟨u, hu, hup⟩ : ∃ u ∈ sphere (0 : ℂ) 1, G u = p := by
    rw [← hGfr] at hp
    exact hp
  have hGu : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
  have hrot : BijOn (fun w : ℂ => u * w) (ball 0 1) (ball 0 1) := by
    have h := (rotation ⟨u, hu⟩).injective.injOn.bijOn_image
      (s := ball (0 : ℂ) 1)
    rwa [LinearIsometryEquiv.image_ball, map_zero] at h
  have hrotcl : MapsTo (fun w : ℂ => u * w) (closedBall 0 1) (closedBall 0 1) := by
    intro w hw
    simpa only [mem_closedBall, dist_zero_right, norm_mul, hGu, one_mul] using hw
  have hGd : DifferentiableOn ℂ G (ball 0 1) := hg.congr fun _ hz => hGg hz
  have hGbij : BijOn G (ball 0 1) Ω := hbij.congr fun _ hz => (hGg hz).symm
  let H : ℂ → ℂ := fun w => G (u * w)
  have hHc : ContinuousOn H (closedBall 0 1) :=
    hGc.comp (continuous_const.mul continuous_id).continuousOn hrotcl
  have hHd : DifferentiableOn ℂ H (ball 0 1) :=
    hGd.comp ((differentiable_const u).mul differentiable_id).differentiableOn hrot.mapsTo
  have hHbij : BijOn H (ball 0 1) Ω := hGbij.comp hrot
  have hHcl : ContinuousOn H (closure (ball (0 : ℂ) 1)) := by
    simpa only [closure_ball _ one_ne_zero] using hHc
  refine ⟨H, hHc, hHd, hHbij, ?_, ?_, ?_, ?_⟩
  · simpa [H] using (hGg (mem_ball_self one_pos)).trans hg0
  · simpa [H] using hup
  · simpa only [closure_ball _ one_ne_zero, hHbij.image_eq] using
      TauCeti.image_closure_eq_closure_image isBounded_ball hHcl (fun _ _ => rfl)
  · simpa only [frontier_ball _ one_ne_zero, hHbij.image_eq] using
      TauCeti.image_frontier_eq_frontier_image isOpen_ball isBounded_ball
        hHd hHbij.injOn hHcl (fun _ _ => rfl)

/-- The boundary-normalized map with its actual closed-disk domain. The
interior map is a homeomorphism onto the Jordan domain, holomorphic both ways. -/
theorem exists_boundary_normalized_disc_map_on_domain {Ω : Set ℂ} {z₀ p : ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩJ : TauCeti.IsJordanCurve (frontier Ω))
    (hz₀ : z₀ ∈ Ω) (hp : p ∈ frontier Ω) :
    ∃ (e : ball (0 : ℂ) 1 ≃ₜ Ω) (G : C(closedBall (0 : ℂ) 1, ℂ)),
      IsHolomorphicFunctionOn (ball (0 : ℂ) 1) (fun z => (e z : ℂ)) ∧
      IsHolomorphicFunctionOn Ω (fun z => (e.symm z : ℂ)) ∧
      (∀ z : ball (0 : ℂ) 1, G ⟨z, ball_subset_closedBall z.property⟩ = (e z : ℂ)) ∧
      G ⟨0, mem_closedBall_self zero_le_one⟩ = z₀ ∧
      G ⟨1, by simp⟩ = p ∧ range G = closure Ω := by
  obtain ⟨g, hgc, hgd, hbij, hg0, hg1, hgcl, -⟩ :=
    exists_boundary_normalized_disc_map hΩo hΩc hΩb hΩJ hz₀ hp
  let e := hgd.toHomeomorphOfBijOn isOpen_ball hbij
  let G : C(closedBall (0 : ℂ) 1, ℂ) := ⟨fun z => g z, hgc.domRestrict⟩
  have hinv : DifferentiableOn ℂ (invFunOn g (ball 0 1)) Ω := by
    simpa only [hbij.image_eq] using DifferentiableOn.invFunOn hgd isOpen_ball hbij.injOn
  refine ⟨e, G, ?_, ?_, fun _ => rfl, hg0, hg1, ?_⟩
  · simpa only [e, DifferentiableOn.toHomeomorphOfBijOn_apply] using
      isHolomorphicFunctionOn_restrict isOpen_ball hgd
  · simpa only [e, DifferentiableOn.toHomeomorphOfBijOn_symm_apply] using
      isHolomorphicFunctionOn_restrict hΩo hinv
  · exact (Set.range_domRestrict _ _).trans hgcl

end FunctionTheory
