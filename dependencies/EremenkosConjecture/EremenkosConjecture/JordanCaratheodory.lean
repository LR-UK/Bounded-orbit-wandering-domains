import EremenkosConjecture.JordanBoundaryApproach
import EremenkosConjecture.JordanBoundaryCompatibility
import FunctionTheory.Conformal.JordanBoundary
import TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster

/-! # Carathéodory homeomorphism for bounded Jordan domains

Tau Ceti supplies continuous extension and boundary injectivity from connected
approach regions. The latter property was proved for Jordan domains using the
public Schoenflies closed-interior chart. A continuous bijection of the compact
closed disk onto the domain closure is then a homeomorphism.
-/

open Set Metric

namespace EremenkosConjecture

theorem injOn_closedBall_of_jordan_image {Ω : Set ℂ} {g G : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hbij : BijOn g (ball 0 1) Ω)
    (hΩb : Bornology.IsBounded Ω) (hJ : IsComplexJordanCurve (frontier Ω))
    (hGc : ContinuousOn G (closedBall 0 1)) (hGg : EqOn G g (ball 0 1)) :
    InjOn G (closedBall 0 1) := by
  have hΩo : IsOpen Ω := by
    rw [← hbij.image_eq]
    exact TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hg hbij.injOn
  have hΩc : IsConnected Ω := by
    rw [← hbij.image_eq]
    exact ((convex_ball (0 : ℂ) 1).isConnected
      ⟨0, mem_ball_self one_pos⟩).image g hg.continuousOn
  apply TauCeti.injOn_closedBall_of_isPreconnected_image_approach one_pos hg hbij.injOn hGc hGg
  rw [hbij.image_eq]
  intro a ha
  exact isPreconnectedApproachAt_bounded_jordan_domain hΩo hΩc hΩb hJ ha.1

theorem exists_homeomorph_extension_of_jordan_bijOn {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hbij : BijOn g (ball 0 1) Ω)
    (hΩb : Bornology.IsBounded Ω) (hJ : IsComplexJordanCurve (frontier Ω)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
      ∀ z (hz : z ∈ ball (0 : ℂ) 1),
        (e ⟨z, ball_subset_closedBall hz⟩ : ℂ) = g z := by
  obtain ⟨G, hGc, hGg, hGcl, -⟩ :=
    FunctionTheory.exists_continuous_extension_of_jordan_bijOn hg hbij hΩb hJ.tauCeti
  have hGi := injOn_closedBall_of_jordan_image hg hbij hΩb hJ hGc hGg
  have hmap : MapsTo G (closedBall (0 : ℂ) 1) (closure Ω) :=
    mapsTo_iff_image_subset.mpr hGcl.subset
  let f : closedBall (0 : ℂ) 1 → closure Ω := fun z => ⟨G z, hmap z.property⟩
  have hfc : Continuous f := hGc.domRestrict.subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (hGi x.property y.property (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := hGcl.symm ▸ hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω :=
    (Equiv.ofBijective f hfb).toHomeomorphOfContinuousClosed hfc hfc.isClosedMap
  exact ⟨e, fun z hz => hGg hz⟩

end EremenkosConjecture
