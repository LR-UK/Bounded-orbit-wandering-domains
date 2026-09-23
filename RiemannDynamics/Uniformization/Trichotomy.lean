/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.HolomorphicEquiv
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Assembly
import RiemannDynamics.Analysis.Winding.GridPrimitives.Primitives
import FunctionTheory.Conformal.RiemannMapping

/-!
# The uniformization trichotomy

Every simply connected domain of the Riemann sphere is biholomorphic to
exactly one of the unit disc, the plane, or the sphere
(`sphere_domain_trichotomy`), and — through a holomorphic embedding into the
sphere — the same holds for every abstract simply connected Riemann surface
(`uniformization_trichotomy`).

The route to the disc case is the Riemann mapping theorem for plane domains:
simple connectivity forces every connected component of the complement to be
unbounded (`unbounded_connectedComponentIn_compl_of_simplyConnectedSpace`),
which yields holomorphic primitives on the domain and hence the hypotheses of
the mapping theorem. The sphere case is Möbius normalization; the plane case
is the complement-of-one-point reading in the finite chart. The three models
are mutually non-biholomorphic: compactness separates `ℂ̂` from the other two,
and Liouville's theorem separates `ℂ` from the disc.

## Main statements

* `sphere_domain_trichotomy` — the trichotomy for domains `U : Opens ℂ̂`;
* `planar_dichotomy` — a simply connected plane domain is biholomorphic to
  the disc or to `ℂ`;
* `uniformization_trichotomy` — the trichotomy for abstract simply connected
  Riemann surfaces, reduced through
  `exists_diffeomorph_opens_sphere_of_simplyConnected`.
-/

open OnePoint Topology TopologicalSpace Metric
open scoped Manifold ContDiff

namespace RiemannDynamics

/-- The open unit disc as a plane domain, the disc model of the trichotomy. -/
def unitDiscOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-! ## The trichotomy for plane and sphere domains -/

/-- **Planar dichotomy**: a simply connected plane domain is biholomorphic to
the unit disc or to the plane. -/
theorem planar_dichotomy (U : Opens ℂ) (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  by_cases hne : (U : Set ℂ) = Set.univ
  · right
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    exact nonempty_diffeomorph_top ℂ
  · left
    obtain ⟨f, hf, hinj, himg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hsc
    exact nonempty_diffeomorph_of_injOn_differentiableOn U unitDiscOpens f hf hinj himg

/-- **The uniformization trichotomy for sphere domains**: a simply connected
domain of the Riemann sphere is biholomorphic to the unit disc, the plane, or
the whole sphere. -/
theorem sphere_domain_trichotomy (U : Opens ℂ̂) (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  by_cases huniv : (U : Set ℂ̂) = Set.univ
  · right; right
    have hU : U = ⊤ := Opens.ext (by simpa using huniv)
    subst hU
    exact nonempty_diffeomorph_top ℂ̂
  · -- A point omitted by `U`, to be moved to `∞` by a Möbius transformation.
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ̂, z₀ ∉ (U : Set ℂ̂) := by
      by_contra h
      push Not at h
      exact huniv (Set.eq_univ_of_forall h)
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) ℂ, g • z₀ = (∞ : ℂ̂) := by
      by_cases h0 : z₀ = ((0 : ℂ) : ℂ̂)
      · obtain ⟨g, -, -, hg⟩ := exists_gl_smul_eq_zero_one_infty
          (a := ((1 : ℂ) : ℂ̂)) (b := ((2 : ℂ) : ℂ̂)) (c := z₀)
          (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
          (by rw [h0, Ne, OnePoint.coe_eq_coe]; norm_num)
          (by rw [h0, Ne, OnePoint.coe_eq_coe]; norm_num)
        exact ⟨g, hg⟩
      · by_cases h1 : z₀ = ((1 : ℂ) : ℂ̂)
        · obtain ⟨g, -, -, hg⟩ := exists_gl_smul_eq_zero_one_infty
            (a := ((0 : ℂ) : ℂ̂)) (b := ((2 : ℂ) : ℂ̂)) (c := z₀)
            (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
            (by rw [h1, Ne, OnePoint.coe_eq_coe]; norm_num)
            (by rw [h1, Ne, OnePoint.coe_eq_coe]; norm_num)
          exact ⟨g, hg⟩
        · obtain ⟨g, -, -, hg⟩ := exists_gl_smul_eq_zero_one_infty
            (a := ((0 : ℂ) : ℂ̂)) (b := ((1 : ℂ) : ℂ̂)) (c := z₀)
            (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
            (Ne.symm h0) (Ne.symm h1)
          exact ⟨g, hg⟩
    -- Transport `U` by the Möbius biholomorphism; the image avoids `∞`.
    obtain ⟨e_g, he_g⟩ := exists_gl_smul_diffeomorph g
    obtain ⟨V, hVimg, ⟨e₁⟩⟩ := exists_diffeomorph_opens_image e_g U
    have hinfV : (∞ : ℂ̂) ∉ (V : Set ℂ̂) := by
      rw [hVimg, he_g]
      rintro ⟨u, huU, hu⟩
      exact hz₀ (MulAction.injective g (hu.trans hg.symm) ▸ huU)
    -- Read the image in the finite chart and apply the planar dichotomy.
    obtain ⟨W, hWimg, ⟨e₂⟩⟩ := exists_diffeomorph_opens_planar V hinfV
    have hscW : SimplyConnectedSpace ↥W :=
      simplyConnectedSpace_of_homeomorph (e₁.trans e₂).toHomeomorph hsc
    rcases planar_dichotomy W hscW with h | h
    · exact Or.inl (h.map fun f => (e₁.trans e₂).trans f)
    · exact Or.inr (Or.inl (h.map fun f => (e₁.trans e₂).trans f))

/-! ## Separation of the three models -/

/-- Liouville separation: the plane is not biholomorphic to the unit disc. -/
theorem not_nonempty_diffeomorph_complex_unitDisc :
    ¬ Nonempty (ℂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  -- The composite `F = Subtype.val ∘ e : ℂ → ℂ` is an entire function.
  have hFsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ e : ℂ → ℂ) :=
    contMDiff_subtype_val.comp e.contMDiff
  have hFdiff : Differentiable ℂ (Subtype.val ∘ e : ℂ → ℂ) :=
    hFsmooth.contDiff.differentiable (by simp)
  -- Its range lies in the unit ball, hence is bounded.
  have hFbdd : Bornology.IsBounded (Set.range (Subtype.val ∘ e : ℂ → ℂ)) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
      (Set.range_subset_iff.mpr fun z => (e z).2)
  -- Liouville: `F` takes the same value at `0` and `1`, contradicting injectivity.
  have h01 : (e 0 : ℂ) = (e 1 : ℂ) := hFdiff.apply_eq_apply_of_bounded hFbdd 0 1
  exact zero_ne_one (e.toEquiv.injective (Subtype.ext h01))

/-- Compactness separation: the sphere is not biholomorphic to the plane. -/
theorem not_nonempty_diffeomorph_sphere_complex :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ℂ := e.toHomeomorph.compactSpace
  exact not_compactSpace_iff.mpr inferInstance hcs

/-- Compactness separation: the sphere is not biholomorphic to the unit
disc. -/
theorem not_nonempty_diffeomorph_sphere_unitDisc :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ↥unitDiscOpens := e.toHomeomorph.compactSpace
  have hc : IsCompact (Metric.ball (0 : ℂ) 1) := isCompact_iff_compactSpace.mpr hcs
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.ball (0 : ℂ) 1 :=
    hc.isClosed.closure_eq
  rw [closure_ball (0 : ℂ) one_ne_zero] at hcl
  have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hcl] at h1
  simp [Metric.mem_ball, dist_eq_norm] at h1

/-! ## The abstract trichotomy -/

/-- **Planarity of simply connected Riemann surfaces**: every simply
connected one-dimensional complex manifold embeds biholomorphically onto a
domain of the Riemann sphere. -/
theorem exists_diffeomorph_opens_sphere_of_simplyConnected (M : Type*)
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    [T2Space M] [SimplyConnectedSpace M] [SecondCountableTopology M] :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  have : ConnectedSpace M := PathConnectedSpace.connectedSpace
  by_cases hcomp : CompactSpace M
  · refine exists_diffeomorph_opens_of_forall_not_hasGreenFunction fun p₀ hp₀ => ?_
    obtain ⟨x, hx, hbdd⟩ := hp₀
    exact not_bddAbove_image_greenFamily_of_compactSpace p₀ x hx hbdd
  · have : NoncompactSpace M := not_compactSpace_iff.mp hcomp
    by_cases hG : ∃ p₀ : M, HasGreenFunction p₀
    · obtain ⟨p₀, hp₀⟩ := hG
      exact exists_diffeomorph_opens_of_hasGreenFunction hp₀
    · push Not at hG
      exact exists_diffeomorph_opens_of_forall_not_hasGreenFunction hG

/-- **The uniformization trichotomy**: every simply connected Riemann surface
is biholomorphic to the unit disc, the plane, or the Riemann sphere. -/
theorem uniformization_trichotomy (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [T2Space M]
    [SimplyConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_sphere_of_simplyConnected M
  have hsc : SimplyConnectedSpace ↥U :=
    simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
  rcases sphere_domain_trichotomy U hsc with h | h | h
  · exact Or.inl (h.map fun f => e.trans f)
  · exact Or.inr (Or.inl (h.map fun f => e.trans f))
  · exact Or.inr (Or.inr (h.map fun f => e.trans f))

end RiemannDynamics
