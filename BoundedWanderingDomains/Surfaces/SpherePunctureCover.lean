module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LegacyDiscCoverBridge
public import BoundedWanderingDomains.Surfaces.AnalyticSurface
public import BoundedWanderingDomains.Surfaces.HolomorphicLifting
public import BoundedWanderingDomains.Surfaces.FinitePunctureTopology
public import FunctionTheory.Conformal.LittlePicardBloch
public import RiemannDynamics.Uniformization.HolomorphicEquiv

@[expose] public section

/-! # A concrete disc cover of the thrice-punctured sphere -/

open Set Function Topology TopologicalSpace OnePoint
open scoped Manifold ContDiff

namespace AreaDeficit.Surfaces

/-- A holomorphic map from the plane to the sphere which omits three distinct
values is constant.  Passing to the finite chart at one omitted value reduces
this to the two-omitted-values form of Little Picard. -/
theorem sphere_map_eq_const_of_three_omitted
    (H : ℂ → ℂ̂) (hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H)
    {a b c : ℂ̂} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ z, H z ≠ a) (hb : ∀ z, H z ≠ b) (hc : ∀ z, H z ≠ c) :
    ∃ d, H = fun _ => d := by
  obtain ⟨g, hga, hgb, hgc⟩ :=
    RiemannDynamics.exists_gl_smul_eq_zero_one_infty hab hac hbc
  obtain ⟨eg, heg⟩ := RiemannDynamics.exists_gl_smul_diffeomorph g
  let K : ℂ → ℂ̂ := eg ∘ H
  have hK : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) K :=
    (eg.mdifferentiable (by simp)).comp hH
  have hega : eg a = ((0 : ℂ) : ℂ̂) := by rw [heg]; exact hga
  have hegb : eg b = ((1 : ℂ) : ℂ̂) := by rw [heg]; exact hgb
  have hegc : eg c = (∞ : ℂ̂) := by rw [heg]; exact hgc
  have hK0 : ∀ z, K z ≠ ((0 : ℂ) : ℂ̂) := fun z hz =>
    ha z (eg.injective (hz.trans hega.symm))
  have hK1 : ∀ z, K z ≠ ((1 : ℂ) : ℂ̂) := fun z hz =>
    hb z (eg.injective (hz.trans hegb.symm))
  have hKinf : ∀ z, K z ≠ (∞ : ℂ̂) := fun z hz =>
    hc z (eg.injective (hz.trans hegc.symm))
  let U : Opens ℂ̂ := ⟨({(∞ : ℂ̂)} : Set ℂ̂)ᶜ, isOpen_compl_singleton⟩
  let HU : ℂ → U := fun z => ⟨K z, by simpa [U] using hKinf z⟩
  have hHU : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) HU := by
    apply (mdifferentiable_subtypeVal_comp_iff U HU).mp
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) K
    exact hK
  obtain ⟨V, -, ⟨e⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_planar U (by simp [U])
  let F : ℂ → ℂ := Subtype.val ∘ e ∘ HU
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : V → ℂ) :=
    (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).mdifferentiable (by simp)
  have hFmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    hval.comp ((e.mdifferentiable (by simp)).comp hHU)
  have hFd : Differentiable ℂ F := mdifferentiable_iff_differentiable.mp hFmd
  let A : U := ⟨((0 : ℂ) : ℂ̂), by simp [U]⟩
  let B : U := ⟨((1 : ℂ) : ℂ̂), by simp [U]⟩
  have hAB : (e A : ℂ) ≠ (e B : ℂ) := by
    intro h
    have := congrArg Subtype.val (e.injective (Subtype.ext h))
    exact zero_ne_one (OnePoint.coe_injective this)
  have hFA : ∀ z, F z ≠ (e A : ℂ) := by
    intro z hz
    have heq : HU z = A := e.injective (Subtype.ext hz)
    exact hK0 z (congrArg Subtype.val heq)
  have hFB : ∀ z, F z ≠ (e B : ℂ) := by
    intro z hz
    have heq : HU z = B := e.injective (Subtype.ext hz)
    exact hK1 z (congrArg Subtype.val heq)
  obtain ⟨d, hd⟩ := FunctionTheory.exists_eq_const_of_two_omitted_values
    hFd hAB (fun z hz => hFA z hz) (fun z hz => hFB z hz)
  refine ⟨H 0, funext fun z => ?_⟩
  have heq : e (HU z) = e (HU 0) := by
    apply Subtype.ext
    exact congrFun hd z |>.trans (congrFun hd 0).symm
  exact eg.injective (congrArg Subtype.val (e.injective heq))

/-- The normalized thrice-punctured sphere. -/
def normalizedThricePuncturedSphere : Opens ℂ̂ :=
  ⟨({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ,
    (((Set.finite_singleton (((1 : ℂ) : ℂ̂))).insert
      (((0 : ℂ) : ℂ̂))).insert (∞ : ℂ̂)).isClosed.isOpen_compl⟩

/-- The normalized thrice-punctured sphere has a concrete holomorphic
universal covering by the unit disc. -/
theorem DiscCover.nonempty_normalizedThricePuncturedSphere :
    Nonempty (DiscCover normalizedThricePuncturedSphere) := by
  let U : Opens ℂ̂ := normalizedThricePuncturedSphere
  have hinf : (∞ : ℂ̂) ∉ (U : Set ℂ̂) := by
    simp [U, normalizedThricePuncturedSphere]
  obtain ⟨V, hVimg, ⟨e⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_planar U hinf
  let P : Finset ℂ := {0, 1}
  let W : Opens ℂ :=
    ⟨((↑P : Set ℂ)ᶜ), P.finite_toSet.isClosed.isOpen_compl⟩
  have hPcard : 2 ≤ P.card := by simp [P]
  have hVW : V = W := by
    apply Opens.ext
    ext z
    have hzV : z ∈ (V : Set ℂ) ↔ ((z : ℂ̂) ∈ (U : Set ℂ̂)) := by
      constructor
      · intro hz
        rw [← hVimg]
        exact ⟨z, hz, rfl⟩
      · intro hz
        change (z : ℂ̂) ∈ (U : Set ℂ̂) at hz
        rw [← hVimg] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        have : w = z := OnePoint.coe_injective hwz
        simpa [this] using hw
    change z ∈ (V : Set ℂ) ↔ z ∈ (W : Set ℂ)
    rw [hzV]
    simp [U, W, P, normalizedThricePuncturedSphere]
  subst V
  obtain ⟨p⟩ := DiscCover.nonempty_finitelyPuncturedPlane P hPcard
  exact ⟨p.transDiffeomorph e.symm⟩

/-- Deleting any three distinct points from the Riemann sphere produces a
surface with a holomorphic universal disc covering. -/
theorem DiscCover.nonempty_sphere_compl_three {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let U : Opens ℂ̂ :=
      ⟨({a, b, c} : Set ℂ̂)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  let U : Opens ℂ̂ :=
    ⟨({a, b, c} : Set ℂ̂)ᶜ,
      (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
  obtain ⟨g, hga, hgb, hgc⟩ :=
    RiemannDynamics.exists_gl_smul_eq_zero_one_infty hab hac hbc
  obtain ⟨eg, heg⟩ := RiemannDynamics.exists_gl_smul_diffeomorph g
  obtain ⟨V, hVimg, ⟨e⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_image eg U
  have hV : V = normalizedThricePuncturedSphere := by
    apply Opens.ext
    rw [hVimg]
    change (eg.toHomeomorph : ℂ̂ → ℂ̂) '' ({a, b, c} : Set ℂ̂)ᶜ =
      ({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ
    rw [eg.toHomeomorph.image_compl]
    congr 1
    have hegh : (eg.toHomeomorph : ℂ̂ → ℂ̂) = (g • ·) := heg
    rw [hegh]
    ext z
    simp [hga, hgb, hgc, or_comm, or_left_comm]
  subst V
  obtain ⟨p⟩ := DiscCover.nonempty_normalizedThricePuncturedSphere
  exact ⟨p.transDiffeomorph e.symm⟩

/-- Three punctures hyperbolize every surface biholomorphic to the sphere. -/
theorem DiscCover.nonempty_compl_three_of_diffeomorph_sphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [SecondCountableTopology X]
    (e : X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let U : Opens X :=
      ⟨({a, b, c} : Set X)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  let U : Opens X :=
    ⟨({a, b, c} : Set X)ᶜ,
      (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
  let T : Opens ℂ̂ :=
    ⟨({e a, e b, e c} : Set ℂ̂)ᶜ,
      (((Set.finite_singleton (e c)).insert (e b)).insert (e a)).isClosed.isOpen_compl⟩
  obtain ⟨V, hVimg, ⟨r⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_image e U
  have hVT : V = T := by
    apply Opens.ext
    rw [hVimg]
    change (e.toHomeomorph : X → ℂ̂) '' ({a, b, c} : Set X)ᶜ =
      ({e a, e b, e c} : Set ℂ̂)ᶜ
    rw [e.toHomeomorph.image_compl]
    congr 1
    ext z
    simp
  subst V
  obtain ⟨p⟩ := DiscCover.nonempty_sphere_compl_three
    (e.injective.ne hab) (e.injective.ne hac) (e.injective.ne hbc)
  exact ⟨p.transDiffeomorph r.symm⟩

/-- If the universal path cover of a compact surface is the sphere, deleting
three distinct points gives a supplied disc cover.  The plane alternative for
the punctured surface would lift to a sphere-valued entire map omitting three
values, and is therefore constant by Little Picard. -/
theorem DiscCover.nonempty_compl_three_of_pathCover_sphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [ConnectedSpace X] [T2Space X]
    [SecondCountableTopology X] [Infinite X]
    (x₀ : X) (e : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂)
    {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let U : Opens X :=
      ⟨({a, b, c} : Set X)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  classical
  let P : Finset X := {a, b, c}
  let U : Opens X :=
    ⟨({a, b, c} : Set X)ᶜ,
      (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
  let : ConnectedSpace U := Subtype.connectedSpace (by
    simpa [U, P] using RiemannDynamics.isConnected_compl_finset P)
  let : Infinite U := Set.Infinite.to_subtype
    (((Set.finite_singleton c).insert b).insert a).infinite_compl
  let π : ℂ̂ → X := RiemannDynamics.pathCoverProj x₀ ∘ e.symm
  have hproj := RiemannDynamics.contMDiff_pathCoverProj x₀
  have hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π :=
    (hproj.comp e.symm.contMDiff).mdifferentiable (by simp)
  have hcov : IsCoveringMap π :=
    (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph
      e.symm.toHomeomorph
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have hprojSurj : Surjective (RiemannDynamics.pathCoverProj x₀) := by
    intro y
    exact ⟨⟨y, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
  have hsurj : Surjective π := hprojSurj.comp e.symm.surjective
  let y₀ : U := Classical.choice (inferInstance : Nonempty U)
  let : T2Space (RiemannDynamics.PathCover y₀) :=
    RiemannDynamics.t2space_pathCover y₀
  let : SimplyConnectedSpace (RiemannDynamics.PathCover y₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover y₀
  let : SecondCountableTopology (RiemannDynamics.PathCover y₀) :=
    RiemannDynamics.secondCountableTopology_pathCover y₀
  have hmodels := RiemannDynamics.uniformization_trichotomy
    (RiemannDynamics.PathCover y₀)
  have hprojU := RiemannDynamics.contMDiff_pathCoverProj y₀
  have hprojUSurj : Surjective (RiemannDynamics.pathCoverProj y₀) := by
    let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
    let : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
    intro y
    exact ⟨⟨y, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath y₀ y)⟩, rfl⟩
  rcases hmodels with hdisc | hplane | hsphere
  · obtain ⟨d⟩ := hdisc
    refine ⟨{ projection := RiemannDynamics.pathCoverProj y₀ ∘ d.symm
              holomorphic := ?_
              covering := ?_
              surjective := ?_ }⟩
    · exact (hprojU.mdifferentiable (by simp)).comp
        (d.symm.mdifferentiable (by simp))
    · exact (RiemannDynamics.pathCoverProj_isCoveringMap y₀).comp_homeomorph
        d.symm.toHomeomorph
    · exact hprojUSurj.comp d.symm.surjective
  · obtain ⟨d⟩ := hplane
    let F : ℂ → U := RiemannDynamics.pathCoverProj y₀ ∘ d.symm
    let G : ℂ → X := Subtype.val ∘ F
    have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
      (hprojU.comp d.symm.contMDiff).mdifferentiable (by simp)
    have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U → X) :=
      (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).mdifferentiable (by simp)
    have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := hval.comp hF
    obtain ⟨w, hw⟩ := hsurj (G 0)
    obtain ⟨H, -, hfac, hH⟩ := exists_holomorphic_lift hπ hcov hG 0 w hw
    obtain ⟨A, hA⟩ := hsurj a
    obtain ⟨B, hB⟩ := hsurj b
    obtain ⟨C, hC⟩ := hsurj c
    have hAB : A ≠ B := fun h => hab (hA.symm.trans (h ▸ hB))
    have hAC : A ≠ C := fun h => hac (hA.symm.trans (h ▸ hC))
    have hBC : B ≠ C := fun h => hbc (hB.symm.trans (h ▸ hC))
    have hHA : ∀ z, H z ≠ A := by
      intro z hz
      have hGa : G z = a := by
        have h := congrFun hfac z
        simpa [hz, hA] using h.symm
      apply (F z).property
      change G z ∈ ({a, b, c} : Set X)
      rw [hGa]
      simp
    have hHB : ∀ z, H z ≠ B := by
      intro z hz
      have hGb : G z = b := by
        have h := congrFun hfac z
        simpa [hz, hB] using h.symm
      apply (F z).property
      change G z ∈ ({a, b, c} : Set X)
      rw [hGb]
      simp
    have hHC : ∀ z, H z ≠ C := by
      intro z hz
      have hGc : G z = c := by
        have h := congrFun hfac z
        simpa [hz, hC] using h.symm
      apply (F z).property
      change G z ∈ ({a, b, c} : Set X)
      rw [hGc]
      simp
    obtain ⟨q, hq⟩ := sphere_map_eq_const_of_three_omitted
      H hH hAB hAC hBC hHA hHB hHC
    have hGc : G = fun _ => π q := by
      funext z
      have hz := congrFun hfac z
      simpa [hq] using hz.symm
    have hFc : F = fun _ => F 0 := by
      funext z
      apply Subtype.ext
      exact (congrFun hGc z).trans (congrFun hGc 0).symm
    have hFsurj : Surjective F := hprojUSurj.comp d.symm.surjective
    obtain ⟨y, hy⟩ := exists_ne (F 0)
    obtain ⟨z, rfl⟩ := hFsurj y
    exact (hy (congrFun hFc z)).elim
  · obtain ⟨d⟩ := hsphere
    let : CompactSpace (RiemannDynamics.PathCover y₀) :=
      d.toHomeomorph.symm.compactSpace
    let : CompactSpace U := hprojUSurj.compactSpace hprojU.continuous
    have hUc : IsCompact (U : Set X) := isCompact_iff_compactSpace.mpr inferInstance
    have hUuniv : (U : Set X) = Set.univ :=
      (show IsClopen (U : Set X) from ⟨hUc.isClosed, U.isOpen⟩).eq_univ
        ⟨y₀, y₀.property⟩
    have haU : a ∈ (U : Set X) := by rw [hUuniv]; trivial
    simp [U] at haU

end AreaDeficit.Surfaces
