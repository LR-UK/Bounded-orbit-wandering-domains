module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
public import RiemannDynamics.Uniformization.Trichotomy
public import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
public import RiemannDynamics.Hyperbolic.DiskModel.SchwarzPick
public import RiemannDynamics.Hyperbolic.DiskModel.MobiusDisk

@[expose] public section

/-!
# Hyperbolic surfaces and the hyperbolic metric

A connected analytic surface is *hyperbolic* when its universal path cover is
biholomorphic to the unit disc — by the uniformization trichotomy this is the
case exactly when the cover is neither the plane nor the sphere. Every
hyperbolic surface carries a complete metric compatible with its topology and
locally isometric to the Poincaré metric of the disc: the distance descends
from the disc along the covering as the infimum of the Poincaré distances
between lifts, the deck transformations acting by isometries by the
Schwarz–Pick theorem.

Main declarations:
* `IsHyperbolic` — the universal path cover at every basepoint is
  biholomorphic to the unit disc;
* `exists_pathCover_rebase_diffeomorph` — covers at two basepoints are
  biholomorphic, so hyperbolicity is basepoint independent;
* `isHyperbolic_of_nonempty_diffeomorph_disc` — one basepoint suffices;
* `isHyperbolic_of_hasGreenFunction` — a surface with a Green's function is
  hyperbolic;
* `exists_hyperbolicMetric_of_diffeomorph`, `exists_hyperbolicMetric` — the
  complete hyperbolic metric, locally isometric to `hyperbolicDistDisk`.
-/

open Metric Topology Filter TopologicalSpace
open scoped Manifold ContDiff unitInterval

namespace RiemannDynamics

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A connected analytic surface is **hyperbolic** when its universal path
cover is biholomorphic to the unit disc, for every choice of basepoint. -/
def IsHyperbolic : Prop :=
  ∀ x₀ : X, Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens)

variable {X}

/-- **Rebasing the universal path cover**: the covers at two basepoints of a
connected surface are biholomorphic, by prepending the class of a fixed path
between the basepoints. -/
theorem exists_pathCover_rebase_diffeomorph [ConnectedSpace X] (x₀ x₁ : X) :
    Nonempty (PathCover x₁ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ PathCover x₀) := by
  classical
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have c₀ : Path.Homotopic.Quotient x₀ x₁ :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x₁)
  -- Translation of path classes along a fixed connecting class is continuous:
  -- preimages of sheets are sheets of the translated point.
  have hcontGen : ∀ (a b : X) (c : Path.Homotopic.Quotient a b),
      Continuous fun qc : PathCover b =>
        (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a) := by
    intro a b c
    refine continuous_generateFrom_iff.mpr ?_
    rintro s ⟨pc, U, hUopen, hpcU, rfl⟩
    have hpre : (fun qc : PathCover b =>
        (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a)) ⁻¹'
        pathCoverSheet a pc U =
        pathCoverSheet b ⟨pc.pt, Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.symm c) pc.cls⟩ U := by
      ext qc
      constructor
      · rintro ⟨η, hη, hcls⟩
        have hcls' : Path.Homotopic.Quotient.trans c qc.cls = Path.Homotopic.Quotient.trans
            pc.cls (Path.Homotopic.Quotient.mk η) := hcls
        refine ⟨η, hη, ?_⟩
        have hgoal : qc.cls = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm c) pc.cls)
            (Path.Homotopic.Quotient.mk η) := by
          rw [Path.Homotopic.Quotient.trans_assoc, ← hcls',
            ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
            Path.Homotopic.Quotient.refl_trans]
        exact hgoal
      · rintro ⟨η, hη, hcls⟩
        have hcls' : qc.cls = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm c) pc.cls)
            (Path.Homotopic.Quotient.mk η) := hcls
        refine ⟨η, hη, ?_⟩
        have hgoal : Path.Homotopic.Quotient.trans c qc.cls = Path.Homotopic.Quotient.trans
            pc.cls (Path.Homotopic.Quotient.mk η) := by
          rw [hcls', ← Path.Homotopic.Quotient.trans_assoc,
            ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
            Path.Homotopic.Quotient.refl_trans]
        exact hgoal
    rw [hpre]
    exact isOpen_generateFrom_of_mem
      ⟨⟨pc.pt, Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm c) pc.cls⟩, U,
        hUopen, hpcU, rfl⟩
  -- Translation of path classes is analytic: through the charts commuting with the
  -- projections it reads as a transition map of the base.
  have hsmoothGen : ∀ (a b : X) (c : Path.Homotopic.Quotient a b),
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω fun qc : PathCover b =>
        (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a) := by
    intro a b c pc
    obtain ⟨e₁, he₁, f₁, hf₁, hpc₁, hprojpc₁, hall₁, hcomm₁⟩ :=
      exists_charts_pathCoverProj_comm b pc
    obtain ⟨e₂, he₂, f₂, hf₂, hpc₂, hproj₂, -, hcomm₂⟩ :=
      exists_charts_pathCoverProj_comm a
        (⟨pc.pt, Path.Homotopic.Quotient.trans c pc.cls⟩ : PathCover a)
    have hA : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e₁ pc := contMDiffAt_of_mem_maximalAtlas he₁ hpc₁
    have he₁pc : e₁ pc ∈ f₁.target := by
      rw [← hcomm₁ pc hpc₁]
      exact f₁.map_source hprojpc₁
    have hB : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f₁.symm (e₁ pc) :=
      contMDiffAt_symm_of_mem_maximalAtlas hf₁ he₁pc
    have hp2 : f₁.symm (e₁ pc) = pathCoverProj b pc := by
      rw [← hcomm₁ pc hpc₁]
      exact f₁.left_inv hprojpc₁
    have hC : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f₂ (f₁.symm (e₁ pc)) := by
      rw [hp2]
      exact contMDiffAt_of_mem_maximalAtlas hf₂ hproj₂
    have hf₂proj : f₂ (f₁.symm (e₁ pc)) ∈ e₂.target := by
      rw [hp2]
      have h2 : f₂ (pathCoverProj b pc) =
          e₂ (⟨pc.pt, Path.Homotopic.Quotient.trans c pc.cls⟩ : PathCover a) :=
        hcomm₂ _ hpc₂
      rw [h2]
      exact e₂.map_source hpc₂
    have hD : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e₂.symm (f₂ (f₁.symm (e₁ pc))) :=
      contMDiffAt_symm_of_mem_maximalAtlas he₂ hf₂proj
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun qc : PathCover b => e₂.symm (f₂ (f₁.symm (e₁ qc)))) pc :=
      hD.comp pc (hC.comp pc (hB.comp pc hA))
    have hSopen : IsOpen (e₁.source ∩ (fun qc : PathCover b =>
        (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a)) ⁻¹' e₂.source) :=
      e₁.open_source.inter (e₂.open_source.preimage (hcontGen a b c))
    refine hF.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hSopen.mem_nhds ⟨hpc₁, hpc₂⟩) ?_)
    intro qc hqc
    have h1 : f₁.symm (e₁ qc) = pathCoverProj b qc := by
      rw [← hcomm₁ qc hqc.1]
      exact f₁.left_inv (hall₁ qc hqc.1)
    have h2 : f₂ (pathCoverProj b qc) =
        e₂ (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a) :=
      hcomm₂ _ hqc.2
    change (⟨qc.pt, Path.Homotopic.Quotient.trans c qc.cls⟩ : PathCover a) =
      e₂.symm (f₂ (f₁.symm (e₁ qc)))
    rw [h1, h2]
    exact (e₂.left_inv hqc.2).symm
  refine ⟨{ toFun := fun pc : PathCover x₁ =>
              (⟨pc.pt, Path.Homotopic.Quotient.trans c₀ pc.cls⟩ : PathCover x₀)
            invFun := fun pc : PathCover x₀ =>
              (⟨pc.pt, Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.symm c₀) pc.cls⟩ : PathCover x₁)
            left_inv := ?_
            right_inv := ?_
            contMDiff_toFun := hsmoothGen x₀ x₁ c₀
            contMDiff_invFun := hsmoothGen x₁ x₀ (Path.Homotopic.Quotient.symm c₀) }⟩
  · rintro ⟨pt, cls⟩
    have hkey : Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm c₀)
        (Path.Homotopic.Quotient.trans c₀ cls) = cls := by
      rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
        Path.Homotopic.Quotient.refl_trans]
    exact congrArg (PathCover.mk pt) hkey
  · rintro ⟨pt, cls⟩
    have hkey : Path.Homotopic.Quotient.trans c₀
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm c₀) cls) = cls := by
      rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
        Path.Homotopic.Quotient.refl_trans]
    exact congrArg (PathCover.mk pt) hkey

/-- Hyperbolicity follows from a disc uniformization of the cover at a single
basepoint. -/
theorem isHyperbolic_of_nonempty_diffeomorph_disc [ConnectedSpace X] {x₀ : X}
    (h : Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens)) :
    IsHyperbolic X := by
  intro x₁
  obtain ⟨F⟩ := exists_pathCover_rebase_diffeomorph x₀ x₁
  obtain ⟨E⟩ := h
  exact ⟨F.trans E⟩

/-- **A surface carrying a Green's function is hyperbolic**: the cover is
simply connected and hyperbolic, hence a plane domain by the Green's-map
embedding, and the Riemann map takes it to the disc. -/
theorem isHyperbolic_of_hasGreenFunction [T2Space X] [ConnectedSpace X]
    [NoncompactSpace X] {p₀ : X} (hG : HasGreenFunction p₀) :
    IsHyperbolic X := by
  classical
  -- ## Instances on the universal path cover at the pole.
  have : T2Space (PathCover p₀) := t2space_pathCover p₀
  have : PathConnectedSpace (PathCover p₀) := pathConnectedSpace_pathCover p₀
  have : ConnectedSpace (PathCover p₀) := PathConnectedSpace.connectedSpace
  have : SimplyConnectedSpace (PathCover p₀) := simplyConnectedSpace_pathCover p₀
  have : NoncompactSpace (PathCover p₀) := noncompactSpace_pathCover p₀
  have : Nontrivial (PathCover p₀) := by
    rcases subsingleton_or_nontrivial (PathCover p₀) with hs | hn
    · have := hs
      have : Finite (PathCover p₀) := Finite.of_subsingleton
      exact absurd isCompact_univ (noncompact_univ (PathCover p₀))
    · exact hn
  -- ## The Green's function upstairs, at the canonical lift of the pole.
  have hGc : HasGreenFunction (pathCoverBase p₀) :=
    hasGreenFunction_pathCover p₀ hG (pc := pathCoverBase p₀) rfl
  -- ## The biholomorphism of the cover onto a plane domain, from the Green's map.
  obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hGc
  have hinj : Function.Injective φ := injective_green_map hGc hφ h0 habs
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
  by_cases hne : (U : Set ℂ) = Set.univ
  · -- ## The full-plane case contradicts hyperbolicity of the cover.
    exfalso
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    obtain ⟨etop⟩ := nonempty_diffeomorph_top ℂ
    obtain ⟨E⟩ : Nonempty (PathCover p₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := ⟨e.trans etop⟩
    obtain ⟨q, hq⟩ := exists_ne (pathCoverBase p₀)
    have hpos := greenEnvelope_pos hGc q hq
    have htrans := greenEnvelope_comp_diffeomorph E (pathCoverBase p₀) q
    have hnb : ¬ BddAbove ((fun v => v (E q)) '' greenFamily (E (pathCoverBase p₀))) :=
      fun hb => not_hasGreenFunction_complex (E (pathCoverBase p₀))
        ⟨E q, fun h => hq (E.toEquiv.injective h), hb⟩
    have hzero : greenEnvelope (E (pathCoverBase p₀)) (E q) = 0 :=
      Real.sSup_of_not_bddAbove hnb
    rw [htrans] at hzero
    linarith
  · -- ## The Riemann map takes the plane domain to the disc.
    have hscU : SimplyConnectedSpace ↥U :=
      simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
    obtain ⟨f, hf, hfinj, hfimg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hscU
    obtain ⟨e₂⟩ := nonempty_diffeomorph_of_injOn_differentiableOn U discOpens f hf
      hfinj hfimg
    exact isHyperbolic_of_nonempty_diffeomorph_disc ⟨e.trans e₂⟩

/-- **The hyperbolic metric, from a chosen uniformization**: a complete
metric on the surface compatible with its topology, locally isometric to the
Poincaré metric of the disc. The distance is the infimum of the disc
distances between lifts; deck transformations act by Poincaré isometries by
the Schwarz–Pick theorem, the fibers are closed and discrete, and the
Poincaré metric of the disc is proper, so the infimum is attained and the
quotient distance is a complete metric. -/
theorem exists_hyperbolicMetric_of_diffeomorph [T2Space X] [ConnectedSpace X]
    (x₀ : X) (E : PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) :
    ∃ m : MetricSpace X,
      m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X› ∧
      @CompleteSpace X m.toUniformSpace ∧
      ∀ x : X, ∃ U ∈ 𝓝 x, ∃ f : X → ℂ,
        (∀ y ∈ U, f y ∈ ball (0 : ℂ) 1) ∧
        ∀ y ∈ U, ∀ z ∈ U, m.dist y z = hyperbolicDistDisk (f y) (f z) := by
  classical
  have hcov := pathCoverProj_isCoveringMap x₀
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  -- The disc readings of cover points lie in the unit ball.
  have hEcm : ∀ pc : PathCover x₀, (↑(E pc) : ℂ) ∈ ball (0 : ℂ) 1 := fun pc => (E pc).2
  -- Lifts of base points through the covering projection.
  have hlift : ∀ y : X, ∃ pc : PathCover x₀, pathCoverProj x₀ pc = y := fun y =>
    ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩
  choose L hL using hlift
  have hFn : ∀ y : X, Nonempty {pc : PathCover x₀ // pathCoverProj x₀ pc = y} := fun y =>
    ⟨⟨L y, hL y⟩⟩
  -- Composition and identity laws for the deck action.
  have hdeck2 : ∀ (δ δ' : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      pathCoverDeck x₀ δ (pathCoverDeck x₀ δ' pc) = pathCoverDeck x₀ (δ.trans δ') pc :=
    fun δ δ' pc =>
      congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.trans_assoc δ δ' pc.cls).symm
  have hdeck_refl : ∀ pc : PathCover x₀,
      pathCoverDeck x₀ (Path.Homotopic.Quotient.refl x₀) pc = pc := by
    intro pc
    obtain ⟨pt, cls⟩ := pc
    exact congrArg (PathCover.mk pt) (Path.Homotopic.Quotient.refl_trans cls)
  have hdeck_symm : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      pathCoverDeck x₀ γ.symm (pathCoverDeck x₀ γ pc) = pc := by
    intro γ pc
    rw [hdeck2, Path.Homotopic.Quotient.symm_trans]
    exact hdeck_refl pc
  -- Freeness of the deck action: a deck transformation with a fixed point is the identity.
  have hfree : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      pathCoverDeck x₀ γ pc = pc → ∀ qc : PathCover x₀, pathCoverDeck x₀ γ qc = qc := by
    intro γ pc h qc
    obtain ⟨pt, cls⟩ := pc
    have h' : PathCover.mk pt (γ.trans cls) = PathCover.mk pt cls := h
    rw [PathCover.mk.injEq] at h'
    have hcl : γ.trans cls = cls := eq_of_heq h'.2
    have hγ : γ = Path.Homotopic.Quotient.refl x₀ := by
      have h3 := congrArg
        (fun c : Path.Homotopic.Quotient x₀ pt => Path.Homotopic.Quotient.trans c cls.symm) hcl
      try dsimp only [] at h3
      rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
        Path.Homotopic.Quotient.trans_refl] at h3
      exact h3
    rw [hγ]
    exact hdeck_refl qc
  -- Plane readings of analytic self-maps of the disc subtype are holomorphic on the ball.
  have hplane : ∀ g : ↥unitDiscOpens → ↥unitDiscOpens, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g →
      DifferentiableOn ℂ
        (fun w : ℂ => if hw : w ∈ ball (0 : ℂ) 1 then ((g ⟨w, hw⟩ : ↥unitDiscOpens) : ℂ) else 0)
        (ball (0 : ℂ) 1) := by
    intro g hg z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hne : Nonempty ↥unitDiscOpens := ⟨⟨z, hz⟩⟩
    have htgt : z ∈ (chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).target := by
      have h1 := (chartAt ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)).map_subtype_source
        (s := unitDiscOpens) hne (x := (⟨z, hz⟩ : ↥unitDiscOpens))
        (mem_chart_source ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ))
      have h2 : (chartAt ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)) ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)
          = z := rfl
      rw [h2] at h1
      rw [Opens.chartAt_eq]
      exact h1
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm) z :=
      contMDiffOn_chart_symm.contMDiffAt
        ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).open_target.mem_nhds htgt)
    have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm z) :=
      hg.contMDiffAt
    have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : ↥unitDiscOpens → ℂ)
        (g ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm z)) :=
      contMDiff_subtype_val.contMDiffAt
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        ((Subtype.val ∘ g) ∘ ⇑(chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm) z :=
      (h3.comp _ h2).comp z h1
    have hFd : DifferentiableAt ℂ
        ((Subtype.val ∘ g) ∘ ⇑(chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm) z :=
      (contMDiffAt_iff_contDiffAt.mp hF).analyticAt.differentiableAt
    refine hFd.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).open_target.mem_nhds htgt] with w hw
    have hval : (Subtype.val ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm w) : ℂ) = w := by
      have hwt : w ∈ ((chartAt ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)).subtypeRestr
          hne).target := by
        rw [← Opens.chartAt_eq]
        exact hw
      have h5 := (chartAt ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)).subtypeRestr_symm_apply
        (U := unitDiscOpens) hne hwt
      have h6 : (↑(chartAt ℂ ((⟨z, hz⟩ : ↥unitDiscOpens) : ℂ)).symm : ℂ → ℂ) w = w := rfl
      rw [Opens.chartAt_eq]
      exact h5.trans h6
    have hwball : w ∈ ball (0 : ℂ) 1 := by
      rw [← hval]
      exact ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm w).2
    change (if hw' : w ∈ ball (0 : ℂ) 1 then ((g ⟨w, hw'⟩ : ↥unitDiscOpens) : ℂ) else 0) =
      ((Subtype.val ∘ g) ∘ ⇑(chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm) w
    rw [dite_eq_left hwball]
    have h7 : (chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm w = ⟨w, hwball⟩ := Subtype.ext hval
    change ((g ⟨w, hwball⟩ : ↥unitDiscOpens) : ℂ) =
      ((g ((chartAt ℂ (⟨z, hz⟩ : ↥unitDiscOpens)).symm w) : ↥unitDiscOpens) : ℂ)
    rw [h7]
  -- Schwarz–Pick contraction for deck transformations read in the disc.
  have hcontract : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc qc : PathCover x₀),
      hyperbolicDistDisk (↑(E (pathCoverDeck x₀ γ pc))) (↑(E (pathCoverDeck x₀ γ qc))) ≤
        hyperbolicDistDisk (↑(E pc)) (↑(E qc)) := by
    intro γ pc qc
    obtain ⟨Dg, hDg⟩ := exists_pathCoverDeck_diffeomorph x₀ γ
    have hgc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω fun p : ↥unitDiscOpens => E (Dg (E.symm p)) :=
      E.contMDiff.comp (Dg.contMDiff.comp E.symm.contMDiff)
    have hAd := hplane _ hgc
    have hAm : Set.MapsTo (fun w : ℂ => if hw : w ∈ ball (0 : ℂ) 1
        then ((E (Dg (E.symm ⟨w, hw⟩)) : ↥unitDiscOpens) : ℂ)
        else 0) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
      intro w hw
      change (if hw' : w ∈ ball (0 : ℂ) 1
        then ((E (Dg (E.symm ⟨w, hw'⟩)) : ↥unitDiscOpens) : ℂ)
        else 0) ∈ ball (0 : ℂ) 1
      rw [dite_eq_left hw]
      exact hEcm (Dg (E.symm ⟨w, hw⟩))
    have hkey : ∀ rc : PathCover x₀,
        (if hw : (↑(E rc) : ℂ) ∈ ball (0 : ℂ) 1
          then ((E (Dg (E.symm ⟨(↑(E rc) : ℂ), hw⟩)) : ↥unitDiscOpens) : ℂ)
          else 0) = ↑(E (pathCoverDeck x₀ γ rc)) := by
      intro rc
      rw [dite_eq_left (hEcm rc)]
      have hmk : (⟨(↑(E rc) : ℂ), hEcm rc⟩ : ↥unitDiscOpens) = E rc := Subtype.ext rfl
      rw [hmk, E.symm_apply_apply, hDg rc]
    have hSP := schwarzPick hAd hAm (hEcm pc) (hEcm qc)
    rw [hkey pc, hkey qc] at hSP
    exact hSP
  -- Deck transformations are isometries of the Poincaré readings.
  have hiso : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc qc : PathCover x₀),
      hyperbolicDistDisk (↑(E (pathCoverDeck x₀ γ pc))) (↑(E (pathCoverDeck x₀ γ qc))) =
        hyperbolicDistDisk (↑(E pc)) (↑(E qc)) := by
    intro γ pc qc
    refine le_antisymm (hcontract γ pc qc) ?_
    have h := hcontract γ.symm (pathCoverDeck x₀ γ pc) (pathCoverDeck x₀ γ qc)
    rwa [hdeck_symm γ pc, hdeck_symm γ qc] at h
  -- Continuity of the Poincaré distance from a fixed center, on the ball.
  have hρcont : ∀ c : ℂ, c ∈ ball (0 : ℂ) 1 →
      ContinuousOn (fun z : ℂ => hyperbolicDistDisk c z) (ball (0 : ℂ) 1) := by
    intro c hc
    have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
    have hnum : Continuous fun z : ℂ => ‖c - z‖ := (continuous_const.sub continuous_id).norm
    have hden : Continuous fun z : ℂ => Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) :=
      Real.continuous_sqrt.comp
        (continuous_const.mul (continuous_const.sub (continuous_norm.pow 2)))
    have hdiv : ContinuousOn
        (fun z : ℂ => ‖c - z‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2))) (ball (0 : ℂ) 1) := by
      refine hnum.continuousOn.div hden.continuousOn ?_
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have h1 : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
      have h2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact (Real.sqrt_pos.mpr (mul_pos h1 h2)).ne'
    change ContinuousOn (fun z : ℂ =>
      2 * Real.arsinh (‖c - z‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)))) (ball (0 : ℂ) 1)
    exact continuousOn_const.mul (Real.continuous_arsinh.comp_continuousOn hdiv)
  -- Small hyperbolic distance forces small Euclidean distance inside the disc.
  have hclose : ∀ c w : ℂ, c ∈ ball (0 : ℂ) 1 → w ∈ ball (0 : ℂ) 1 → ∀ δ : ℝ,
      hyperbolicDistDisk c w < 2 * Real.arsinh δ → w ∈ ball c δ := by
    intro c w hc hw δ h
    have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hfc : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    have hfw : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hP_pos : 0 < (1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2) := mul_pos hfc hfw
    have hsq_pos : 0 < Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2)) := Real.sqrt_pos.mpr hP_pos
    have h2 : Real.arsinh (‖c - w‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2))) <
        Real.arsinh δ := by
      have hρ : hyperbolicDistDisk c w =
          2 * Real.arsinh (‖c - w‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2))) := rfl
      rw [hρ] at h
      linarith
    have h3 : ‖c - w‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2)) < δ :=
      Real.arsinh_lt_arsinh.mp h2
    have hsq_le : Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2)) ≤ 1 := by
      refine Real.sqrt_le_one.mpr ?_
      have ha1 : 1 - ‖c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c, sq_nonneg ‖c‖]
      have hb1 : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w, sq_nonneg ‖w‖]
      calc
        (1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2) ≤ 1 * (1 - ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_right ha1 hfw.le
        _ ≤ 1 := by simp
    have h4 : ‖c - w‖ ≤ ‖c - w‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
      rw [le_div_iff₀ hsq_pos]
      nlinarith [norm_nonneg (c - w)]
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  -- Pure real arithmetic: the sub-disc radius trapping hyperbolic sublevels.
  have harith : ∀ a S : ℝ, 0 ≤ a → a < 1 → 0 ≤ S →
      1 - (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) < 1 ∧
      ∀ u : ℝ, 0 ≤ u → u < 1 → (a < u → (u - a) ^ 2 ≤ 2 * S ^ 2 * (1 - u)) →
        u ≤ 1 - (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) := by
    intro a S ha0 ha1 hS0
    have hK1 : (1 : ℝ) ≤ 2 * S ^ 2 + 1 := by nlinarith [sq_nonneg S]
    have hden : (0 : ℝ) < 4 * (2 * S ^ 2 + 1) := by linarith
    have hfrac_pos : 0 < (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) := by
      have h1 : 0 < (1 - a) ^ 2 := pow_pos (by linarith) 2
      positivity
    have hfrac_le : (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) ≤ (1 - a) / 4 := by
      rw [div_le_div_iff₀ hden (by norm_num)]
      have h1 : (1 - a) ^ 2 ≤ 1 - a := by nlinarith
      nlinarith
    refine ⟨by linarith, ?_⟩
    intro u hu0 hu1 himp
    rcases le_or_gt u a with hua | hua
    · linarith
    · have h5 := himp hua
      by_contra hcon
      push Not at hcon
      have h7 : 1 - u < (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) := by linarith
      have h9 : 2 * S ^ 2 * (1 - u) ≤
          2 * S ^ 2 * ((1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1))) :=
        mul_le_mul_of_nonneg_left h7.le (by positivity)
      have h10 : 2 * S ^ 2 * ((1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1))) +
          (1 - a) ^ 2 / (4 * (2 * S ^ 2 + 1)) = (1 - a) ^ 2 / 4 := by
        field_simp
      have h8 : (u - a) ^ 2 < (1 - a) ^ 2 / 4 := by linarith
      have h12 : u - a < (1 - a) / 2 := by
        by_contra h12c
        push Not at h12c
        nlinarith [h8]
      linarith
  -- Closed hyperbolic balls are compact subsets of the disc.
  have hsub_cpt : ∀ c : ℂ, c ∈ ball (0 : ℂ) 1 → ∀ R : ℝ,
      IsCompact {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ hyperbolicDistDisk c z ≤ R} := by
    intro c hc R
    rcases le_or_gt 0 R with hR | hR
    · have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
      have hS0 : 0 ≤ Real.sinh (R / 2) := by
        rw [← Real.sinh_zero]
        exact Real.sinh_le_sinh.mpr (by linarith)
      obtain ⟨hrr1, hrrB⟩ := harith ‖c‖ (Real.sinh (R / 2)) (norm_nonneg c) hc1 hS0
      have hsubset : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ hyperbolicDistDisk c z ≤ R} ⊆
          closedBall (0 : ℂ)
            (1 - (1 - ‖c‖) ^ 2 / (4 * (2 * Real.sinh (R / 2) ^ 2 + 1))) := by
        rintro z ⟨hz, hρz⟩
        rw [mem_closedBall_zero_iff]
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        refine hrrB ‖z‖ (norm_nonneg z) hz1 ?_
        intro hzc
        have hfc : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
        have hfz : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have hP_pos : 0 < (1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2) := mul_pos hfc hfz
        have hsq_pos : 0 < Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) := Real.sqrt_pos.mpr hP_pos
        have hρz' : 2 * Real.arsinh (‖c - z‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2))) ≤ R :=
          hρz
        have ht : ‖c - z‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) ≤ Real.sinh (R / 2) := by
          have h3 : Real.arsinh (‖c - z‖ / Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2))) ≤
              Real.arsinh (Real.sinh (R / 2)) := by
            rw [Real.arsinh_sinh]
            linarith
          exact Real.arsinh_le_arsinh.mp h3
        have hnum : ‖c - z‖ ≤ Real.sinh (R / 2) * Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by
          rw [div_le_iff₀ hsq_pos] at ht
          linarith
        have hcz2 : ‖c - z‖ ^ 2 ≤ Real.sinh (R / 2) ^ 2 * ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by
          have hsqnn := Real.sqrt_nonneg ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2))
          have h4 : ‖c - z‖ ^ 2 ≤
              (Real.sinh (R / 2) * Real.sqrt ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2))) ^ 2 := by
            nlinarith [norm_nonneg (c - z)]
          rwa [mul_pow, Real.sq_sqrt hP_pos.le] at h4
        have hzc' : ‖z‖ - ‖c‖ ≤ ‖z - c‖ := norm_sub_norm_le z c
        have hrev : ‖z - c‖ = ‖c - z‖ := norm_sub_rev z c
        have h6 : (‖z‖ - ‖c‖) ^ 2 ≤ ‖c - z‖ ^ 2 := by
          nlinarith [norm_nonneg (c - z)]
        have hA : (1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2) ≤ 1 - ‖z‖ ^ 2 := by
          nlinarith [sq_nonneg ‖c‖, hfz.le]
        have hB : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by
          nlinarith [norm_nonneg z]
        calc (‖z‖ - ‖c‖) ^ 2 ≤ ‖c - z‖ ^ 2 := h6
          _ ≤ Real.sinh (R / 2) ^ 2 * ((1 - ‖c‖ ^ 2) * (1 - ‖z‖ ^ 2)) := hcz2
          _ ≤ Real.sinh (R / 2) ^ 2 * (2 * (1 - ‖z‖)) :=
              mul_le_mul_of_nonneg_left (hA.trans hB) (sq_nonneg _)
          _ = 2 * Real.sinh (R / 2) ^ 2 * (1 - ‖z‖) := by ring
      have hA_eq : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ hyperbolicDistDisk c z ≤ R} =
          closedBall (0 : ℂ) (1 - (1 - ‖c‖) ^ 2 / (4 * (2 * Real.sinh (R / 2) ^ 2 + 1))) ∩
            (fun z : ℂ => hyperbolicDistDisk c z) ⁻¹' Set.Iic R := by
        ext z
        constructor
        · rintro ⟨hz, hρz⟩
          exact ⟨hsubset ⟨hz, hρz⟩, hρz⟩
        · rintro ⟨hz, hρz⟩
          exact ⟨closedBall_subset_ball hrr1 hz, hρz⟩
      rw [hA_eq]
      have hclosed : IsClosed
          (closedBall (0 : ℂ) (1 - (1 - ‖c‖) ^ 2 / (4 * (2 * Real.sinh (R / 2) ^ 2 + 1))) ∩
            (fun z : ℂ => hyperbolicDistDisk c z) ⁻¹' Set.Iic R) :=
        ContinuousOn.preimage_isClosed_of_isClosed
          ((hρcont c hc).mono (closedBall_subset_ball hrr1)) isClosed_closedBall isClosed_Iic
      exact (isCompact_closedBall (0 : ℂ) _).of_isClosed_subset hclosed Set.inter_subset_left
    · have hempty : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ hyperbolicDistDisk c z ≤ R} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _
        have := hyperbolicDistDisk_nonneg c z
        intro hle
        linarith
      rw [hempty]
      exact isCompact_empty
  -- Compact subsets of the ball pull back to compact subsets of the disc subtype.
  have hpre_cpt : ∀ S : Set ℂ, S ⊆ ball (0 : ℂ) 1 → IsCompact S →
      IsCompact (Subtype.val ⁻¹' S : Set ↥unitDiscOpens) := by
    intro S hSsub hS
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set ↥unitDiscOpens) = S := by
      rw [Set.image_preimage_eq_inter_range, Subtype.range_val]
      exact Set.inter_eq_self_of_subset_left hSsub
    rw [himg]
    exact hS
  -- The candidate distance: infimum of Poincaré readings against lifts of the target.
  set dd : PathCover x₀ → X → ℝ := fun p y =>
    ⨅ q : {pc : PathCover x₀ // pathCoverProj x₀ pc = y},
      hyperbolicDistDisk (↑(E p)) (↑(E q.1)) with hdd
  have hbddb : ∀ (p : PathCover x₀) (y : X), BddBelow (Set.range
      fun q : {pc : PathCover x₀ // pathCoverProj x₀ pc = y} =>
        hyperbolicDistDisk (↑(E p)) (↑(E q.1))) := by
    intro p y
    refine ⟨0, ?_⟩
    rintro v ⟨q, rfl⟩
    exact hyperbolicDistDisk_nonneg _ _
  have hd_le : ∀ (p : PathCover x₀) (y : X) (q : PathCover x₀), pathCoverProj x₀ q = y →
      dd p y ≤ hyperbolicDistDisk (↑(E p)) (↑(E q)) := fun p y q hq =>
    ciInf_le (hbddb p y) ⟨q, hq⟩
  have hd_nonneg : ∀ (p : PathCover x₀) (y : X), 0 ≤ dd p y := fun p y =>
    Real.iInf_nonneg fun q => hyperbolicDistDisk_nonneg _ _
  -- Base-lift independence of the infimum, through the deck action.
  have haux : ∀ (p p' : PathCover x₀) (γ : Path.Homotopic.Quotient x₀ x₀),
      pathCoverDeck x₀ γ p = p' → ∀ y : X, dd p' y ≤ dd p y := by
    intro p p' γ hγ y
    have := hFn y
    refine le_ciInf fun r => ?_
    have hmem : pathCoverProj x₀ (pathCoverDeck x₀ γ r.1) = y := r.2
    have h1 : dd p' y ≤ hyperbolicDistDisk (↑(E p')) (↑(E (pathCoverDeck x₀ γ r.1))) :=
      hd_le p' y _ hmem
    have h2 : hyperbolicDistDisk (↑(E p')) (↑(E (pathCoverDeck x₀ γ r.1))) =
        hyperbolicDistDisk (↑(E p)) (↑(E r.1)) := by
      rw [← hγ]
      exact hiso γ p r.1
    rw [h2] at h1
    exact h1
  have hbase : ∀ p p' : PathCover x₀, pathCoverProj x₀ p = pathCoverProj x₀ p' →
      ∀ y : X, dd p y = dd p' y := by
    intro p p' h y
    obtain ⟨γ, hγ⟩ := pathCoverDeck_transitive x₀ p p' h
    have hγ' : pathCoverDeck x₀ γ.symm p' = p := by
      rw [← hγ]
      exact hdeck_symm γ p
    exact le_antisymm (haux p' p γ.symm hγ' y) (haux p p' γ hγ y)
  -- Sublevel sets of lifts are finite.
  have hfinlevel : ∀ (p : PathCover x₀) (y : X) (R : ℝ),
      {q : PathCover x₀ | pathCoverProj x₀ q = y ∧
        hyperbolicDistDisk (↑(E p)) (↑(E q)) ≤ R}.Finite := by
    intro p y R
    have h1 := hsub_cpt (↑(E p)) (hEcm p) R
    have h2 : IsCompact (Subtype.val ⁻¹' {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        hyperbolicDistDisk (↑(E p)) z ≤ R} : Set ↥unitDiscOpens) :=
      hpre_cpt _ (fun z hz => hz.1) h1
    have h3 : IsCompact (⇑E.symm '' (Subtype.val ⁻¹' {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        hyperbolicDistDisk (↑(E p)) z ≤ R})) := h2.image E.symm.continuous
    refine (finite_fiber_inter_compact x₀ h3 y).subset ?_
    rintro q ⟨hq1, hq2⟩
    refine ⟨Set.mem_singleton_iff.mpr hq1, ?_⟩
    exact ⟨E q, ⟨hEcm q, hq2⟩, E.symm_apply_apply q⟩
  -- The infimum is attained on a lift.
  have hattain : ∀ (p : PathCover x₀) (y : X), ∃ q : PathCover x₀,
      pathCoverProj x₀ q = y ∧ dd p y = hyperbolicDistDisk (↑(E p)) (↑(E q)) := by
    intro p y
    have := hFn y
    have hfin := hfinlevel p y (hyperbolicDistDisk (↑(E p)) (↑(E (L y))))
    have hne : {q : PathCover x₀ | pathCoverProj x₀ q = y ∧
        hyperbolicDistDisk (↑(E p)) (↑(E q)) ≤
          hyperbolicDistDisk (↑(E p)) (↑(E (L y)))}.Nonempty :=
      ⟨L y, hL y, le_refl _⟩
    obtain ⟨qs, hqs, hmin⟩ := Set.exists_min_image _
      (fun q : PathCover x₀ => hyperbolicDistDisk (↑(E p)) (↑(E q))) hfin hne
    refine ⟨qs, hqs.1, le_antisymm (hd_le p y qs hqs.1) (le_ciInf fun r => ?_)⟩
    by_cases hcase : hyperbolicDistDisk (↑(E p)) (↑(E r.1)) ≤
        hyperbolicDistDisk (↑(E p)) (↑(E (L y)))
    · exact hmin r.1 ⟨r.2, hcase⟩
    · exact hqs.2.trans (le_of_not_ge hcase)
  -- Metric axioms.
  have hd_self : ∀ x : X, dd (L x) x = 0 := by
    intro x
    have h1 : dd (L x) x ≤ 0 := by
      have h2 := hd_le (L x) x (L x) (hL x)
      rwa [hyperbolicDistDisk_self] at h2
    exact le_antisymm h1 (hd_nonneg (L x) x)
  have hd_comm : ∀ a b : X, dd (L a) b = dd (L b) a := by
    have hle : ∀ a b : X, dd (L b) a ≤ dd (L a) b := by
      intro a b
      obtain ⟨q, hq, hqe⟩ := hattain (L a) b
      have h1 : dd (L b) a = dd q a := hbase (L b) q (by rw [hL b, hq]) a
      have h2 : dd q a ≤ hyperbolicDistDisk (↑(E q)) (↑(E (L a))) := hd_le q a (L a) (hL a)
      rw [h1]
      calc dd q a ≤ hyperbolicDistDisk (↑(E q)) (↑(E (L a))) := h2
        _ = hyperbolicDistDisk (↑(E (L a))) (↑(E q)) := hyperbolicDistDisk_comm _ _
        _ = dd (L a) b := hqe.symm
    exact fun a b => le_antisymm (hle b a) (hle a b)
  have hd_triangle : ∀ a b c' : X, dd (L a) c' ≤ dd (L a) b + dd (L b) c' := by
    intro a b c'
    obtain ⟨q, hq, hqe⟩ := hattain (L a) b
    obtain ⟨r, hr, hre⟩ := hattain q c'
    have h1 : dd (L b) c' = dd q c' := hbase (L b) q (by rw [hL b, hq]) c'
    have h2 : dd (L a) c' ≤ hyperbolicDistDisk (↑(E (L a))) (↑(E r)) := hd_le (L a) c' r hr
    have h3 : hyperbolicDistDisk (↑(E (L a))) (↑(E r)) ≤
        hyperbolicDistDisk (↑(E (L a))) (↑(E q)) + hyperbolicDistDisk (↑(E q)) (↑(E r)) :=
      hyperbolicDistDisk_triangle (hEcm _) (hEcm _) (hEcm _)
    rw [hqe, h1, hre]
    linarith
  have hd_eq0 : ∀ a b : X, dd (L a) b = 0 → a = b := by
    intro a b h
    obtain ⟨q, hq, hqe⟩ := hattain (L a) b
    have h0 : hyperbolicDistDisk (↑(E (L a))) (↑(E q)) = 0 := by
      rw [← hqe]
      exact h
    have h1 := (hyperbolicDistDisk_eq_zero_iff (hEcm (L a)) (hEcm q)).mp h0
    have h2 : L a = q := E.toEquiv.injective (Subtype.ext h1)
    calc a = pathCoverProj x₀ (L a) := (hL a).symm
      _ = pathCoverProj x₀ q := by rw [h2]
      _ = b := hq
  -- The metric topology agrees with the surface topology.
  have Hchar : ∀ s : Set X, IsOpen s ↔
      ∀ x ∈ s, ∃ ε > 0, ∀ y : X, dd (L x) y < ε → y ∈ s := by
    intro s
    constructor
    · intro hs x hxs
      have hO : IsOpen (pathCoverProj x₀ ⁻¹' s) := hs.preimage hcov.continuous
      have hEopen : IsOpen (⇑E '' (pathCoverProj x₀ ⁻¹' s)) := E.toHomeomorph.isOpenMap _ hO
      have hΩopen : IsOpen (Subtype.val '' (⇑E '' (pathCoverProj x₀ ⁻¹' s))) :=
        unitDiscOpens.isOpen.isOpenMap_subtype_val _ hEopen
      have hcΩ : (↑(E (L x)) : ℂ) ∈ Subtype.val '' (⇑E '' (pathCoverProj x₀ ⁻¹' s)) := by
        refine ⟨E (L x), ⟨L x, ?_, rfl⟩, rfl⟩
        rw [Set.mem_preimage, hL x]
        exact hxs
      obtain ⟨εE, hεE, hball⟩ := Metric.isOpen_iff.mp hΩopen _ hcΩ
      refine ⟨2 * Real.arsinh εE, ?_, ?_⟩
      · have h1 : Real.arsinh 0 < Real.arsinh εE := Real.arsinh_lt_arsinh.mpr hεE
        rw [Real.arsinh_zero] at h1
        linarith
      · intro y hy
        have := hFn y
        obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt hy
        have hin : (↑(E q.1) : ℂ) ∈ ball (↑(E (L x)) : ℂ) εE :=
          hclose _ _ (hEcm (L x)) (hEcm q.1) εE hq
        have hΩ : (↑(E q.1) : ℂ) ∈ Subtype.val '' (⇑E '' (pathCoverProj x₀ ⁻¹' s)) := hball hin
        obtain ⟨w', hw', hveq⟩ := hΩ
        obtain ⟨o, hoO, rfl⟩ := hw'
        have hEo : E o = E q.1 := Subtype.ext hveq
        have ho : o = q.1 := E.toEquiv.injective hEo
        rw [ho] at hoO
        have hmem : pathCoverProj x₀ q.1 ∈ s := hoO
        rwa [q.2] at hmem
    · intro hs
      rw [isOpen_iff_forall_mem_open]
      intro x hxs
      obtain ⟨ε, hε, hball⟩ := hs x hxs
      obtain ⟨e₀, he₀s, he₀p, -⟩ := exists_pathCover_openPartialHomeomorph x₀ (L x)
      have hxe : x ∈ e₀.target := by
        have h1 := e₀.map_source he₀s
        rwa [he₀p (L x) he₀s, hL x] at h1
      have hgc : ContinuousOn
          (fun y : X => hyperbolicDistDisk (↑(E (L x))) (↑(E (e₀.symm y)))) e₀.target := by
        have h1 : ContinuousOn (fun y : X => (↑(E (e₀.symm y)) : ℂ)) e₀.target :=
          (continuous_subtype_val.comp E.continuous).comp_continuousOn e₀.continuousOn_symm
        exact (hρcont _ (hEcm (L x))).comp h1 fun y _ => hEcm (e₀.symm y)
      have hWopen : IsOpen (e₀.target ∩
          (fun y : X => hyperbolicDistDisk (↑(E (L x))) (↑(E (e₀.symm y)))) ⁻¹' Set.Iio ε) :=
        hgc.isOpen_inter_preimage e₀.open_target isOpen_Iio
      have hsymmx : e₀.symm x = L x := by
        have h1 := e₀.left_inv he₀s
        rwa [he₀p (L x) he₀s, hL x] at h1
      refine ⟨_, ?_, hWopen, ⟨hxe, ?_⟩⟩
      · intro y hy
        apply hball
        have hqy : pathCoverProj x₀ (e₀.symm y) = y := by
          have h1 := e₀.right_inv hy.1
          rwa [he₀p (e₀.symm y) (e₀.map_target hy.1)] at h1
        have h2 : dd (L x) y ≤ hyperbolicDistDisk (↑(E (L x))) (↑(E (e₀.symm y))) :=
          hd_le (L x) y (e₀.symm y) hqy
        have h3 : hyperbolicDistDisk (↑(E (L x))) (↑(E (e₀.symm y))) < ε := hy.2
        linarith
      · change hyperbolicDistDisk (↑(E (L x))) (↑(E (e₀.symm x))) < ε
        rw [hsymmx, hyperbolicDistDisk_self]
        exact hε
  -- Assemble the metric space.
  set mX : MetricSpace X := MetricSpace.ofDistTopology (fun a b => dd (L a) b) hd_self hd_comm
    hd_triangle Hchar hd_eq0 with hmX
  refine ⟨mX, rfl, ?_, ?_⟩
  · -- Completeness via properness: closed balls are continuous images of compacts.
    let := mX
    have : ProperSpace X := by
      constructor
      intro xc r
      have hcb : closedBall xc r = pathCoverProj x₀ ''
          (⇑E.symm '' (Subtype.val ⁻¹' {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
            hyperbolicDistDisk (↑(E (L xc))) z ≤ r})) := by
        ext y
        rw [mem_closedBall]
        have hdy : dist y xc = dd (L xc) y := by
          have h1 : dist y xc = dd (L y) xc := rfl
          rw [h1, hd_comm]
        rw [hdy]
        constructor
        · intro hle
          obtain ⟨q, hq, hqe⟩ := hattain (L xc) y
          refine ⟨q, ⟨E q, ⟨hEcm q, ?_⟩, E.symm_apply_apply q⟩, hq⟩
          rw [← hqe]
          exact hle
        · rintro ⟨q, ⟨w, hw, rfl⟩, rfl⟩
          have h2 := hd_le (L xc) (pathCoverProj x₀ (E.symm w)) (E.symm w) rfl
          have h3 : (↑(E (E.symm w)) : ℂ) = ↑w := by rw [E.apply_symm_apply]
          rw [h3] at h2
          have hw' : (↑w : ℂ) ∈ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
              hyperbolicDistDisk (↑(E (L xc))) z ≤ r} := hw
          exact h2.trans hw'.2
      rw [hcb]
      have h1 := hsub_cpt (↑(E (L xc))) (hEcm (L xc)) r
      have h2 : IsCompact (Subtype.val ⁻¹' {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
          hyperbolicDistDisk (↑(E (L xc))) z ≤ r} : Set ↥unitDiscOpens) :=
        hpre_cpt _ (fun z hz => hz.1) h1
      exact ((h2.image E.symm.continuous).image hcov.continuous)
    exact complete_of_proper
  · -- Local isometry with the Poincaré metric of the disc.
    intro x
    -- Separation of the fiber over x from the chosen lift.
    have hsep : ∃ sep : ℝ, 0 < sep ∧ ∀ q : PathCover x₀, pathCoverProj x₀ q = x → q ≠ L x →
        4 * sep ≤ hyperbolicDistDisk (↑(E (L x))) (↑(E q)) := by
      have hfin : ({q : PathCover x₀ | pathCoverProj x₀ q = x ∧
          hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1} \ {L x}).Finite :=
        (hfinlevel (L x) x 1).sdiff
      rcases Set.eq_empty_or_nonempty ({q : PathCover x₀ | pathCoverProj x₀ q = x ∧
          hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1} \ {L x}) with hemp | hne
      · refine ⟨1 / 8, by norm_num, ?_⟩
        intro q hq hqne
        by_contra hcon
        push Not at hcon
        have hq1 : hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1 := by linarith
        have hqmem : q ∈ ({q : PathCover x₀ | pathCoverProj x₀ q = x ∧
            hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1} \ {L x}) :=
          ⟨⟨hq, hq1⟩, fun h => hqne (Set.mem_singleton_iff.mp h)⟩
        rw [hemp] at hqmem
        exact hqmem
      · obtain ⟨qm, hqm, hmin⟩ := Set.exists_min_image _
          (fun q : PathCover x₀ => hyperbolicDistDisk (↑(E (L x))) (↑(E q))) hfin hne
        have hqm_ne : qm ≠ L x := fun h => hqm.2 (Set.mem_singleton_iff.mpr h)
        have hqm_pos : 0 < hyperbolicDistDisk (↑(E (L x))) (↑(E qm)) := by
          rcases (hyperbolicDistDisk_nonneg (↑(E (L x))) (↑(E qm))).lt_or_eq with h | h
          · exact h
          · exfalso
            have h1 := (hyperbolicDistDisk_eq_zero_iff (hEcm (L x)) (hEcm qm)).mp h.symm
            exact hqm_ne (E.toEquiv.injective (Subtype.ext h1)).symm
        refine ⟨min (hyperbolicDistDisk (↑(E (L x))) (↑(E qm)) / 4) (1 / 8), by positivity, ?_⟩
        intro q hq hqne
        by_cases hq1 : hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1
        · have hqmem : q ∈ ({q : PathCover x₀ | pathCoverProj x₀ q = x ∧
              hyperbolicDistDisk (↑(E (L x))) (↑(E q)) ≤ 1} \ {L x}) :=
            ⟨⟨hq, hq1⟩, fun h => hqne (Set.mem_singleton_iff.mp h)⟩
          have h2 := hmin q hqmem
          have h3 := min_le_left (hyperbolicDistDisk (↑(E (L x))) (↑(E qm)) / 4) (1 / 8)
          linarith
        · push Not at hq1
          have h3 := min_le_right (hyperbolicDistDisk (↑(E (L x))) (↑(E qm)) / 4) (1 / 8)
          linarith
    obtain ⟨sep, hsep_pos, hsep4⟩ := hsep
    -- Optimal lifts of every point, seen from the lift of x.
    choose Q hQp hQd using fun y : X => hattain (L x) y
    have hUopen : IsOpen {y : X | dd (L x) y < sep} := by
      rw [Hchar]
      intro a ha
      have ha' : dd (L x) a < sep := ha
      refine ⟨sep - dd (L x) a, by linarith, ?_⟩
      intro y hy
      change dd (L x) y < sep
      have h1 := hd_triangle x a y
      linarith
    have hxU : x ∈ {y : X | dd (L x) y < sep} := by
      change dd (L x) x < sep
      rw [hd_self x]
      exact hsep_pos
    refine ⟨{y : X | dd (L x) y < sep}, hUopen.mem_nhds hxU,
      fun y => (↑(E (Q y)) : ℂ), fun y _ => hEcm (Q y), ?_⟩
    intro y hy z hz
    have hy' : hyperbolicDistDisk (↑(E (L x))) (↑(E (Q y))) < sep := by
      rw [← hQd y]
      exact hy
    have hz' : hyperbolicDistDisk (↑(E (L x))) (↑(E (Q z))) < sep := by
      rw [← hQd z]
      exact hz
    change dd (L y) z = hyperbolicDistDisk (↑(E (Q y))) (↑(E (Q z)))
    have hbase_y : dd (L y) z = dd (Q y) z := hbase (L y) (Q y) (by rw [hL y, hQp y]) z
    rw [hbase_y]
    refine le_antisymm (hd_le (Q y) z (Q z) (hQp z)) ?_
    have := hFn z
    refine le_ciInf fun r => ?_
    obtain ⟨γ, hγ⟩ := pathCoverDeck_transitive x₀ (Q z) r.1 (by rw [hQp z, r.2])
    by_cases hfix : pathCoverDeck x₀ γ (L x) = L x
    · have hQzfix : pathCoverDeck x₀ γ (Q z) = Q z := hfree γ (L x) hfix (Q z)
      have hrQz : r.1 = Q z := by rw [← hγ, hQzfix]
      rw [hrQz]
    · have hfib : pathCoverProj x₀ (pathCoverDeck x₀ γ (L x)) = x :=
        (pathCoverProj_deck x₀ γ (L x)).trans (hL x)
      have h4s := hsep4 _ hfib hfix
      have hiso1 : hyperbolicDistDisk (↑(E (pathCoverDeck x₀ γ (Q z))))
            (↑(E (pathCoverDeck x₀ γ (L x)))) =
          hyperbolicDistDisk (↑(E (Q z))) (↑(E (L x))) := hiso γ (Q z) (L x)
      have htri1 : hyperbolicDistDisk (↑(E (L x))) (↑(E (pathCoverDeck x₀ γ (L x)))) ≤
          hyperbolicDistDisk (↑(E (L x))) (↑(E (pathCoverDeck x₀ γ (Q z)))) +
            hyperbolicDistDisk (↑(E (pathCoverDeck x₀ γ (Q z))))
              (↑(E (pathCoverDeck x₀ γ (L x)))) :=
        hyperbolicDistDisk_triangle (hEcm _) (hEcm _) (hEcm _)
      have hcomm1 : hyperbolicDistDisk (↑(E (Q z))) (↑(E (L x))) =
          hyperbolicDistDisk (↑(E (L x))) (↑(E (Q z))) := hyperbolicDistDisk_comm _ _
      have h3s : 3 * sep ≤
          hyperbolicDistDisk (↑(E (L x))) (↑(E (pathCoverDeck x₀ γ (Q z)))) := by
        rw [hiso1, hcomm1] at htri1
        linarith
      have htri2 : hyperbolicDistDisk (↑(E (L x))) (↑(E (pathCoverDeck x₀ γ (Q z)))) ≤
          hyperbolicDistDisk (↑(E (L x))) (↑(E (Q y))) +
            hyperbolicDistDisk (↑(E (Q y))) (↑(E (pathCoverDeck x₀ γ (Q z)))) :=
        hyperbolicDistDisk_triangle (hEcm _) (hEcm _) (hEcm _)
      have htri3 : hyperbolicDistDisk (↑(E (Q y))) (↑(E (Q z))) ≤
          hyperbolicDistDisk (↑(E (Q y))) (↑(E (L x))) +
            hyperbolicDistDisk (↑(E (L x))) (↑(E (Q z))) :=
        hyperbolicDistDisk_triangle (hEcm _) (hEcm _) (hEcm _)
      have hcomm2 : hyperbolicDistDisk (↑(E (Q y))) (↑(E (L x))) =
          hyperbolicDistDisk (↑(E (L x))) (↑(E (Q y))) := hyperbolicDistDisk_comm _ _
      rw [← hγ]
      linarith

/-- **Every hyperbolic surface carries a complete hyperbolic metric**: a
metric compatible with the topology, complete, and locally isometric to the
Poincaré metric of the disc. -/
theorem exists_hyperbolicMetric [T2Space X] [ConnectedSpace X]
    (hX : IsHyperbolic X) :
    ∃ m : MetricSpace X,
      m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X› ∧
      @CompleteSpace X m.toUniformSpace ∧
      ∀ x : X, ∃ U ∈ 𝓝 x, ∃ f : X → ℂ,
        (∀ y ∈ U, f y ∈ ball (0 : ℂ) 1) ∧
        ∀ y ∈ U, ∀ z ∈ U, m.dist y z = hyperbolicDistDisk (f y) (f z) := by
  have : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨E⟩ := hX (Classical.arbitrary X)
  exact exists_hyperbolicMetric_of_diffeomorph (Classical.arbitrary X) E

end RiemannDynamics
