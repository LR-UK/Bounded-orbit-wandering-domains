/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import RiemannDynamics.Uniformization.Perron.GreensFunction.Basic
import BoundedWanderingDomains.Surfaces.SubdomainCover
import BoundedWanderingDomains.Surfaces.LegacyDiscCoverBridge
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Topology of finitely punctured analytic surfaces -/

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- Removing finitely many points from a connected infinite analytic surface
leaves it connected. -/
theorem isConnected_compl_finset [ConnectedSpace M] [Infinite M] [T2Space M]
    (F : Finset M) : IsConnected ((↑F : Set M)ᶜ) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, Set.compl_empty]
      exact isConnected_univ
  | @insert p F hp ih =>
      have hFclosed : IsClosed (↑F : Set M) := F.finite_toSet.isClosed
      let O : Opens M := ⟨(↑F : Set M)ᶜ, hFclosed.isOpen_compl⟩
      letI : ConnectedSpace O := Subtype.connectedSpace ih
      have hpO : p ∈ O := by
        change p ∉ (↑F : Set M)
        exact fun h => hp (Finset.mem_coe.mp h)
      have hOinf : ((↑F : Set M)ᶜ).Infinite := F.finite_toSet.infinite_compl
      obtain ⟨a, ha, b, hb, hab⟩ := hOinf.nontrivial
      have hnt : ∃ u w : O, u ≠ w :=
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
      have hc := isConnected_compl_singleton_of_connected
        (M := O) hnt ⟨p, hpO⟩
      have himg := hc.image Subtype.val continuous_subtype_val.continuousOn
      have heq : Subtype.val '' ({(⟨p, hpO⟩ : O)}ᶜ : Set O) =
          (↑(insert p F) : Set M)ᶜ := by
        ext w
        constructor
        · rintro ⟨⟨x, hxO⟩, hxne, rfl⟩
          intro hw
          rw [Finset.coe_insert, Set.mem_insert_iff] at hw
          rcases hw with rfl | hwF
          · exact hxne (Set.mem_singleton_iff.mpr rfl)
          · exact hxO hwF
        · intro hw
          have hwp : w ≠ p := by
            intro h
            apply hw
            apply Finset.mem_coe.mpr
            rw [h]
            exact Finset.mem_insert_self p F
          have hwF : w ∉ (↑F : Set M) := fun h =>
            hw (Finset.mem_coe.mpr
              (Finset.mem_insert_of_mem (Finset.mem_coe.mp h)))
          refine ⟨⟨w, hwF⟩, ?_, rfl⟩
          intro h
          exact hwp (congrArg Subtype.val (Set.mem_singleton_iff.mp h))
      rwa [heq] at himg

/-- The complement of a nonempty finite set in a connected analytic surface
is noncompact. -/
theorem noncompact_compl_finset [ConnectedSpace M] [Infinite M]
    [T2Space M] {F : Finset M} (hF : F.Nonempty) :
    ¬ IsCompact ((↑F : Set M)ᶜ) := by
  intro hcompact
  have hopen : IsOpen ((↑F : Set M)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
  have hclopen : IsClopen ((↑F : Set M)ᶜ) := ⟨hcompact.isClosed, hopen⟩
  have hnonempty : ((↑F : Set M)ᶜ).Nonempty :=
    F.finite_toSet.infinite_compl.nonempty
  have huniv := hclopen.eq_univ hnonempty
  obtain ⟨p, hp⟩ := hF
  have hpcompl : p ∈ ((↑F : Set M)ᶜ) := huniv.symm ▸ Set.mem_univ p
  exact hpcompl (Finset.mem_coe.mpr hp)

/-- The open subtype obtained by deleting a nonempty finite set is a
noncompact connected surface. -/
theorem finitePuncture_instances [ConnectedSpace M] [Infinite M]
    [T2Space M] (F : Finset M) (hF : F.Nonempty) :
    ∃ O : Opens M, (O : Set M) = (↑F : Set M)ᶜ ∧
      Nonempty (ConnectedSpace O) ∧ Nonempty (NoncompactSpace O) := by
  let O : Opens M := ⟨(↑F : Set M)ᶜ, F.finite_toSet.isClosed.isOpen_compl⟩
  let hc : ConnectedSpace O := Subtype.connectedSpace (isConnected_compl_finset F)
  let hn : NoncompactSpace O :=
    not_compactSpace_iff.mp (by
      intro hco
      have hset : IsCompact (O : Set M) := isCompact_iff_compactSpace.mpr hco
      exact noncompact_compl_finset hF hset)
  exact ⟨O, rfl, ⟨hc⟩, ⟨hn⟩⟩

end RiemannDynamics

namespace AreaDeficit.Surfaces.DiscCover

open RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [Infinite M]

/-- A disc cover on an ambient open set restricts to any connected open set
of the original surface contained in it. -/
theorem nonempty_of_le_open (V U : TopologicalSpace.Opens M)
    (p : DiscCover V) (hUV : U ≤ V) [ConnectedSpace U] :
    Nonempty (DiscCover U) := by
  let O : TopologicalSpace.Opens V :=
    ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  let F : O → U := fun x => ⟨(x : V), x.property⟩
  let G : U → O := fun x =>
    ⟨⟨(x : M), hUV x.property⟩, x.property⟩
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ F) x :=
      ((contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).comp
        (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω))).contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  have hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω G := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ G) x := by
      rw [contMDiffAt_iff_target]
      have hbase : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
          (Subtype.val : U → M) x :=
        (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).contMDiffAt
      exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hbase.continuousAt,
        (contMDiffAt_iff_target.mp hbase).2⟩
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  let e : O ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ U :=
    { toFun := F
      invFun := G
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      contMDiff_toFun := hF
      contMDiff_invFun := hG }
  letI : ConnectedSpace O :=
    (e.toHomeomorph.connectedSpace_iff).mpr inferInstance
  obtain ⟨q⟩ := p.nonempty_subdomain O
  exact ⟨q.transDiffeomorph e⟩

/-- Finite punctures of a disc-covered surface inherit a concrete universal
cover by the disc. -/
theorem nonempty_finitePuncture (p : DiscCover M) (F : Finset M) :
    let O : Opens M :=
      ⟨(↑F : Set M)ᶜ, F.finite_toSet.isClosed.isOpen_compl⟩
    Nonempty (DiscCover O) := by
  let O : Opens M := ⟨(↑F : Set M)ᶜ,
    F.finite_toSet.isClosed.isOpen_compl⟩
  letI : ConnectedSpace O :=
    Subtype.connectedSpace (RiemannDynamics.isConnected_compl_finset F)
  exact p.nonempty_subdomain O

end AreaDeficit.Surfaces.DiscCover

#print axioms RiemannDynamics.isConnected_compl_finset
#print axioms RiemannDynamics.noncompact_compl_finset
#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_finitePuncture
#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_of_le_open
