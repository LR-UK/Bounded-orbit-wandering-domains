/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import RiemannDynamics.Uniformization.Perron.GreensFunction.Basic
import BoundedWanderingDomains.Surfaces.SubdomainCover

/-! # Topology of finitely punctured analytic surfaces -/

open Set Topology TopologicalSpace
open scoped Manifold

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
