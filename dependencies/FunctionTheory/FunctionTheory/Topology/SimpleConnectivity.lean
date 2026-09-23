import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Simple connectivity detected on compact connected subsets

An open connected plane domain is simply connected if every compact connected
subset lies in a simply connected subdomain. Each loop has compact connected
image, and its contraction in that subdomain maps back to the ambient domain.
-/

open Set

namespace FunctionTheory

theorem isSimplyConnected_of_compact_connected_subsets {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hlocal : ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ U →
      ∃ V : Set ℂ, IsSimplyConnected V ∧ K ⊆ V ∧ V ⊆ U) :
    IsSimplyConnected U := by
  have hpc : PathConnectedSpace U :=
    isPathConnected_iff_pathConnectedSpace.mp (hUo.isConnected_iff_isPathConnected.mp hUc)
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨hpc, ?_⟩
  intro x γ
  let p : Path (x : ℂ) (x : ℂ) := γ.map continuous_subtype_val
  have hKc : IsCompact (range p) := isCompact_range p.continuous
  have hKn : IsConnected (range p) := isConnected_range p.continuous
  have hKU : range p ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact (γ t).property
  obtain ⟨V, hV, hKV, hVU⟩ := hlocal (range p) hKc hKn hKU
  have hxV : (x : ℂ) ∈ V := hKV ⟨0, p.source⟩
  let xv : V := ⟨x, hxV⟩
  let q : Path xv xv :=
    { toFun := fun t => ⟨p t, hKV (mem_range_self t)⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  have : SimplyConnectedSpace V := hV
  have hq : Path.Homotopic q (Path.refl xv) :=
    SimplyConnectedSpace.paths_homotopic q (Path.refl xv)
  let ι : C(V, U) := ⟨fun z => ⟨z, hVU z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  exact hq.map ι

end FunctionTheory
