/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactificationCutoff
import BoundedWanderingDomains.Surfaces.ComponentDomains
import BoundedWanderingDomains.Surfaces.BoundaryEscape

/-! # End charts through compactification and finite-puncture restrictions -/

open Set Function Filter Metric TopologicalSpace
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

namespace FinitePunctureDiscs

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- A punctured coordinate disc from a pairwise-disjoint ambient family
survives restriction first past the compactification anchors, then past the
old finite stage, and finally past the newly inserted point. -/
theorem puncturedBall_subset_three_restricted_targets
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (E : Finset X) (hEF : E ⊆ F)
    (O : Opens X) (hO : ∀ x : X, x ∈ O ↔ x ∉ E)
    (hON : Nonempty O) (P : Finset O)
    (hPF : ∀ x ∈ P, (x : X) ∈ F)
    (hUN : Nonempty (finitePunctureDomain P))
    (a : finitePunctureDomain P) (haF : ((a : O) : X) ∈ F)
    (hWN : Nonempty (finitePunctureDomain ({a} : Finset _))) :
    ball (chartAt ℂ (D.disc i).center (D.disc i).center)
          (D.disc i).radius \
        {chartAt ℂ (D.disc i).center (D.disc i).center} ⊆
      ((((chartAt ℂ (D.disc i).center).subtypeRestr hON).subtypeRestr
        hUN).subtypeRestr hWN).target := by
  intro z hz
  let c := chartAt ℂ (D.disc i).center
  let d := c.subtypeRestr hON
  let e := d.subtypeRestr hUN
  let yX := c.symm z
  have hzt : z ∈ c.target := by
    apply (D.disc i).closedBall_subset
    exact mem_closedBall.mpr (le_of_lt hz.1)
  have hycarrier : yX ∈ (D.disc i).closedCarrier := by
    refine ⟨z, mem_closedBall.mpr (le_of_lt hz.1), rfl⟩
  have hyF : yX ∉ F := by
    intro hy
    let j : ↑F := ⟨yX, hy⟩
    by_cases hji : j = i
    · have hycenter : yX = (D.disc i).center := by
        calc
          yX = (j : X) := rfl
          _ = (i : X) := congrArg Subtype.val hji
          _ = (D.disc i).center := (D.center i).symm
      apply hz.2
      calc
        z = c yX := (c.right_inv hzt).symm
        _ = c (D.disc i).center := congrArg c hycenter
    · have hyj : yX ∈ (D.disc j).closedCarrier := by
        rw [show yX = (j : X) from rfl, ← D.center j]
        refine ⟨chartAt ℂ (D.disc j).center (D.disc j).center, ?_, ?_⟩
        · simpa only [mem_closedBall, dist_self] using (D.disc j).radius_pos.le
        · exact (chartAt ℂ (D.disc j).center).left_inv
            (mem_chart_source ℂ (D.disc j).center)
      exact Set.disjoint_left.mp
        (D.pairwise (mem_univ j) (mem_univ i) hji) hyj hycarrier
  have hyE : yX ∉ E := fun hy => hyF (hEF hy)
  let yO : O := ⟨yX, (hO yX).mpr hyE⟩
  have hyP : yO ∉ P := fun hy => hyF (hPF yO hy)
  let yU : finitePunctureDomain P := ⟨yO, hyP⟩
  have hya : yU ≠ a := by
    intro h
    apply hyF
    have heq : yX = ((a : O) : X) :=
      congrArg (fun w : finitePunctureDomain P => ((w : O) : X)) h
    rw [heq]
    exact haF
  let yW : finitePunctureDomain ({a} : Finset _) := by
    refine ⟨yU, ?_⟩
    simpa only [mem_finitePunctureDomain, Finset.mem_singleton] using hya
  have hycs : yX ∈ c.source := c.map_target hzt
  have hyds : yO ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
      using hycs
  have hyes : yU ∈ e.source := by
    simpa only [e, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
      using hyds
  have hmap := e.map_subtype_source hWN (x := yW) hyes
  have heq : e yU = z := by
    change c yX = z
    exact c.right_inv hzt
  exact heq ▸ hmap

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- The inverse of a successively restricted compactification chart escapes
every compact subset of an intermediate open subtype when its centre is not
in that subtype. -/
theorem subtypeRestr_symm_tendsto_cocompact
    (O : Opens X) (hON : Nonempty O) (U : Opens O) (hUN : Nonempty U)
    (W : Opens U) (hWN : Nonempty W) (b : X)
    (hnot : ∀ y : U, ((y : O) : X) ≠ b)
    {R : ℝ} (hR : 0 < R)
    (hball : ball (chartAt ℂ b b) R \ {chartAt ℂ b b} ⊆
      ((((chartAt ℂ b).subtypeRestr hON).subtypeRestr hUN).subtypeRestr
        hWN).target) :
    let e := (((chartAt ℂ b).subtypeRestr hON).subtypeRestr hUN).subtypeRestr
      hWN
    let x : ℂ → W := fun z => e.symm z
    Tendsto (fun z => (x z : U)) (𝓝[≠] (chartAt ℂ b b))
        (cocompact U) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ b b),
        z ∈ e.target ∧ x z = e.symm z := by
  let c := chartAt ℂ b
  let d := c.subtypeRestr hON
  let f := d.subtypeRestr hUN
  let e := f.subtypeRestr hWN
  let x : ℂ → W := fun z => e.symm z
  have hevent : ∀ᶠ z in 𝓝[≠] (chartAt ℂ b b), z ∈ e.target := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (chartAt ℂ b b) hR)]
        with z hzne hzball
    exact hball ⟨hzball, by
      simpa only [mem_compl_iff, mem_singleton_iff] using hzne⟩
  have hambient : Tendsto (fun z => (((x z : W) : U) : O) : ℂ → X)
      (𝓝[≠] (chartAt ℂ b b)) (𝓝 b) := by
    have hchart : Tendsto (chartAt ℂ b).symm
        (𝓝 (chartAt ℂ b b)) (𝓝 b) := by
      have hbsource : b ∈ (chartAt ℂ b).source := mem_chart_source ℂ b
      have hbtarget := (chartAt ℂ b).map_source hbsource
      have hc := (chartAt ℂ b).symm.continuousAt hbtarget
      change Tendsto (chartAt ℂ b).symm
        (𝓝 (chartAt ℂ b b)) (𝓝 ((chartAt ℂ b).symm
          (chartAt ℂ b b))) at hc
      simpa only [(chartAt ℂ b).left_inv hbsource] using hc
    apply (hchart.mono_left inf_le_left).congr'
    filter_upwards [hevent] with z hz
    have hW := f.subtypeRestr_symm_apply hWN hz
    have hzf := f.subtypeRestr_target_subset hWN hz
    have hU := d.subtypeRestr_symm_apply hUN hzf
    have hzd := d.subtypeRestr_target_subset hUN hzf
    have hO := c.subtypeRestr_symm_apply hON hzd
    have hW' : ((e.symm z : W) : U) = f.symm z := by
      simpa only [Function.comp_apply] using hW
    have hU' : ((f.symm z : U) : O) = d.symm z := by
      simpa only [Function.comp_apply] using hU
    have hO' : ((d.symm z : O) : X) = c.symm z := by
      simpa only [Function.comp_apply] using hO
    have hval : ((((x z : W) : U) : O) : X) = c.symm z := by
      calc
        ((((x z : W) : U) : O) : X) = (((f.symm z : U) : O) : X) :=
          congrArg (fun y : U => ((y : O) : X)) (by simpa only [x] using hW')
        _ = ((d.symm z : O) : X) :=
          congrArg (fun y : O => (y : X)) hU'
        _ = c.symm z := hO'
    simpa only [c] using hval.symm
  have hescape : Tendsto (fun z => (x z : U))
      (𝓝[≠] (chartAt ℂ b b)) (cocompact U) := by
    rw [hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    have hKi : IsCompact
        (((fun y : U => ((y : O) : X)) '' K)) :=
      hK.image (continuous_subtype_val.comp continuous_subtype_val)
    have hbK : b ∉ ((fun y : U => ((y : O) : X)) '' K) := by
      rintro ⟨y, _, rfl⟩
      exact hnot y rfl
    have hnhds : (((fun y : U => ((y : O) : X)) '' K)ᶜ) ∈ 𝓝 b :=
      hKi.isClosed.isOpen_compl.mem_nhds hbK
    filter_upwards [hambient.eventually hnhds] with z hz hzx
    exact hz ⟨x z, hzx, rfl⟩
  exact ⟨hescape, hevent.mono fun z hz => ⟨hz, rfl⟩⟩

end FinitePunctureDiscs
end AreaDeficit.Surfaces
