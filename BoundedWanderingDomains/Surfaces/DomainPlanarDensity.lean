/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.DomainSchwarz
import BoundedWanderingDomains.Surfaces.DomainChartDensity
import BoundedWanderingDomains.GeneralDomainMetric

/-! # Identification with the existing planar hyperbolic density

For a domain contained in one holomorphic chart, its intrinsic chart
density agrees with the previously constructed planar density. This lets
the checked planar puncture estimate be used locally on a surface.
-/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainChartDensity_eq_planar (p : DiscCover M)
    (U : TopologicalSpace.Opens M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hci : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c.symm c.target)
    (hUc : (U : Set M) ⊆ c.source)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ domainChartSet U c)
    (hb : b ∉ domainChartSet U c) (z : ℂ) :
    p.domainChartDensity U c z = closedComplementDensity
      (domainChartSet U c)ᶜ (isOpen_domainChartSet U c).isClosed_compl hab ha hb z := by
  classical
  let T := domainChartSet U c
  have hT : IsOpen T := isOpen_domainChartSet U c
  by_cases hz : z ∈ T
  · have hzA : z ∉ Tᶜ := not_not.mpr hz
    obtain ⟨q,hq⟩ := RiemannDynamics.exists_disc_covering_complement_component
      hT.isClosed_compl hzA hab ha hb
    rw [closedComplementDensity_eq_cover _ hT.isClosed_compl hab ha hb hzA hq,
      p.domainChartDensity_of_mem U c hz]
    let x : U := ⟨c.symm z,hz.2⟩
    have hxc : (x : M) ∈ c.source := c.map_target hz.1
    apply le_antisymm
    · obtain ⟨t,ht,htm,ht0,he⟩ := hq.density_extremal (mem_connectedComponentIn hzA)
      have htT : ∀ v : unitDisc, t v ∈ T := by
        intro v
        exact not_not.mp (connectedComponentIn_subset _ _ (htm v.property))
      let g : unitDisc → M := fun v => c.symm (t v)
      have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
        intro v
        apply ((hci _ (htT v).1).mdifferentiableAt
          (c.open_target.mem_nhds (htT v).1)).comp v
        exact mdifferentiableAt_subtype_iff.mpr
          ((ht.differentiableAt (isOpen_ball.mem_nhds v.property)).mdifferentiableAt)
      have hgm : ∀ v, g v ∈ U := fun v => (htT v).2
      have hg0 : g discZero = (x : M) := congrArg c.symm ht0
      have hcg : planeExtension (c ∘ g) =ᶠ[𝓝 (0 : ℂ)] t := by
        filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball 0 1 by simp)] with v hv
        rw [show v = ((⟨v,hv⟩ : unitDisc) : ℂ) from rfl,planeExtension_coe]
        exact c.right_inv (htT ⟨v,hv⟩).1
      have hs := p.domainDensity_schwarz_disc U hg hgm hc (hg0.symm ▸ hxc)
      have heq : (⟨g discZero,hgm discZero⟩ : U) = x := Subtype.ext hg0
      rw [heq,hcg.deriv_eq] at hs
      have hn : 0 < ‖deriv t 0‖ := by
        have hnn := norm_nonneg (deriv t 0)
        by_contra hn
        have he0 := le_antisymm (le_of_not_gt hn) hnn
        rw [he0,mul_zero] at he
        norm_num at he
      exact (mul_le_mul_iff_left₀ hn).mp (hs.trans_eq he.symm)
    · obtain ⟨g,hg,hg0,hgm,he⟩ := p.domainDensity_extremal_disc U hc (x := x) hxc
      let t := planeExtension (c ∘ g)
      have ht : DifferentiableOn ℂ t (ball 0 1) := by
        apply planeExtension_differentiableOn
        intro v
        exact ((hc _ (hUc (hgm v))).mdifferentiableAt
          (c.open_source.mem_nhds (hUc (hgm v)))).comp v (hg v)
      have ht0 : t 0 = z := by
        change planeExtension (c ∘ g) (discZero : ℂ) = z
        rw [planeExtension_coe]
        dsimp only [comp_apply]
        rw [hg0]
        exact c.right_inv hz.1
      have htm : MapsTo t (ball 0 1) T := by
        intro v hv
        have heq : t v = c (g ⟨v,hv⟩) := planeExtension_coe _ (⟨v,hv⟩ : unitDisc)
        rw [heq]
        refine ⟨c.map_source (hUc (hgm _)),?_⟩
        change c.symm (c (g ⟨v,hv⟩)) ∈ U
        rw [c.left_inv (hUc (hgm _))]
        exact hgm _
      have hcomp : MapsTo t (ball 0 1) (connectedComponentIn Tᶜᶜ z) := by
        rw [compl_compl,mapsTo_iff_image_subset]
        apply (isPreconnected_ball.image t ht.continuousOn).subset_connectedComponentIn
        · exact ⟨0,by simp,ht0⟩
        · exact htm.image_subset
      have hs := hq.density_schwarz ht hcomp
      rw [ht0] at hs
      have hn : 0 < ‖deriv t 0‖ := by
        have hnn := norm_nonneg (deriv t 0)
        by_contra hn
        have he0 := le_antisymm (le_of_not_gt hn) hnn
        change p.domainDensity U c x * ‖deriv t 0‖ = 2 at he
        rw [he0,mul_zero] at he
        norm_num at he
      exact (mul_le_mul_iff_left₀ hn).mp (hs.trans_eq he.symm)
  · have hz' : ¬ z ∉ Tᶜ := by simpa only [mem_compl_iff,not_not] using hz
    change z ∉ domainChartSet U c at hz
    change ¬ z ∉ (domainChartSet U c)ᶜ at hz'
    simp only [domainChartDensity,dite_eq_right hz,closedComplementDensity,dite_eq_right hz']

end AreaDeficit.Surfaces.DiscCover
