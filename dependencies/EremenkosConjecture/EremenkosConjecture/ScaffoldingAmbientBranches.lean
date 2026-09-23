import EremenkosConjecture.ScaffoldingAmbient
import EremenkosConjecture.BiLipschitzChains

/-! # Section 4 inverse branches with quantitative ambient charts -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture.Scaffolding

theorem exists_iterated_strip_chart_with_ambient {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (j : ℕ) (hj : 0 < j) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (H : ℕ → ℂ ≃ₜ ℂ),
      e.target = targetStrip j ∧ e.source ⊆ sourceStrip 0 ∧
      (∀ z, e z = (f^[j]) z) ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀ k < j, MapsTo (f^[k]) e.source (insetSourceStrip k)) ∧
      ∀ k ≤ j, DifferentiableOn ℂ (f^[k]) e.source ∧ EqOn (f^[k]) (H k) e.source ∧
        ∃ L L' : ℝ≥0, LipschitzWith L (H k) ∧ LipschitzWith L' (H k).symm := by
  classical
  choose c hcS hcT hc hcI using exists_source_chart hf hclose
  choose G hG hGL using exists_bilipschitz_inset_extension hf hclose
  have hcover (n : ℕ) : sourceStrip n ∪ targetStrip n ⊆ (chartChain c n).target := by
    induction n with
    | zero => exact subset_univ _
    | succ n ih =>
        have hsub : (c n).source ⊆ (chartChain c n).target := by
          rw [hcS n]
          exact (openInsetSourceStrip_subset n).trans
            ((insetSourceStrip_subset n).trans (subset_union_left.trans ih))
        rw [chartChain_target_eq hsub]
        exact hcT n
  let e := ((chartChain c j).symm.restrOpen (targetStrip j) (isOpen_targetStrip j)).symm
  have heT : e.target = targetStrip j :=
    inter_eq_right.mpr (subset_union_right.trans (hcover j))
  have heS : e.source ⊆ (chartChain c j).source := inter_subset_left
  have he (z : ℂ) : e z = (f^[j]) z := chartChain_apply hc j z
  have horbit : ∀ k < j, MapsTo (f^[k]) e.source (insetSourceStrip k) := by
    intro k hk z hz
    apply openInsetSourceStrip_subset k
    rw [← hcS k]
    exact chartChain_orbit hc j k hk (heS hz)
  have hsource : e.source ⊆ sourceStrip 0 := fun z hz =>
    insetSourceStrip_subset 0 (horbit 0 hj hz)
  refine ⟨e, ambientChain G, heT, hsource, he,
    (chartChain_inverse_holomorphic hcI j).mono inter_subset_left, horbit, ?_⟩
  intro k hk
  refine ⟨?_, ambientChain_eq_iterate hG (fun i hi => horbit i (hi.trans_le hk)),
    exists_lipschitz_ambientChain G hGL k⟩
  exact ComplexDynamics.differentiableOn_iterate_of_mapsTo f sourceStrips e.source hf k
    (fun i hi z hz => mem_iUnion.mpr ⟨i, insetSourceStrip_subset i (horbit i (hi.trans_le hk) hz)⟩)

end EremenkosConjecture.Scaffolding
