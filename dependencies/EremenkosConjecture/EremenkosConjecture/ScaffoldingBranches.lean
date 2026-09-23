import EremenkosConjecture.ScaffoldingStability
import EremenkosConjecture.ConformalEmbedding
import ComplexDynamics.Iteration
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # The inverse branches through successive source strips -/

open Set Metric Function Complex

namespace EremenkosConjecture.Scaffolding

theorem exists_source_chart {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100) (j : ℕ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.source = openInsetSourceStrip j ∧
      sourceStrip (j + 1) ∪ targetStrip (j + 1) ⊆ e.target ∧
      (∀ z, e z = f z) ∧ DifferentiableOn ℂ e.symm e.target := by
  have hsub : openInsetSourceStrip j ⊆ sourceStrips :=
    (openInsetSourceStrip_subset j).trans ((insetSourceStrip_subset j).trans (subset_iUnion _ j))
  obtain ⟨e, heS, heT, he, hei⟩ := exists_conformal_chart_of_injOn
    (isOpen_openInsetSourceStrip j) (hf.mono hsub)
    ((injective_on_inset_sourceStrip hf hclose j).mono (openInsetSourceStrip_subset j))
    (by
      intro z hz hn
      have H := (derivative_bounds_on_inset hf hclose (openInsetSourceStrip_subset j hz)).1
      simp only [hn, norm_zero] at H
      norm_num at H)
  exact ⟨e, heS, heT.symm ▸ next_strips_subset_image hf hclose j, he, hei⟩

noncomputable def chartChain (e : ℕ → OpenPartialHomeomorph ℂ ℂ) : ℕ → OpenPartialHomeomorph ℂ ℂ
  | 0 => OpenPartialHomeomorph.refl ℂ
  | n + 1 => (chartChain e n).trans (e n)

theorem chartChain_apply {e : ℕ → OpenPartialHomeomorph ℂ ℂ} {f : ℂ → ℂ}
    (he : ∀ n z, e n z = f z) (n : ℕ) (z : ℂ) : chartChain e n z = (f^[n]) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change e n (chartChain e n z) = _
      rw [he, ih, iterate_succ_apply']

theorem chartChain_target_eq {e : ℕ → OpenPartialHomeomorph ℂ ℂ} {n : ℕ}
    (hsub : (e n).source ⊆ (chartChain e n).target) :
    (chartChain e (n + 1)).target = (e n).target := by
  change (e n).target ∩ (e n).symm ⁻¹' (chartChain e n).target = (e n).target
  exact inter_eq_left.mpr (fun z hz => hsub ((e n).map_target hz))

theorem chartChain_inverse_holomorphic {e : ℕ → OpenPartialHomeomorph ℂ ℂ}
    (he : ∀ n, DifferentiableOn ℂ (e n).symm (e n).target) (n : ℕ) :
    DifferentiableOn ℂ (chartChain e n).symm (chartChain e n).target := by
  induction n with
  | zero => exact differentiableOn_id
  | succ n ih =>
      exact ih.comp ((he n).mono inter_subset_left) (fun z hz => hz.2)

theorem chartChain_orbit {e : ℕ → OpenPartialHomeomorph ℂ ℂ} {f : ℂ → ℂ}
    (he : ∀ n z, e n z = f z) (n : ℕ) :
    ∀ k < n, MapsTo (f^[k]) (chartChain e n).source (e k).source := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk z hz
      by_cases hkn : k < n
      · exact ih k hkn hz.1
      · have hkn : k = n := by omega
        subst k
        have H : chartChain e n z ∈ (e n).source := hz.2
        rwa [chartChain_apply he] at H

/-- The conformal isomorphisms `f^j : V_j → T_j` and their intermediate
source-strip itinerary from Lemma 4.1. Uniform bounds hold at every orbit point. -/
theorem exists_iterated_strip_chart {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (j : ℕ) (hj : 0 < j) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.target = targetStrip j ∧ e.source ⊆ sourceStrip 0 ∧
      (∀ z, e z = (f^[j]) z) ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀ k < j, MapsTo (f^[k]) e.source (sourceStrip k)) ∧
      ∀ k < j, ∀ z ∈ e.source, 2 ≤ ‖deriv f ((f^[k]) z)‖ ∧
        ‖deriv f ((f^[k]) z)‖ ≤ 8 := by
  classical
  choose c hcS hcT hc hcI using exists_source_chart hf hclose
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
  have hsource : e.source ⊆ sourceStrip 0 := by
    intro z hz
    exact insetSourceStrip_subset 0 (horbit 0 hj hz)
  have hsourceOrbit : ∀ k < j, MapsTo (f^[k]) e.source (sourceStrip k) :=
    fun k hk z hz => insetSourceStrip_subset k (horbit k hk hz)
  refine ⟨e, heT, hsource, he, ?_, ?_, hsourceOrbit, ?_⟩
  · have H := ComplexDynamics.differentiableOn_iterate_of_mapsTo f sourceStrips e.source hf j
      (fun k hk z hz => mem_iUnion.mpr ⟨k, hsourceOrbit k hk hz⟩)
    exact H.congr (fun z _ => he z)
  · exact (chartChain_inverse_holomorphic hcI j).mono inter_subset_left
  · intro k hk z hz
    exact derivative_bounds_on_inset hf hclose (horbit k hk hz)

end EremenkosConjecture.Scaffolding
