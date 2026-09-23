import CompactCutoff
import CompactDeficit
import ConformalLaplacian
import LocalMetricComparison
import LocalPunctures
import HolomorphicTransport

open Set Metric MeasureTheory Filter Function Laplacian
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

theorem measurable_density (G : FinitePunctureMetricInput)
    {P : Finset ℂ} (hP : 2 ≤ P.card) : Measurable (G.density P) :=
  (G.smooth P hP).continuousOn.measurable_of_countable_compl
    (by simpa using P.finite_toSet.countable)

/-- The uniform integral estimate is deduced from the classical metric
input. The constant is chosen before the punctures and the measured set. -/
theorem local_integrated_deficit (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (E : Finset ℂ)
    (hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) →
      ∀ W : Set ℂ, MeasurableSet W → W ⊆ K →
      (∀ w ∈ W, f w ∉ P ∪ E) →
      (∫⁻ z in W, ENNReal.ofReal ((G.density P z)^2) -
        ENNReal.ofReal ((‖deriv f z‖ * G.density (P ∪ E) (f z))^2)) ≤ C := by
  classical
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨chi, hchi, hc, hsupp, hchi0, hchiK⟩ :=
    exists_compact_cutoff hK isOpen_interior hKL
  obtain ⟨M, hM, H⟩ := G.compact_log_comparison hV hf hn hL hLV hab E hE
  refine ⟨ENNReal.ofReal (M * ∫ x, |Δ chi x|), ENNReal.ofReal_ne_top, ?_⟩
  intro P ha hb hforward W hW hWK hWQ
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hQ : 2 ≤ (P ∪ E).card := hP.trans (Finset.card_le_card Finset.subset_union_left)
  have hF := finite_local_preimage hL (hf.mono hLV)
    (fun x hx => hn x (hLV hx)) (P ∪ E).finite_toSet
  let F := hF.toFinset
  have hxQ : ∀ x ∈ interior L, x ∉ F → f x ∉ P ∪ E := by
    intro x hx hxF hxq
    exact hxF (hF.mem_toFinset.mpr ⟨interior_subset hx, hxq⟩)
  have hxP : ∀ x ∈ interior L, x ∉ F → x ∉ P := by
    intro x hx hxF hxp
    exact hxQ x hx hxF (Finset.mem_union_left E
      (hforward x (hLV (interior_subset hx)) hxp))
  have hreg : ∀ x ∈ interior L, x ∉ F → deriv f x ≠ 0 := by
    intro x hx hxF heq
    exact hxQ x hx hxF (Finset.mem_union_right P
      (hE x (hLV (interior_subset hx)) heq))
  have hsmooth : ∀ (Q : Finset ℂ), 2 ≤ Q.card → ∀ x, x ∉ Q →
      ContDiffAt ℝ 2 (G.density Q) x := by
    intro Q hQ x hx
    exact (G.smooth Q hQ).contDiffAt (Q.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
  apply density_deficit_on_set F isOpen_interior hW hM hchi hc hchi0 hsupp
    (fun x hx => hchiK x (hWK hx)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx hxF
    exact hWQ x hx (hF.mem_toFinset.mp hxF).2
  · intro x hx hxF
    exact ⟨G.positive P hP x (hxP x hx hxF), hsmooth P hP x (hxP x hx hxF)⟩
  · intro x hx hxF
    exact ⟨mul_pos (norm_pos_iff.mpr (hreg x hx hxF))
        (G.positive (P ∪ E) hQ (f x) (hxQ x hx hxF)),
      pullback_density_contDiffAt (hsmooth (P ∪ E) hQ (f x) (hxQ x hx hxF))
        (hf x (hLV (interior_subset hx))) (hreg x hx hxF)⟩
  · intro x hx hxF
    exact G.curvature P hP x (hxP x hx hxF)
  · intro x hx hxF
    exact pullback_density_curvature
      (hsmooth (P ∪ E) hQ (f x) (hxQ x hx hxF))
      (G.positive (P ∪ E) hQ (f x) (hxQ x hx hxF))
      (G.curvature (P ∪ E) hQ (f x) (hxQ x hx hxF))
      (hf x (hLV (interior_subset hx))) (hreg x hx hxF)
  · intro x hx hxF
    exact H P ha hb hforward x (interior_subset hx) (hxQ x hx hxF)

/-- Normalisation commutes with forming the density measure. -/
theorem area_eq_scaled_square (G : FinitePunctureMetricInput) (P : Finset ℂ) :
    G.area P = ENNReal.ofReal (1 / (2 * Real.pi)) •
      volume.withDensity (fun z => ENNReal.ofReal ((G.density P z)^2)) := by
  rw [area, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Uniform area advance for an injective measurable source set, with
curvature −1 and area divided by 2π. -/
theorem local_area_advance (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (E : Finset ℂ)
    (hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) →
      ∀ W : Set ℂ, MeasurableSet W → W ⊆ K → InjOn f W →
      (∀ w ∈ W, f w ∉ P ∪ E) →
      G.area P W ≤ G.area (P ∪ E) (f '' W) + C := by
  obtain ⟨C, hC, H⟩ := G.local_integrated_deficit hV hf hn hK hKV hab E hE
  refine ⟨ENNReal.ofReal (1 / (2 * Real.pi)) * C,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC, ?_⟩
  intro P ha hb hforward W hW hWK hinj hWQ
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hQ : 2 ≤ (P ∪ E).card := hP.trans (Finset.card_le_card Finset.subset_union_left)
  have h := holomorphic_area_advance_of_density_deficit hW
    (fun z hz => (hf z (hKV (hWK hz))).differentiableAt.hasDerivAt)
    hinj (G.measurable_density hQ) (H P ha hb hforward W hW hWK hWQ)
  rw [G.area_eq_scaled_square P, G.area_eq_scaled_square (P ∪ E)]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_right h _).trans_eq (mul_add _ _ _)

/-- One finite bound works for every puncture set and every injective
forward configuration supported in K. In particular it is independent
of a hyperbolic disc radius and of the starting time of its orbit tail. -/
theorem local_cancellation_bound (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (E : Finset ℂ)
    (hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E) :
    ∃ H : ℝ≥0∞, H ≠ ∞ ∧ ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) →
      ∀ B W : Set ℂ, MeasurableSet B → MeasurableSet W → B ⊆ W → W ⊆ K →
      InjOn f W → f '' W ⊆ W \ B → (∀ w ∈ W, f w ∉ P ∪ E) →
      G.area P B ≤ H := by
  obtain ⟨C, hC, H⟩ := G.local_area_advance hV hf hn hK hKV hab E hE
  refine ⟨(E.card : ℝ≥0∞) + C, ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hC⟩, ?_⟩
  intro P ha hb hforward B W hB hW hBW hWK hinj himage hWQ
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hfW := hW.image_of_continuousOn_injOn (hf.continuousOn.mono (hWK.trans hKV)) hinj
  apply finite_area_cancellation hB hBW
    (ne_top_of_le_ne_top (G.area_finite P hP) (measure_mono (subset_univ W)))
    himage (H P ha hb hforward W hW hWK hinj hWQ)
  have hd : ((E \ P).card : ℝ≥0∞) ≤ (E.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : E \ P ⊆ E)
  exact (G.insertion_area_cost hP hfW).trans (add_le_add le_rfl hd)

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.local_integrated_deficit
#print axioms AreaDeficit.FinitePunctureMetricInput.local_area_advance
#print axioms AreaDeficit.FinitePunctureMetricInput.local_cancellation_bound
