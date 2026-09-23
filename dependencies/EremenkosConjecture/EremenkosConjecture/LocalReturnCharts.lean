import EremenkosConjecture.ScaffoldingAmbientBranches
import EremenkosConjecture.LocalChartImageChange

open Set Function
open scoped NNReal

namespace EremenkosConjecture.Scaffolding

/-- The Section 4 inverse branch carries all the closed-inset chart estimates
through every intermediate return iterate. The same return map works for
every inset of the prescribed conformal domain. -/
theorem exists_return_map_with_local_charts
    {f φ : ℂ → ℂ} {U : Set ℂ} {j : ℕ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (hj : 0 < j) (hφ : DifferentiableOn ℂ φ U)
    (hφT : MapsTo φ U (targetStrip j)) :
    ∃ ψ : ℂ → ℂ,
      (∀ k ≤ j, DifferentiableOn ℂ (fun z => (f^[k]) (ψ z)) U) ∧
      EqOn (fun z => (f^[j]) (ψ z)) φ U ∧
      (∀ k < j, MapsTo (fun z => (f^[k]) (ψ z)) U (insetSourceStrip k)) ∧
      ∀ (P : Set ℂ) (D : LocalIterateChart φ 1 P), D.chart.source = U →
        ∀ k ≤ j, ∃ E : LocalIterateChart (fun z => (f^[k]) (ψ z)) 1 P,
          E.chart.source = U := by
  obtain ⟨e, H, heT, _, he, hehol, horbit, hext⟩ :=
    exists_iterated_strip_chart_with_ambient hf hclose j hj
  let ψ := e.symm ∘ φ
  have htarget : MapsTo φ U e.target := by simpa only [heT] using hφT
  have hsource : MapsTo ψ U e.source := fun z hz => e.map_target (htarget hz)
  have hψ : DifferentiableOn ℂ ψ U := hehol.comp hφ htarget
  have hfinal : EqOn (fun z => (f^[j]) (ψ z)) φ U := by
    intro z hz
    change (f^[j]) (ψ z) = φ z
    rw [← he]
    exact e.right_inv (htarget hz)
  have hinv : EqOn ψ ((H j).symm ∘ φ) U := by
    intro z hz
    apply (H j).injective
    rw [comp_apply, Homeomorph.apply_symm_apply,
      ← (hext j le_rfl).2.1 (hsource hz)]
    exact hfinal hz
  have heq (k : ℕ) (hk : k ≤ j) :
      EqOn (fun z => (f^[k]) (ψ z)) (((H j).symm.trans (H k)) ∘ φ) U := by
    intro z hz
    change (f^[k]) (ψ z) = (H k) ((H j).symm (φ z))
    rw [(hext k hk).2.1 (hsource hz), hinv hz]
    rfl
  have hhol (k : ℕ) (hk : k ≤ j) :
      DifferentiableOn ℂ (fun z => (f^[k]) (ψ z)) U :=
    (hext k hk).1.comp hψ hsource
  refine ⟨ψ, hhol, hfinal, fun k hk z hz => horbit k hk (hsource hz), ?_⟩
  intro P D hDU k hk
  obtain ⟨M, M', hM, hM'⟩ := (hext j le_rfl).2.2
  obtain ⟨N, N', hN, hN'⟩ := (hext k hk).2.2
  apply exists_localIterateChart_on_source_of_image_change D
    (by simpa only [iterate_one] using hhol k hk)
    (by simpa only [hDU] using D.chart.open_source)
    (by simpa only [hDU] using D.connected_source)
    (by rw [hDU]) (by simpa only [hDU] using D.contains) Subset.rfl
    ((H j).symm.trans (H k)) (hN.comp hM') (hM.comp hN')
  intro z hz
  change (f^[k]) (ψ z) = (H k) ((H j).symm (D.chart z))
  rw [D.agrees]
  exact heq k hk hz

end EremenkosConjecture.Scaffolding
