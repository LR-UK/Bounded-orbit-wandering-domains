import EremenkosConjecture.ScaffoldingAmbientBranches
import EremenkosConjecture.ScaffoldingRealEstimates
import EremenkosConjecture.RayStage

/-! # Pulling an explicit map back through a return branch -/

open Set Function
open scoped NNReal

namespace EremenkosConjecture.Scaffolding

theorem exists_return_map {f φ : ℂ → ℂ} {U C : Set ℂ} {j : ℕ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (hj : 0 < j) (hφ : DifferentiableOn ℂ φ U)
    (hφT : MapsTo φ U (targetStrip j)) (hCU : C ⊆ U)
    (hφext : HasQuantitativeExtensionOn φ C) :
    ∃ ψ : ℂ → ℂ,
      (∀ k ≤ j, DifferentiableOn ℂ (fun z => (f^[k]) (ψ z)) U) ∧
      EqOn (fun z => (f^[j]) (ψ z)) φ U ∧
      (∀ k < j, MapsTo (fun z => (f^[k]) (ψ z)) U (insetSourceStrip k)) ∧
      (∀ k ≤ j, HasQuantitativeExtensionOn (fun z => (f^[k]) (ψ z)) C) := by
  obtain ⟨e, H, heT, _, he, hehol, horbit, hext⟩ :=
    exists_iterated_strip_chart_with_ambient hf hclose j hj
  obtain ⟨P, hP, L, L', hL, hL'⟩ := hφext
  let ψ := e.symm ∘ φ
  have htarget : MapsTo φ U e.target := by simpa only [heT] using hφT
  have hsource : MapsTo ψ U e.source := fun z hz => e.map_target (htarget hz)
  have hψ : DifferentiableOn ℂ ψ U := hehol.comp hφ htarget
  have hfinal : EqOn (fun z => (f^[j]) (ψ z)) φ U := by
    intro z hz
    change (f^[j]) (ψ z) = φ z
    rw [← he]
    exact e.right_inv (htarget hz)
  have hinv : EqOn ψ ((H j).symm ∘ P) C := by
    intro z hz
    apply (H j).injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply, ← (hext j le_rfl).2.1 (hsource (hCU hz))]
    exact (hfinal (hCU hz)).trans (hP hz)
  refine ⟨ψ, fun k hk => (hext k hk).1.comp hψ hsource,
    hfinal, fun k hk z hz => horbit k hk (hsource hz), ?_⟩
  intro k hk
  obtain ⟨M, M', hM, hM'⟩ := (hext j le_rfl).2.2
  obtain ⟨N, N', hN, hN'⟩ := (hext k hk).2.2
  refine ⟨(P.trans (H j).symm).trans (H k), ?_, N * (M' * L), L' * (M * N'),
    hN.comp (hM'.comp hL), hL'.comp (hM.comp hN')⟩
  intro z hz
  change (f^[k]) (ψ z) = H k ((H j).symm (P z))
  rw [(hext k hk).2.1 (hsource (hCU hz)), hinv hz]
  rfl

theorem return_map_small_real_part {f ψ φ : ℂ → ℂ} {U : Set ℂ} {j : ℕ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (horbit : ∀ k < j, MapsTo (fun z => (f^[k]) (ψ z)) U (insetSourceStrip k))
    (hfinal : EqOn (fun z => (f^[j]) (ψ z)) φ U)
    {z : ℂ} (hz : z ∈ U) (hφ : |(φ z).re| < 1 / 2) : |(ψ z).re| < 1 / 2 := by
  apply abs_re_preimage_lt_half (n := j)
    (fun k hk => hclose _ (mem_iUnion.mpr ⟨k, insetSourceStrip_subset k (horbit k hk hz)⟩))
  simpa only [hfinal hz] using hφ

theorem return_map_large_real_parts {f ψ φ : ℂ → ℂ} {U : Set ℂ} {j : ℕ} {M : ℝ}
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (horbit : ∀ k < j, MapsTo (fun z => (f^[k]) (ψ z)) U (insetSourceStrip k))
    (hfinal : EqOn (fun z => (f^[j]) (ψ z)) φ U)
    (hM : 1 / 2 ≤ M) {z : ℂ} (hz : z ∈ U)
    (hφ : (φ z).re < -(6 : ℝ) ^ j * (M + 1)) :
    ∀ k ≤ j, M ≤ |((f^[k]) (ψ z)).re| := by
  have hc : ∀ k < j, ‖f ((f^[k]) (ψ z)) - 5 * (f^[k]) (ψ z)‖ ≤ 1 / 100 :=
    fun k hk => hclose _ (mem_iUnion.mpr ⟨k, insetSourceStrip_subset k (horbit k hk hz)⟩)
  have hleft : (ψ z).re < -M := re_preimage_far_left (by linarith) hc (by
    simpa only [hfinal hz] using hφ)
  apply abs_re_iterate_lower_bound hM _ hc
  exact (show M ≤ -(ψ z).re by linarith).trans (neg_le_abs _)

end EremenkosConjecture.Scaffolding
