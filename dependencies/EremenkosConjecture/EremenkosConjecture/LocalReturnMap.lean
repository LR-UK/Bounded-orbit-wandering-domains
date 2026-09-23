import EremenkosConjecture.ScaffoldingAmbientBranches
import ComplexApproximation.Topology.HomeomorphicTail

open Set Function

namespace EremenkosConjecture.Scaffolding

/-- Pull back an arbitrary injective holomorphic map through the Section 4
branch. A homeomorphism on its tail suffices for all intermediate return maps;
the bounded decoration requires no ambient extension. -/
theorem exists_return_map_with_homeomorphic_tail
    {f φ : ℂ → ℂ} {U C : Set ℂ} {j : ℕ}
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (hj : 0 < j) (hφ : DifferentiableOn ℂ φ U) (hφinj : InjOn φ U)
    (hφT : MapsTo φ U (targetStrip j)) (hCU : C ⊆ U)
    (hφtail : ComplexApproximation.HasHomeomorphicTailOn φ C) :
    ∃ ψ : ℂ → ℂ,
      (∀ k ≤ j, DifferentiableOn ℂ (fun z => (f^[k]) (ψ z)) U) ∧
      EqOn (fun z => (f^[j]) (ψ z)) φ U ∧
      (∀ k < j, MapsTo (fun z => (f^[k]) (ψ z)) U (insetSourceStrip k)) ∧
      (∀ k ≤ j, InjOn (fun z => (f^[k]) (ψ z)) U) ∧
      (∀ k ≤ j, ComplexApproximation.HasHomeomorphicTailOn
        (fun z => (f^[k]) (ψ z)) C) := by
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
  refine ⟨ψ, fun k hk => (hext k hk).1.comp hψ hsource,
    hfinal, fun k hk z hz => horbit k hk (hsource hz), ?_, ?_⟩
  · intro k hk x hx y hy hxy
    apply hφinj hx hy
    apply ((H j).symm.trans (H k)).injective
    exact (heq k hk hx).symm.trans (hxy.trans (heq k hk hy))
  · intro k hk
    exact (hφtail.homeomorph_comp ((H j).symm.trans (H k))).congr
      ((heq k hk).mono hCU)

end EremenkosConjecture.Scaffolding
