import EremenkosConjecture.HolomorphicGluing
import EremenkosConjecture.ScaffoldingBackground
import ComplexApproximation.Topology.HomeomorphicTail
import ComplexApproximation.Arakelian
import ComplexApproximation.ArakelianGluing
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding ComplexApproximation

/-- The reference function for one step, expressed using the current local
chart. Its existence and entire approximation are proved below. -/
structure LocalReference (f ψ : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ)
    (j : ℕ) (B C : Set ℂ) where
  g : ℂ → ℂ
  domain : Set ℂ
  open_domain : IsOpen domain
  contains : (background j ∪ e '' B) ∪ e '' C ⊆ domain
  holomorphic : DifferentiableOn ℂ g domain
  background_eq : EqOn g f (background j)
  barrier_eq : EqOn g (fun _ => 0) (e '' B)
  return_eq : ∀ z ∈ C, g (e z) = ψ z

theorem exists_localReference
    {f ψ : ℂ → ℂ} (hf : Differentiable ℂ f)
    (e : OpenPartialHomeomorph ℂ ℂ) (hei : DifferentiableOn ℂ e.symm e.target)
    {U B C : Set ℂ} {j : ℕ} (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U)
    (hB : IsClosed B) (hC : IsClosed C) (hBC : Disjoint B C)
    (hsource : B ∪ C ⊆ e.source) (hCU : C ⊆ U)
    (htail : HasHomeomorphicTailOn e (B ∪ C))
    (hT : MapsTo e (B ∪ C) (targetStrip j)) :
    Nonempty (LocalReference f ψ e j B C) := by
  have hBU : B ⊆ e.source := subset_union_left.trans hsource
  have hCS : C ⊆ e.source := subset_union_right.trans hsource
  have hBe : IsClosed (e '' B) := (htail.mono subset_union_left).isClosed_image
    hB (e.continuousOn.mono hBU)
  have hCe : IsClosed (e '' C) := (htail.mono subset_union_right).isClosed_image
    hC (e.continuousOn.mono hCS)
  let W := e '' (U ∩ e.source)
  have hW : IsOpen W := e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hWT : W ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source hz.2
  have hWU : MapsTo e.symm W U := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [e.left_inv hz.2] using hz.1
  have hCW : e '' C ⊆ W := image_mono (fun z hz => ⟨hCU hz, hCS hz⟩)
  have hhol : DifferentiableOn ℂ (ψ ∘ e.symm) W := hψ.comp (hei.mono hWT) hWU
  have hbgB : Disjoint (background j) (e '' B) :=
    (disjoint_background_targetStrip j).mono_right
      (by rintro _ ⟨z, hz, rfl⟩; exact hT (Or.inl hz))
  have hbgC : Disjoint (background j) (e '' C) :=
    (disjoint_background_targetStrip j).mono_right
      (by rintro _ ⟨z, hz, rfl⟩; exact hT (Or.inr hz))
  have heBC : Disjoint (e '' B) (e '' C) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact disjoint_left.mp hBC hx ((e.injOn (hCS hy) (hBU hx) hxy) ▸ hy)
  obtain ⟨D, g, hD, hcontains, hg, hbg, hbar, hreturn⟩ :=
    exists_holomorphic_gluing_three_closed (background j) (e '' B) (e '' C)
      univ univ W (isArakelian_background j).isClosed hBe hCe hbgB hbgC heBC
      isOpen_univ isOpen_univ hW (subset_univ _) (subset_univ _) hCW
      f (fun _ => 0) (ψ ∘ e.symm) hf.differentiableOn (differentiableOn_const 0) hhol
  refine ⟨⟨g, D, hD, hcontains, hg,
    fun z hz => (hbg z hz).eq_of_nhds,
    fun z hz => (hbar z hz).eq_of_nhds, ?_⟩⟩
  intro z hz
  simpa only [comp_apply, e.left_inv (hCS hz)] using
    (hreturn (e z) (mem_image_of_mem e hz)).eq_of_nhds

theorem LocalReference.exists_entire_approximation
    {f ψ : ℂ → ℂ} {e : OpenPartialHomeomorph ℂ ℂ} {j : ℕ} {B C : Set ℂ}
    (P : LocalReference f ψ e j B C)
    (hArak : IsArakelian ((background j ∪ e '' B) ∪ e '' C))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ z ∈ (background j ∪ e '' B) ∪ e '' C, dist (F z) (P.g z) < ε := by
  obtain ⟨F, hF, hclose⟩ := arakelian_approximation_of_holomorphic _ hArak
    P.domain P.open_domain P.contains P.g P.holomorphic ε hε
  exact ⟨F, hF, fun z hz => by simpa only [dist_eq_norm] using hclose z hz⟩

end EremenkosConjecture
