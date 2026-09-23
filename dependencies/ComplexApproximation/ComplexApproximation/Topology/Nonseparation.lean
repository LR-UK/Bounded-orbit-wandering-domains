import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Nonseparation in plane domains

The disjoint closed-set case of Janiszewski's theorem, and its consequence:
a compact subset of a plane domain is full exactly when its relative
complement is connected. Thus domain homeomorphisms preserve fullness.
Neither simple connectivity nor an extension to the whole plane is required.

The continuous-logarithm proof was first developed in
EremenkosConjecture/DisjointFullUnions.lean and is generalised here.
-/

open Set Metric Function
open scoped Topology

namespace ComplexApproximation

theorem frontier_component_subset_compl {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : frontier (connectedComponentIn U z) ⊆ Uᶜ := by
  intro w hw hwU
  have hw' : (⟨w, hwU⟩ : U) ∈ closure (connectedComponent (⟨z, hz⟩ : U)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    simpa only [Set.mem_preimage, connectedComponentIn_eq_image hz] using hw.1
  rw [isClosed_connectedComponent.closure_eq] at hw'
  have hwc : w ∈ connectedComponentIn U z := by
    rw [connectedComponentIn_eq_image hz]
    exact ⟨⟨w, hwU⟩, hw', rfl⟩
  exact hw.2 ((hU.connectedComponentIn).interior_eq.symm ▸ hwc)

private theorem exp_difference_constant {S : Set ℂ} (hS : IsPreconnected S)
    {f g : ℂ → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (he : EqOn (Complex.exp ∘ f) (Complex.exp ∘ g) S)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) : f x - g x = f y - g y := by
  apply Complex.isCoveringMap_exp.constOn_of_comp hS (hf.sub hg) ?_ hx hy
  intro a ha b hb
  apply Subtype.ext
  change Complex.exp (f a - g a) = Complex.exp (f b - g b)
  have hea : Complex.exp (f a) = Complex.exp (g a) := he ha
  have heb : Complex.exp (f b) = Complex.exp (g b) := he hb
  rw [Complex.exp_sub, Complex.exp_sub, hea, heb,
    div_self (Complex.exp_ne_zero _), div_self (Complex.exp_ne_zero _)]

private theorem no_separating_component_of_disjoint
    (A B C : Set ℂ) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ)
    (hfront : frontier C ⊆ A ∪ B) {x y : ℂ}
    (hx : x ∈ (A ∪ B)ᶜ) (hy : y ∈ (A ∪ B)ᶜ)
    (hxC : x ∈ C) (hyC : y ∉ C) : False := by
  classical
  obtain ⟨θ, hθA, hθB, _⟩ := exists_continuous_zero_one_of_isClosed hA hB hAB
  let κ : ℂ := 2 * Real.pi * Complex.I
  have hκexp : Complex.exp κ = 1 := Complex.exp_two_pi_mul_I
  have hκne : κ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let t : ℂ → ℂ := fun z => (θ z : ℂ) * κ
  have ht : Continuous t := (Complex.continuous_ofReal.comp θ.continuous).mul continuous_const
  let F : ℂ → ℂ := fun z => if z ∈ C then Complex.exp (t z) else 1
  have hF : Continuous F := by
    apply Continuous.if ?_ (Complex.continuous_exp.comp ht) continuous_const
    intro z hz
    rcases hfront hz with hzA | hzB
    · have H : θ z = 0 := hθA hzA
      simp [t, H]
    · have H : θ z = 1 := hθB hzB
      simpa [t, H] using hκexp
  have hFne (z : ℂ) : F z ≠ 0 := by
    dsimp [F]
    split_ifs
    · exact Complex.exp_ne_zero _
    · exact one_ne_zero
  have hsc : IsSimplyConnected (univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨L, hL, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hF.continuousOn (by rintro ⟨z, _, hz⟩; exact hFne z hz)
  have hLcont : Continuous L := continuousOn_univ.mp hL
  let u : ℂ → ℂ := fun z => if z ∈ C then t z - κ else 0
  let v : ℂ → ℂ := fun z => if z ∈ C then t z else 0
  have hu : ContinuousOn u Aᶜ := by
    apply ContinuousOn.if ?_ (ht.sub continuous_const).continuousOn continuousOn_const
    intro z hz
    have hzB : z ∈ B := (hfront hz.2).resolve_left hz.1
    have H : θ z = 1 := hθB hzB
    simp [t, H, κ]
  have hv : ContinuousOn v Bᶜ := by
    apply ContinuousOn.if ?_ ht.continuousOn continuousOn_const
    intro z hz
    have hzA : z ∈ A := (hfront hz.2).resolve_right hz.1
    have H : θ z = 0 := hθA hzA
    simp [t, H]
  have hue (z : ℂ) : Complex.exp (u z) = F z := by
    by_cases hz : z ∈ C
    · simp only [u, F, ite_eq_left hz, Complex.exp_sub, hκexp, div_one]
    · simp [u, F, hz]
  have hve (z : ℂ) : Complex.exp (v z) = F z := by
    by_cases hz : z ∈ C <;> simp [v, F, hz]
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  have hyA : y ∈ Aᶜ := fun h => hy (Or.inl h)
  have hyB : y ∈ Bᶜ := fun h => hy (Or.inr h)
  have H₁ := exp_difference_constant hAc hLcont.continuousOn hu
    (fun z _ => (hLe (mem_univ z)).trans (hue z).symm) hxA hyA
  have H₂ := exp_difference_constant hBc hLcont.continuousOn hv
    (fun z _ => (hLe (mem_univ z)).trans (hve z).symm) hxB hyB
  simp only [u, v, ite_eq_left hxC, ite_eq_right hyC, sub_zero] at H₁ H₂
  apply hκne
  linear_combination H₁ - H₂


/-- Disjoint closed nonseparating plane sets have nonseparating union.
The conclusion uses preconnectedness to allow an empty complement. -/
theorem isPreconnected_compl_union_disjoint (A B : Set ℂ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) :
    IsPreconnected (A ∪ B)ᶜ := by
  rcases ((A ∪ B)ᶜ).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]
    exact isPreconnected_empty
  · have heq : connectedComponentIn (A ∪ B)ᶜ x = (A ∪ B)ᶜ := by
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      intro y hy
      by_contra hyC
      exact no_separating_component_of_disjoint A B _ hA hB hAB hAc hBc
        (by simpa only [compl_compl] using
          frontier_component_subset_compl (hA.union hB).isOpen_compl hx)
        hx hy (mem_connectedComponentIn hx) hyC
    rw [← heq]
    exact (isConnected_connectedComponentIn_iff.mpr hx).isPreconnected

/-- Every component of the complement of a closed set meets any nonempty
open neighbourhood of that set. -/
theorem complement_component_meets_domain (K U : Set ℂ)
    (hK : IsClosed K) (hU : IsOpen U) (hne : U.Nonempty) (hKU : K ⊆ U)
    {z : ℂ} (hz : z ∉ K) : (connectedComponentIn Kᶜ z ∩ U).Nonempty := by
  by_contra h
  have hCU : connectedComponentIn Kᶜ z ⊆ Uᶜ := by
    intro w hw hwU
    exact h ⟨w, hw, hwU⟩
  have hfront : frontier (connectedComponentIn Kᶜ z) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hwK : w ∈ K := by
      simpa only [compl_compl] using frontier_component_subset_compl hK.isOpen_compl hz hw
    exact (closure_minimal hCU hU.isClosed_compl hw.1) (hKU hwK)
  have heq : connectedComponentIn Kᶜ z = univ :=
    (frontier_eq_empty_iff.mp hfront).resolve_left
      (nonempty_iff_ne_empty.mp ⟨z, mem_connectedComponentIn hz⟩)
  obtain ⟨w, hw⟩ := hne
  exact hCU (heq.symm ▸ mem_univ w) hw

/-- A compact subset of a (nonempty connected open) plane domain is full
if and only if its complement relative to that domain is connected. -/
theorem isConnected_compl_iff_domain_diff (K U : Set ℂ)
    (hK : IsCompact K) (hU : IsOpen U) (hUc : IsConnected U) (hKU : K ⊆ U) :
    IsConnected Kᶜ ↔ IsConnected (U \ K) := by
  constructor
  · intro hfull
    have hpre := isPreconnected_compl_union_disjoint K Uᶜ hK.isClosed
      hU.isClosed_compl (disjoint_left.mpr (fun z hz hzU => hzU (hKU hz)))
      hfull.isPreconnected (by simpa only [compl_compl] using hUc.isPreconnected)
    have heq : (K ∪ Uᶜ)ᶜ = U \ K := by ext z; simp only [mem_compl_iff,
      mem_union, not_or, not_not, mem_sdiff]; exact and_comm
    rw [heq] at hpre
    refine ⟨?_, hpre⟩
    obtain ⟨z, hz⟩ := hfull.nonempty
    obtain ⟨w, hwC, hwU⟩ := complement_component_meets_domain K U hK.isClosed hU
      hUc.nonempty hKU hz
    exact ⟨w, hwU, connectedComponentIn_subset Kᶜ z hwC⟩
  · intro hdiff
    obtain ⟨x, hxU, hxK⟩ := hdiff.nonempty
    have hsub : U \ K ⊆ connectedComponentIn Kᶜ x :=
      hdiff.isPreconnected.subset_connectedComponentIn ⟨hxU, hxK⟩ (sdiff_subset_compl U K)
    have heq : connectedComponentIn Kᶜ x = Kᶜ := by
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      intro z hz
      obtain ⟨w, hwC, hwU⟩ := complement_component_meets_domain K U hK.isClosed hU
        hUc.nonempty hKU hz
      have hwx := hsub ⟨hwU, connectedComponentIn_subset Kᶜ z hwC⟩
      have hsame := (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwx).symm
      rw [← hsame]
      exact mem_connectedComponentIn hz
    rw [← heq]
    exact isConnected_connectedComponentIn_iff.mpr hxK

/-- Homeomorphisms between plane domains preserve fullness of compact subsets.
The map has its actual domain `U`; no values outside `U` or ambient extension
are supplied. In particular this applies to conformal isomorphisms. -/
theorem isConnected_compl_image_domain_homeomorph
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (e : U ≃ₜ V)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (hfull : IsConnected Kᶜ) :
    IsConnected ((fun z : U => (e z : ℂ)) '' ((↑) ⁻¹' K))ᶜ := by
  let φ : U → ℂ := fun z => (e z : ℂ)
  let L : Set ℂ := φ '' ((↑) ⁻¹' K)
  have hφ : Continuous φ := continuous_subtype_val.comp e.continuous
  have hφinj : Injective φ := Subtype.val_injective.comp e.injective
  have hLK : IsCompact L :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKU)).image hφ
  have hLV : L ⊆ V := by rintro w ⟨z, _, rfl⟩; exact (e z).property
  apply (isConnected_compl_iff_domain_diff L V hLK hV hVc hLV).mpr
  have hd := (isConnected_compl_iff_domain_diff K U hK hU hUc hKU).mp hfull
  have hp : IsConnected (((↑) : U → ℂ) ⁻¹' (U \ K)) :=
    hd.preimage_of_isOpenMap Subtype.val_injective hU.isOpenMap_subtype_val
      (by simpa only [Subtype.range_coe] using (sdiff_subset : U \ K ⊆ U))
  have heq : φ '' (((↑) : U → ℂ) ⁻¹' (U \ K)) = V \ L := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(e z).property, ?_⟩
      rintro ⟨y, hy, he⟩
      exact hz.2 ((hφinj he) ▸ hy)
    · rintro ⟨hwV, hwL⟩
      let z : U := e.symm ⟨w, hwV⟩
      have hz : φ z = w := congrArg Subtype.val (e.apply_symm_apply ⟨w, hwV⟩)
      refine ⟨z, ⟨z.property, ?_⟩, hz⟩
      intro hzK
      exact hwL ⟨z, hzK, hz⟩
  rw [← heq]
  exact hp.image φ hφ.continuousOn

end ComplexApproximation
