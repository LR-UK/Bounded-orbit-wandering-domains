module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.BackwardOrbitModels
public import FunctionTheory.NormalFamilies.ZalcmanMontel
public import ComplexDynamics.Basic
public import Mathlib.Order.OrderIsoNat

@[expose] public section

/-! # Montel normality off the closure of a two-point backward orbit -/

open Set Function Filter OnePoint NoWanderingDomains
open scoped Topology

namespace BoundedWanderingDomains

theorem normalSequenceOn_of_normal_family {X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y] {F : ℕ → X → Y} {U : Set X}
    (h : NoWanderingDomains.IsNormal (range F) U) :
    ComplexDynamics.IsNormalSequenceOn F U := by
  intro φ _
  obtain ⟨ψ, hψ, g, hg⟩ := h (fun n => ⟨F (φ n), mem_range_self _⟩)
  exact ⟨ψ, hψ, g ∘ Subtype.val,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hg⟩

/-- For a sequence indexed by the natural numbers, the sequential normality
used by `ComplexDynamics` is equivalent to normality of its range as a
family.  An arbitrary sequence drawn from the range either has a subsequence
whose original indices strictly increase, or has an eventually constant
subsequence. -/
theorem normal_family_of_normalSequenceOn {X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y] {F : ℕ → X → Y} {U : Set X}
    (h : ComplexDynamics.IsNormalSequenceOn F U) :
    NoWanderingDomains.IsNormal (range F) U := by
  classical
  intro seq
  choose u hu using fun n => (seq n).property
  have hseq (n : ℕ) : (seq n : X → Y) = F (u n) := (hu n).symm
  obtain ⟨e, he | he⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) u
  · have hue : StrictMono (u ∘ e) := fun m n hmn => he m n hmn
    obtain ⟨ψ, hψ, g, hg⟩ := h (u ∘ e) hue
    let G : X → Y := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else F 0 x
    refine ⟨e ∘ ψ, e.strictMono.comp hψ, G, ?_⟩
    have hgG : TendstoLocallyUniformly
        (fun n (z : U) => F ((u ∘ e) (ψ n)) z) (G ∘ Subtype.val) atTop :=
      hg.congr_right fun z => by simp [G, z.property]
    have hgU : TendstoLocallyUniformlyOn
        (fun n x => F ((u ∘ e) (ψ n)) x) G atTop U :=
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hgG
    exact hgU.congr fun n x _ => by
      exact congrFun (hseq ((e ∘ ψ) n)).symm x
  · have hue : Antitone (u ∘ e) := by
      intro m n hmn
      rcases hmn.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact Nat.le_of_not_gt (he m n hlt)
    obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hue
    let φ : ℕ → ℕ := fun n => e (N + n)
    have hφ : StrictMono φ := e.strictMono.comp (strictMono_nat_of_lt_succ fun n => by omega)
    refine ⟨φ, hφ, F (u (e N)), ?_⟩
    have hconst (n : ℕ) : (seq (φ n) : X → Y) = F (u (e N)) := by
      rw [hseq]
      exact congr_arg F (hN (N + n) (Nat.le_add_right N n)).symm
    have ht : TendstoUniformlyOn (fun _ : ℕ => F (u (e N)))
        (F (u (e N))) atTop U := by
      intro V hV
      exact Filter.Eventually.of_forall fun _ _ _ => refl_le_uniformity hV rfl
    exact ht.tendstoLocallyUniformlyOn.congr fun n x _ => congrFun (hconst n).symm x

/-- Normality of an indexed family passes simultaneously to a subsequence
and to restriction to an arbitrary subtype of the domain. -/
theorem normal_family_restrict_subsequence {X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y] {F : ℕ → X → Y} {W S : Set X}
    (h : NoWanderingDomains.IsNormal (range F) W) (σ : ℕ → ℕ) :
    NoWanderingDomains.IsNormal
      (range (fun n (z : S) => F (σ n) z))
      (((↑) : S → X) ⁻¹' W) := by
  classical
  intro seq
  choose u hu using fun n => (seq n).property
  let seqX : ℕ → range F := fun n => ⟨F (σ (u n)), mem_range_self _⟩
  obtain ⟨φ, hφ, g, hg⟩ := h seqX
  refine ⟨φ, hφ, g ∘ Subtype.val, ?_⟩
  have hcomp := hg.comp ((↑) : S → X)
    (fun _ hz => hz) continuous_subtype_val.continuousOn
  exact hcomp.congr fun n z _ => by
    exact congrFun (hu (φ n)) z

theorem mem_fatouSet_of_two_omitted_values
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ} (hab : a ≠ b)
    {U : Set ℂ} (hU : IsOpen U)
    (homit : ∀ n w, w ∈ U → (f^[n]) w ≠ a ∧ (f^[n]) w ≠ b) :
    U ⊆ ComplexDynamics.fatouSet f := by
  intro z hz
  have hnorm := FunctionTheory.isNormalAt_of_two_omitted_values
    (𝓕 := range (ComplexDynamics.sphericalIterate f)) hab hU
    (by
      rintro F ⟨n, rfl⟩
      exact (hf.iterate n).differentiableOn.sphereHolomorphicOn hU)
    (by
      rintro F ⟨n, rfl⟩ w hw
      exact ⟨fun h => (homit n w hw).1 (OnePoint.coe_injective h),
        fun h => (homit n w hw).2 (OnePoint.coe_injective h), OnePoint.coe_ne_infty _⟩) hz
  obtain ⟨V, hV, hn⟩ := hnorm
  have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
      ComplexDynamics.riemannSphereUniformSpace := unique_uniformity_of_compact rfl rfl
  rw [heq] at hn
  exact ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
    normalSequenceOn_of_normal_family (hn.mono interior_subset)⟩

theorem backwardOrbit_complement_subset_fatouSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ} (hab : a ≠ b) :
    (closure (twoPointBackwardOrbit f a b))ᶜ ⊆ ComplexDynamics.fatouSet f := by
  apply mem_fatouSet_of_two_omitted_values hf hab isClosed_closure.isOpen_compl
  intro n w hw
  exact ⟨fun h => hw (subset_closure ⟨n, Or.inl h⟩),
    fun h => hw (subset_closure ⟨n, Or.inr h⟩)⟩

/-- Every component after the initial one is recovered by the backward-orbit
obstacle. The two roots may be arbitrary distinct points of the initial component. -/
theorem backwardOrbit_complement_component
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ} (hab : a ≠ b)
    {U : ℕ → Set ℂ}
    (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (ha : a ∈ U 0) (hb : b ∈ U 0)
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ∈ U n) :
    connectedComponentIn (closure (twoPointBackwardOrbit f a b))ᶜ z = U n := by
  have hiter : ∀ k w, w ∈ U n → (f^[k]) w ∈ U (n + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro w hw
      simpa only [iterate_succ_apply', Nat.add_succ] using hfm (n + k) (ih w hw)
  obtain ⟨p, hp, hcomp⟩ := hU n
  have hUo : IsOpen (U n) := hcomp ▸ (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  have hUT : twoPointBackwardOrbit f a b ⊆ (U n)ᶜ := by
    rintro w ⟨k, hk⟩ hw
    have h := hiter k w hw
    rcases hk with hk | hk
    · exact disjoint_left.mp (hdis (by omega : n + k ≠ 0)) h (hk ▸ ha)
    · exact disjoint_left.mp (hdis (by omega : n + k ≠ 0)) h (hk ▸ hb)
  have hUC : U n ⊆ (closure (twoPointBackwardOrbit f a b))ᶜ := by
    intro w hw hc
    exact closure_minimal hUT hUo.isClosed_compl hc hw
  have hzcomp : connectedComponentIn (ComplexDynamics.fatouSet f) z = U n := by
    rw [hcomp] at hz ⊢
    exact (connectedComponentIn_eq hz).symm
  apply Subset.antisymm
  · rw [← hzcomp]
    exact connectedComponentIn_mono z (backwardOrbit_complement_subset_fatouSet hf hab)
  · have hc : IsPreconnected (U n) := hcomp ▸ isPreconnected_connectedComponentIn
    exact hc.subset_connectedComponentIn hz hUC

end BoundedWanderingDomains
