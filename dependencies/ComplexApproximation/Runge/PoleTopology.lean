import Runge.PoleShift
import Runge.UniformClosure
import Mathlib.Topology.Connected.Clopen

open Polynomial Set
open scoped BigOperators Topology

namespace Runge

noncomputable def polynomialMap (K : Set ℂ) (p : ℂ[X]) : C(K, ℂ) :=
  ⟨fun z => p.eval (z : ℂ), p.continuous.comp continuous_subtype_val⟩

@[simp] theorem polynomialMap_apply (K : Set ℂ) (p : ℂ[X]) (z : K) :
    polynomialMap K p z = p.eval (z : ℂ) := rfl

noncomputable def poleKernel (K : Set ℂ) (a : ℂ) (ha : a ∉ K) : C(K, ℂ) :=
  ⟨fun z => ((z : ℂ)-a)⁻¹, (continuous_subtype_val.sub continuous_const).inv₀
    (fun z => sub_ne_zero.mpr (fun h => ha (by
      change (z : ℂ) = a at h
      exact h ▸ z.property)))⟩

@[simp] theorem poleKernel_apply (K : Set ℂ) (a : ℂ) (ha : a ∉ K) (z : K) :
    poleKernel K a ha z = ((z : ℂ)-a)⁻¹ := rfl

theorem continuous_poleKernel (K : Set ℂ) :
    Continuous (fun a : ↥(Kᶜ) => poleKernel K a a.property) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.inv₀
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))
  intro p
  apply sub_ne_zero.mpr
  intro h
  change (p.2 : ℂ) = (p.1 : ℂ) at h
  exact p.1.property (h ▸ p.2.property)

noncomputable def polePartialMap (K : Set ℂ) (a b : ℂ) (hb : b ∉ K) (N : ℕ) : C(K, ℂ) :=
  poleKernel K b hb * ∑ n ∈ Finset.range N,
    (algebraMap ℂ C(K, ℂ) (a-b) * poleKernel K b hb)^n

@[simp] theorem polePartialMap_apply (K : Set ℂ) (a b : ℂ) (hb : b ∉ K) (N : ℕ) (z : K) :
    polePartialMap K a b hb N z = polePartial a b N z := by
  simp [polePartialMap, polePartial, div_eq_mul_inv]

theorem polePartialMap_mem (K : Set ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (a b : ℂ) (hb : b ∉ K) (hS : poleKernel K b hb ∈ S) (N : ℕ) :
    polePartialMap K a b hb N ∈ S := by
  apply S.mul_mem hS
  apply S.sum_mem
  intro n _
  exact S.pow_mem (S.mul_mem (S.algebraMap_mem _) hS) n

/-- A closed algebra that can approximate the old pole can approximate any pole
within its clearance from `K`. -/
theorem poleKernel_mem_of_near (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ)))
    (a b : ℂ) (ha : a ∉ K) (hb : b ∉ K) (d : ℝ) (hd : 0 < d)
    (hmove : ‖a-b‖ < d) (hclear : ∀ z ∈ K, d ≤ ‖z-b‖)
    (hbS : poleKernel K b hb ∈ S) : poleKernel K a ha ∈ S := by
  change poleKernel K a ha ∈ (S : Set C(K, ℂ))
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, _, hN⟩ := pole_shift_uniform_approximation a b d hd hmove hclear ε hε
  refine ⟨polePartialMap K a b hb N, polePartialMap_mem K S a b hb hbS N, ?_⟩
  rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
  intro z
  simpa only [ContinuousMap.sub_apply, poleKernel_apply, polePartialMap_apply] using hN z z.property

/-- The poles whose kernels lie in a given algebra, as a subset of `Kᶜ`. -/
def goodPoles (K : Set ℂ) (S : Subalgebra ℂ C(K, ℂ)) : Set ↥(Kᶜ) :=
  {a | poleKernel K a a.property ∈ S}

theorem isClosed_goodPoles (K : Set ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) : IsClosed (goodPoles K S) :=
  hS.preimage (continuous_poleKernel K)

theorem isOpen_goodPoles (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ))) :
    IsOpen (goodPoles K S) := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  rw [Metric.isOpen_iff]
  intro a ha
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl a a.property
  refine ⟨d, hd, ?_⟩
  intro b hb
  apply poleKernel_mem_of_near K S hS b a b.property a.property d hd
  · simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hb
  · intro z hz
    apply le_of_not_gt
    intro h
    have hm : z ∈ Metric.ball (a : ℂ) d := by simpa only [Metric.mem_ball, dist_eq_norm] using h
    exact hball hm hz
  · exact ha

theorem isClopen_goodPoles (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ))) :
    IsClopen (goodPoles K S) :=
  ⟨isClosed_goodPoles K S hS, isOpen_goodPoles K S hS⟩

end Runge
