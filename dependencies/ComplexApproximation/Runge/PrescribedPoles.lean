import Runge.RationalGeneration
import Runge.PolesAtInfinity
import Runge.RationalApproximation

open Polynomial Set Function Bornology

namespace Runge

/-- The allowed pole set meets every bounded connected component of the
complement of the compact set. The unbounded component needs no finite pole. -/
def MeetsBoundedComplementComponents (K P : Set ℂ) : Prop :=
  ∀ a ∉ K, IsBounded (connectedComponentIn Kᶜ a) →
    (connectedComponentIn Kᶜ a ∩ P).Nonempty

theorem poleKernel_mem_of_same_component (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ)))
    (a b : ℂ) (ha : a ∉ K) (hb : b ∉ K)
    (hcomp : b ∈ connectedComponentIn Kᶜ a) (hbS : poleKernel K b hb ∈ S) :
    poleKernel K a ha ∈ S := by
  have hcomp' : (⟨b, hb⟩ : ↥(Kᶜ)) ∈ connectedComponent (⟨a, ha⟩ : ↥(Kᶜ)) := by
    rw [connectedComponentIn_eq_image ha] at hcomp
    obtain ⟨b', hb', he⟩ := hcomp
    have he' : b' = (⟨b, hb⟩ : ↥(Kᶜ)) := Subtype.ext he
    exact he' ▸ hb'
  have hsub := isPreconnected_connectedComponent.subset_isClopen
    (isClopen_goodPoles K S hS) ⟨⟨b, hb⟩, hcomp', hbS⟩
  exact hsub (mem_connectedComponent (x := (⟨a, ha⟩ : ↥(Kᶜ))))

theorem all_poleKernels_mem_poleClosure (K P : Set ℂ) [CompactSpace K]
    (hP : MeetsBoundedComplementComponents K P) (a : ℂ) (ha : a ∉ K) :
    poleKernel K a ha ∈ poleClosure K P := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
  by_cases hb : IsBounded (connectedComponentIn Kᶜ a)
  · obtain ⟨b, hbc, hbP⟩ := hP a ha hb
    have hbK : b ∉ K := connectedComponentIn_subset Kᶜ a hbc
    exact poleKernel_mem_of_same_component K (poleClosure K P)
      (poleAlgebra K P).isClosed_topologicalClosure a b ha hbK hbc
      ((poleAlgebra K P).le_topologicalClosure (poleKernel_mem_poleAlgebra K P b hbK hbP))
  · have hfar : ∃ b ∈ connectedComponentIn Kᶜ a, r < ‖b‖ := by
      by_contra! hn
      exact hb (isBounded_iff_forall_norm_le.mpr ⟨r, hn⟩)
    obtain ⟨b, hbc, hbr⟩ := hfar
    have hbK : b ∉ K := connectedComponentIn_subset Kᶜ a hbc
    apply poleKernel_mem_of_same_component K (poleClosure K P)
      (poleAlgebra K P).isClosed_topologicalClosure a b ha hbK hbc
    exact poleKernel_mem_of_large_norm K (poleClosure K P)
      (poleAlgebra K P).isClosed_topologicalClosure
      (fun p => (poleAlgebra K P).le_topologicalClosure (polynomialMap_mem_poleAlgebra K P p))
      r hr.le hKr b hbK hbr

theorem rationalClosure_le_poleClosure (K P : Set ℂ) [CompactSpace K]
    (hP : MeetsBoundedComplementComponents K P) : rationalClosure K ≤ poleClosure K P :=
  rationalClosure_le_of_polynomials_and_kernels K (poleClosure K P)
    (poleAlgebra K P).isClosed_topologicalClosure
    (fun p => (poleAlgebra K P).le_topologicalClosure (polynomialMap_mem_poleAlgebra K P p))
    (all_poleKernels_mem_poleClosure K P hP)

theorem analytic_mem_poleClosure (K P : Set ℂ) [CompactSpace K]
    (hP : MeetsBoundedComplementComponents K P) (U : Set ℂ)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    (⟨fun z : K => f z, (hf.continuousOn.mono hKU).domRestrict⟩ : C(K, ℂ))
      ∈ poleClosure K P := by
  apply rationalClosure_le_poleClosure K P hP
  rw [mem_rationalClosure_iff]
  intro ε hε
  obtain ⟨p, q, hq, hpq⟩ := rational_approximation K
    (isCompact_iff_compactSpace.mpr inferInstance) U hU hKU f hf ε hε
  exact ⟨p, q, fun z => hq z z.property, fun z => hpq z z.property⟩

/-- Runge approximation with prescribed poles. Every zero of the chosen
denominator lies in `P`, and the denominator is nonzero everywhere on `K`. -/
theorem prescribed_poles_approximation (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨p, q, hq0, hq, hqP, hpq⟩ := (mem_poleClosure_iff K P _).mp
    (analytic_mem_poleClosure K P hP U hU hKU f hf) ε hε
  exact ⟨p, q, hq0, fun z hz => hq ⟨z, hz⟩, hqP, fun z hz => hpq ⟨z, hz⟩⟩

theorem meets_empty_of_connected_complement (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) : MeetsBoundedComplementComponents K ∅ := by
  intro a ha hb
  rw [hconn.isPreconnected.connectedComponentIn ha] at hb
  have huniv : IsBounded (Set.univ : Set ℂ) := by simpa using hK.isBounded.union hb
  exact False.elim (NormedSpace.unbounded_univ ℝ ℂ huniv)

/-- The polynomial form of Runge's theorem for a compact set with connected
complement. -/
theorem polynomial_approximation (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨p, hp⟩ := (mem_poleClosure_empty_iff K _).mp
    (analytic_mem_poleClosure K ∅ (meets_empty_of_connected_complement K hK hconn)
      U hU hKU f hf) ε hε
  exact ⟨p, fun z hz => hp ⟨z, hz⟩⟩

end Runge
