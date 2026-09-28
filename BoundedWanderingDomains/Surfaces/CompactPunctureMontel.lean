/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteEndNormal

/-! # Normality for discs omitting hyperbolising finite anchors -/

open Set Function Filter Topology
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X]
  [FirstCountableTopology X]

theorem DiscCover.exists_normal_disc_subsequence_finite_complement
    (E : Finset X) (O : TopologicalSpace.Opens X) (hO : ∀ x, x ∈ O ↔ x ∉ E)
    (p : DiscCover O) (F : ℕ → unitDisc → O)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n)) :
    letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
    ∃ (φ : ℕ → ℕ) (G : unitDisc → OnePoint X), StrictMono φ ∧
      TendstoLocallyUniformly (fun n z => ((F (φ n) z : X) : OnePoint X)) G atTop := by
  classical
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_univ : IsCompact (univ : Set X)).tendsto_subseq
    (fun n => show (F n discZero : X) ∈ univ from mem_univ _)
  by_cases haE : a ∈ E
  · refine ⟨φ, (fun _ => (a : OnePoint X)), hφ, ?_⟩
    intro u hu z
    obtain ⟨r, hzr, hr1⟩ := exists_between (mem_ball_zero_iff.mp z.property)
    have hr : 0 < r := (norm_nonneg _).trans_lt hzr
    have hN : {x : X | ((a : OnePoint X), (x : OnePoint X)) ∈ u} ∈ 𝓝 a :=
      OnePoint.continuous_coe.continuousAt (mem_nhds_left _ hu)
    have hh := p.eventually_maps_radius_into_end_neighborhood E O hO (fun n => F (φ n))
      (fun n => hF (φ n)) haE hlim hN hr hr1
    refine ⟨{w : unitDisc | ‖(w : ℂ)‖ < r},
      (isOpen_lt continuous_subtype_val.norm continuous_const).mem_nhds hzr, hh⟩
  · have haO := (hO a).mpr haE
    obtain ⟨L, hL, haL, hLO⟩ := exists_compact_subset O.isOpen haO
    have hLc : IsCompact (Subtype.val ⁻¹' L : Set O) := by
      rw [IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
      convert hL using 1
      exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hLO hx⟩, rfl⟩)
    have hh : ∀ᶠ n in atTop, (F (φ n) discZero : X) ∈ L :=
      hlim.eventually (mem_interior_iff_mem_nhds.mp haL)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hh
    obtain ⟨ψ, G, hψ, hconv⟩ := p.exists_normal_disc_subsequence_ambient O hLc
      (fun n => F (φ (n + N))) (fun n => hF (φ (n + N)))
      (fun n => hN (n + N) (by omega))
    exact ⟨(fun n => φ (ψ n + N)), G,
      hφ.comp (by intro n m hnm; exact Nat.add_lt_add_right (hψ hnm) N), hconv⟩

end AreaDeficit.Surfaces
