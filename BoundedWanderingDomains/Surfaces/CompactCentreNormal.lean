/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.NormalFamilies
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.Surfaces.KernelNormal

/-! # Normal lifts of holomorphic discs with compact centre values -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Holomorphic discs whose centre values remain in a compact subset of a
disc-covered surface have a subsequence with normalised lifts converging
locally uniformly inside the covering disc. -/
theorem DiscCover.exists_normal_lift_subsequence (p : DiscCover M)
    {K : Set M} (hK : IsCompact K) (F : ℕ → unitDisc → M)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K) :
    ∃ (φ : ℕ → ℕ) (H : ℕ → unitDisc → unitDisc) (g : ℂ → ℂ)
      (w : unitDisc),
      StrictMono φ ∧
      (∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H n)) ∧
      (∀ n, p.projection ∘ H n = F (φ n)) ∧
      TendstoLocallyUniformlyOn
        (fun n => planeExtension (fun z => (H n z : ℂ))) g atTop (ball 0 1) ∧
      g 0 = (w : ℂ) ∧ MapsTo g (ball 0 1) (ball 0 1) := by
  obtain ⟨B, hB, hKB⟩ := p.compact_lift_set hK
  choose b hbB hbp using fun n => hKB (hcentre n)
  obtain ⟨w, hwB, φ₀, hφ₀, hwlim⟩ := hB.tendsto_subseq hbB
  letI : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  letI : LocallyPathConnectedSpace unitDisc :=
    ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  choose H₀ hH₀zero hH₀fac hH₀diff using fun n =>
    exists_holomorphic_lift p.holomorphic p.covering (hF (φ₀ n))
      discZero (b (φ₀ n)) (hbp (φ₀ n))
  have hdiff : ∀ n, DifferentiableOn ℂ
      (planeExtension (fun z => (H₀ n z : ℂ))) (ball 0 1) := fun n =>
    planeExtension_differentiableOn
      ((mdifferentiable_subtype_val unitDisc).comp (hH₀diff n))
  have hbound : ∀ n z, z ∈ ball (0 : ℂ) 1 →
      ‖planeExtension (fun v => (H₀ n v : ℂ)) z‖ ≤ 1 := by
    intro n z hz
    rw [planeExtension_coe _ ⟨z, hz⟩]
    exact (mem_ball_zero_iff.mp (H₀ n ⟨z, hz⟩).property).le
  obtain ⟨ψ, g, hψ, hlim, hgd⟩ :=
    AreaDeficit.bounded_holomorphic_subsequence isOpen_ball hdiff hbound
  have hg0 : g 0 = (w : ℂ) := by
    have hlocal := hlim.tendsto_at (show (0 : ℂ) ∈ ball 0 1 by simp)
    have hvalues : (fun n => planeExtension (fun z => (H₀ (ψ n) z : ℂ)) 0) =
        fun n => (b (φ₀ (ψ n)) : ℂ) := by
      funext n
      calc
        planeExtension (fun z => (H₀ (ψ n) z : ℂ)) 0 =
            (H₀ (ψ n) discZero : ℂ) := by
              simpa only [show (discZero : ℂ) = 0 from rfl] using
                planeExtension_coe (fun z => (H₀ (ψ n) z : ℂ)) discZero
        _ = (b (φ₀ (ψ n)) : ℂ) := congrArg Subtype.val (hH₀zero (ψ n))
    rw [hvalues] at hlocal
    have htow : Tendsto (fun n => (b (φ₀ (ψ n)) : ℂ)) atTop (𝓝 (w : ℂ)) :=
      (continuous_subtype_val.tendsto w).comp (hwlim.comp hψ.tendsto_atTop)
    exact (tendsto_nhds_unique htow hlocal).symm
  let φ := φ₀ ∘ ψ
  let H := H₀ ∘ ψ
  refine ⟨φ, H, g, w, hφ₀.comp hψ, fun n => hH₀diff (ψ n), ?_, hlim,
    hg0, normal_lift_limit_maps_disc H₀ w hlim hgd hg0⟩
  intro n
  exact hH₀fac (ψ n)

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.DiscCover.exists_normal_lift_subsequence
