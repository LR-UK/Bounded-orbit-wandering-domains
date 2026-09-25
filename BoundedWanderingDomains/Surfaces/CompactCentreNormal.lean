/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.NormalFamilies
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.Surfaces.KernelNormal
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.UniformSpace.Uniformizable

/-! # Normal lifts of holomorphic discs with compact centre values -/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

/-- Local uniform convergence into a subtype can be checked after composing
with its uniformly inducing inclusion. -/
theorem tendstoLocallyUniformly_subtype_of_val
    {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
    {s : Set β} {p : Filter ι} {F : ι → α → s} {f : α → s}
    (h : TendstoLocallyUniformly
      (fun n x => (F n x : β)) (fun x => (f x : β)) p) :
    TendstoLocallyUniformly F f p := by
  intro u hu x
  rw [uniformity_subtype] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  obtain ⟨t, ht, hevent⟩ := h v hv x
  refine ⟨t, ht, hevent.mono ?_⟩
  intro n hn y hy
  exact hvu (hn y hy)

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
      (w : unitDisc) (B : Set unitDisc),
      StrictMono φ ∧
      IsCompact B ∧ (∀ n, H n discZero ∈ B) ∧
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
  refine ⟨φ, H, g, w, B, hφ₀.comp hψ, hB, ?_,
    fun n => hH₀diff (ψ n), ?_, hlim,
    hg0, normal_lift_limit_maps_disc H₀ w hlim hgd hg0⟩
  · intro n
    change H₀ (ψ n) discZero ∈ B
    rw [hH₀zero]
    exact hbB (φ₀ (ψ n))
  intro n
  exact hH₀fac (ψ n)

/-- Descending the normal lifts through the universal covering gives the
ordinary Montel theorem for surface-valued holomorphic discs whose centre
values remain in a compact set. -/
theorem DiscCover.exists_normal_disc_subsequence [T2Space M]
    [LocallyCompactSpace M] (p : DiscCover M)
    {K : Set M} (hK : IsCompact K) (F : ℕ → unitDisc → M)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K) :
    letI : UniformSpace (OnePoint M) := uniformSpaceOfCompactR1
    ∃ (φ : ℕ → ℕ) (G : unitDisc → OnePoint M), StrictMono φ ∧
      TendstoLocallyUniformly
        (fun n z => ((F (φ n) z : M) : OnePoint M)) G atTop := by
  letI : UniformSpace (OnePoint M) := uniformSpaceOfCompactR1
  obtain ⟨φ, H, g, w, B, hφ, hB, hHcentre, hHdiff, hfac, hlim, hg0, hgmap⟩ :=
    p.exists_normal_lift_subsequence hK F hF hcentre
  let G₀ : unitDisc → unitDisc := fun z => ⟨g (z : ℂ), hgmap z.property⟩
  have hliftVal : TendstoLocallyUniformly
      (fun n z => (H n z : ℂ)) (fun z => (G₀ z : ℂ)) atTop := by
    intro u hu z
    obtain ⟨t, ht, hevent⟩ := hlim u hu (z : ℂ) z.property
    have ht' : t ∈ 𝓝 (z : ℂ) := by
      rwa [isOpen_ball.nhdsWithin_eq z.property] at ht
    refine ⟨Subtype.val ⁻¹' t, continuous_subtype_val.continuousAt ht', ?_⟩
    filter_upwards [hevent] with n hn
    intro y hy
    simpa only [G₀, planeExtension_coe] using hn (y : ℂ) hy
  have hlift : TendstoLocallyUniformly H G₀ atTop :=
    tendstoLocallyUniformly_subtype_of_val hliftVal
  let q : unitDisc → OnePoint M := fun z => (p.projection z : OnePoint M)
  have hqcont : Continuous q := OnePoint.continuous_coe.comp p.continuous
  have hdesc : TendstoLocallyUniformly (q ∘ H ·) (q ∘ G₀) atTop := by
    intro u hu x
    have hxnorm : ‖(x : ℂ)‖ < 1 := mem_ball_zero_iff.mp x.property
    let r : ℝ := (‖(x : ℂ)‖ + 1) / 2
    have hxr : ‖(x : ℂ)‖ < r := by dsimp [r]; linarith
    have hr : r < 1 := by dsimp [r]; linarith
    obtain ⟨C, hC, hcontrol⟩ :=
      unitDisc_maps_compact_closed_ball hB hr
    let S : Set unitDisc := {z | ‖(z : ℂ)‖ < r}
    have hSopen : IsOpen S := by
      have hSeq : S = Subtype.val ⁻¹' ball (0 : ℂ) r := by
        ext z
        simp only [S, mem_setOf_eq, mem_preimage, mem_ball_zero_iff]
      rw [hSeq]
      exact isOpen_ball.preimage continuous_subtype_val
    have hxS : x ∈ S := hxr
    have hHS : ∀ n, MapsTo (H n) S C := by
      intro n z hz
      exact hcontrol (H n) (hHdiff n) (hHcentre n) z (le_of_lt hz)
    have hG₀S : MapsTo G₀ S C := by
      intro z hz
      apply hC.isClosed.mem_of_tendsto
        ((tendstoLocallyUniformlyOn_univ.mpr hlift).tendsto_at (mem_univ z))
      exact Eventually.of_forall (fun n => hHS n hz)
    have hqu : UniformContinuousOn q C :=
      hC.uniformContinuousOn_of_continuous hqcont.continuousOn
    have hc := hqu.comp_tendstoLocallyUniformlyOn
      (show TendstoLocallyUniformlyOn H G₀ atTop S from
        (tendstoLocallyUniformlyOn_univ.mpr hlift).mono (subset_univ S))
      hG₀S (Eventually.of_forall hHS)
    obtain ⟨t, ht, hevent⟩ := hc u hu x hxS
    rw [hSopen.nhdsWithin_eq hxS] at ht
    exact ⟨t, ht, hevent⟩
  refine ⟨φ, q ∘ G₀, hφ, ?_⟩
  convert hdesc using 1
  funext n z
  change (F (φ n) z : OnePoint M) = (p.projection (H n z) : OnePoint M)
  exact congrArg (fun y : M => (y : OnePoint M)) (congrFun (hfac n) z).symm

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.DiscCover.exists_normal_lift_subsequence
