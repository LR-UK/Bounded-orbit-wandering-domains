/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.BakerCoveringDiscs

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- Once the target covering discs embed, the local power-coordinate argument
makes the map itself injective on each fixed-radius source disc. -/
theorem eventually_injOn_shrinking_covering_discs
    {f : ℂ → ℂ} {K : Set ℂ} {U : ℕ → Set ℂ}
    {p : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {M : ℝ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ a ∈ K, ¬EventuallyConst f (𝓝 a))
    (hp : ∀ n, IsHolomorphicDiscCovering (p n) (U n))
    (hzK : ∀ n, z n ∈ K) (hp0 : ∀ n, p n 0 = z n)
    (hb : ∀ n x, x ∈ U n → ‖x‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hfm : ∀ n, MapsTo f (U n) (U (n+1)))
    (hfd : ∀ n, DifferentiableOn ℂ f (U n))
    (hnext : ∀ n, f (z n) = z (n+1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsc : ∀ᶠ n in atTop, IsSimplyConnected (p n '' ball 0 r)) :
    ∀ᶠ n in atTop, InjOn f (p n '' ball 0 r) := by
  classical
  have hloc : ∀ a : K, ∃ O : Set ℂ, IsOpen O ∧ (a : ℂ) ∈ O ∧
      ∃ d : ℕ, d ≠ 0 ∧ ∃ ψ : ℂ → ℂ, ContinuousOn ψ O ∧ InjOn ψ O ∧
      ∀ x ∈ O, f x = f a + ψ x ^ d :=
    fun a => exists_univalent_power_neighbourhood (hf a a.2) (hn a a.2)
  choose O hOo haO d hd ψ hψ hψi he using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hOo (by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, haO ⟨a, ha⟩⟩)
  let I := {a : K // a ∈ t}
  have hcover : K ⊆ ⋃ a : I, O a.val := by
    intro x hx
    obtain ⟨a, hat, ha⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, ha⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric hK
    (fun a : I => hOo a.val) hcover
  let E : Set ℂ := range (fun a : I => f a.val)
  have hE : E.Finite := finite_range _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_disjoint_finite hdis hE)
  have hscnext : ∀ᶠ n in atTop, IsSimplyConnected (p (n+1) '' ball 0 r) :=
    (Filter.tendsto_add_atTop_nat 1).eventually hsc
  filter_upwards [eventually_ge_atTop N, covering_discs_shrink hp hb hdis hr.le hr1 hδ,
    hscnext] with n hnN hshrink hsn
  let D := p n '' ball 0 r
  have hDU : D ⊆ U n := (image_mono (ball_subset_ball hr1.le)).trans (hp n).maps.image_subset
  have hnextU : p (n+1) '' ball 0 r ⊆ U (n+1) :=
    (image_mono (ball_subset_ball hr1.le)).trans (hp (n+1)).maps.image_subset
  obtain ⟨a, ha⟩ := hδcover (z n) (hzK n)
  have hDO : D ⊆ O a.val := by
    intro x hx
    apply ha
    rw [← hp0 n]
    exact hshrink x (image_mono ball_subset_closedBall hx)
  apply injOn_of_power_coordinate (hd a.val)
    ((convex_ball (0 : ℂ) r).isPreconnected.image (p n)
      ((hp n).holo.continuousOn.mono (ball_subset_ball hr1.le)))
    ((hp (n+1)).image_isOpen isOpen_ball (ball_subset_ball hr1.le)) hsn
  · intro hx
    exact disjoint_left.mp (hN (n+1) (by omega)) (hnextU hx) ⟨a, rfl⟩
  · exact (hfd n).continuousOn.mono hDU
  · exact (hψ a.val).mono hDO
  · exact (hψi a.val).mono hDO
  · exact mapsTo_covering_disc (hp n) (hp (n+1)) (hfd n) (hfm n)
      (by rw [hp0, hp0, hnext]) hr1
  · exact fun x hx => he a.val x (hDO hx)

end AreaDeficit
