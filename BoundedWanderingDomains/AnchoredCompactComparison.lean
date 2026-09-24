/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.UnconditionalPointRemoval
import FunctionTheory.Conformal.SchottkyConfinement

/-!
# Uniform metric comparison away from a compact deleted set

A family of normalised disc maps omitting two fixed values is uniformly
continuous near the origin when its centres range over a fixed compact set.
This supplies a radius independent of all additional punctures.
-/

open Set Metric Function
open scoped Topology

namespace AreaDeficit

/-- Source discs of a uniform radius stay away from a fixed disjoint
compact set. The radius is independent of the holomorphic map. -/
theorem exists_uniform_disc_radius_avoiding_compact
    {C K : Set ℂ} (hC : IsCompact C) (hK : IsCompact K)
    (hCK : Disjoint C K) {a b : ℂ} (hab : a ≠ b) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ p : ℂ → ℂ,
      AnalyticOnNhd ℂ p (ball (0 : ℂ) 1) →
      (∀ w ∈ ball (0 : ℂ) 1, p w ≠ a) →
      (∀ w ∈ ball (0 : ℂ) 1, p w ≠ b) →
      p 0 ∈ C → MapsTo p (ball (0 : ℂ) r) Kᶜ := by
  have hCsub : C ⊆ Kᶜ := by
    intro z hzC hzK
    exact Set.disjoint_left.mp hCK hzC hzK
  obtain ⟨δ, hδ, hδK⟩ := hC.exists_cthickening_subset_open
    hK.isClosed.isOpen_compl hCsub
  obtain ⟨r, hr, hr1, H⟩ :=
    FunctionTheory.exists_uniform_radius_of_compact_centres_omit_pair hC hab hδ
  refine ⟨r, hr, hr1, ?_⟩
  intro p hp ha hb hpC w hw
  have hwp := H p hp ha hb hpC hw
  exact hδK ((closedBall_subset_cthickening hpC δ) (ball_subset_closedBall hwp))

/-- The logarithmic density increase on a compact set separated from the
new punctures is bounded independently of both finite puncture sets. The
two fixed anchors guarantee that every covering map omits the same values. -/
theorem FinitePunctureMetricInput.uniform_log_gain_away_from_compact
    (G : FinitePunctureMetricInput)
    {C K : Set ℂ} (hC : IsCompact C) (hK : IsCompact K)
    (hCK : Disjoint C K) {a b : ℂ} (hab : a ≠ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (P Q : Finset ℂ) (z : ℂ),
      a ∈ P → b ∈ P → (↑Q : Set ℂ) ⊆ K → z ∈ C → z ∉ P ∪ Q →
      max (Real.log (G.density (P ∪ Q) z) - Real.log (G.density P z)) 0 ≤ M := by
  obtain ⟨r, hr, hr1, H⟩ :=
    exists_uniform_disc_radius_avoiding_compact hC hK hCK hab
  refine ⟨max (Real.log (1 / r)) 0, le_max_right _ _, ?_⟩
  intro P Q z ha hb hQ hzC hz
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hPQ : 2 ≤ (P ∪ Q).card :=
    hP.trans (Finset.card_le_card Finset.subset_union_left)
  have hzP : z ∉ P := fun h => hz (Finset.mem_union_left Q h)
  obtain ⟨p, hp, hm, hp0, he⟩ := G.extremal_disc P hP z hzP
  have havoid : MapsTo p (ball (0 : ℂ) r) Kᶜ := by
    apply H p (hp.analyticOnNhd isOpen_ball)
    · intro w hw heq
      exact hm hw (heq ▸ ha)
    · intro w hw heq
      exact hm hw (heq ▸ hb)
    · exact hp0 ▸ hzC
  have hsmall : ball (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := ball_subset_ball hr1.le
  have hmap : MapsTo p (ball (0 : ℂ) r) ((↑(P ∪ Q) : Set ℂ)ᶜ) := by
    intro w hw hmem
    rcases Finset.mem_union.mp hmem with hwP | hwQ
    · exact hm (hsmall hw) hwP
    · exact havoid hw (hQ hwQ)
  have hs := G.schwarz_on_ball hPQ hr (hp.mono hsmall) hmap
  rw [hp0] at hs
  have hnorm : 0 < ‖deriv p 0‖ := by
    have hne : ‖deriv p 0‖ ≠ 0 := by
      intro h
      rw [h, mul_zero] at he
      norm_num at he
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hscaled : G.density (P ∪ Q) z * r ≤ G.density P z := by
    apply (mul_le_mul_iff_left₀ hnorm).mp
    calc
      (G.density (P ∪ Q) z * r) * ‖deriv p 0‖ =
        (G.density (P ∪ Q) z * ‖deriv p 0‖) * r := by ring
      _ ≤ 2 := (le_div_iff₀ hr).mp hs
      _ = G.density P z * ‖deriv p 0‖ := he.symm
  have hpos : 0 < G.density P z := G.positive P hP z hzP
  have hposQ : 0 < G.density (P ∪ Q) z := G.positive (P ∪ Q) hPQ z hz
  have hratio : G.density (P ∪ Q) z / G.density P z ≤ 1 / r := by
    apply (div_le_div_iff₀ hpos hr).mpr
    simpa only [one_mul] using hscaled
  have hlog := Real.log_le_log (div_pos hposQ hpos) hratio
  rw [Real.log_div (ne_of_gt hposQ) (ne_of_gt hpos)] at hlog
  exact max_le_max hlog le_rfl

end AreaDeficit

#print axioms AreaDeficit.exists_uniform_disc_radius_avoiding_compact
#print axioms AreaDeficit.FinitePunctureMetricInput.uniform_log_gain_away_from_compact
