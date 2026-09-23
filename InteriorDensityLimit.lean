import OmittedPairCompactness
import DiscSchwarzPick

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- On a component of the complement of the limiting puncture barrier,
the increasing densities converge and dominate every disc metric pulled
back by a holomorphic map of that component to the unit disc. -/
theorem density_limit_lower (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ)))
    {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z))
    (hum : MapsTo u (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z) (ball 0 1)) :
    ∃ ell : ℝ, 0 < ell ∧ Tendsto (fun n => G.density (P n) z) atTop (𝓝 ell) ∧
      discDensity (u z) * ‖deriv u z‖ ≤ ell := by
  classical
  let A := closure (⋃ n, (↑(P n) : Set ℂ))
  let U := connectedComponentIn Aᶜ z
  have hU : IsOpen U := isClosed_closure.isOpen_compl.connectedComponentIn
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUA : U ⊆ Aᶜ := connectedComponentIn_subset _ _
  have hzP : ∀ n, z ∉ P n :=
    fun n hn => hz (subset_closure (mem_iUnion.mpr ⟨n, hn⟩))
  have hc : ∀ n, 2 ≤ (P n).card := fun n => Finset.one_lt_card.mpr
    ⟨a, hP (Nat.zero_le n) ha, b, hP (Nat.zero_le n) hb, hab⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hzU
  have hbd : ∀ n, G.density (P n) z ≤ 2 / δ := by
    intro n
    have hm : MapsTo (fun w : ℂ => z + w) (ball 0 δ) ((↑(P n) : Set ℂ)ᶜ) := by
      intro w hw hwp
      have hzw : z + w ∈ U := hδU (by simpa [dist_eq_norm] using hw)
      exact hUA hzw (subset_closure (mem_iUnion.mpr ⟨n, hwp⟩))
    simpa using G.schwarz_on_ball (hc n) hδ (by fun_prop) hm
  have hbounded : BddAbove (range (fun n => G.density (P n) z)) :=
    ⟨2 / δ, fun _ hx => by obtain ⟨n, rfl⟩ := hx; exact hbd n⟩
  have hmono : Monotone (fun n => G.density (P n) z) :=
    fun i j hij => G.density_mono (hc i) (hP hij) (hzP j)
  let ell := ⨆ n, G.density (P n) z
  have ht : Tendsto (fun n => G.density (P n) z) atTop (𝓝 ell) :=
    tendsto_atTop_ciSup hmono hbounded
  have hell : 0 < ell := (G.positive (P 0) (hc 0) z (hzP 0)).trans_le
    (le_ciSup hbounded 0)
  choose p hp hm h0 he using fun n => G.extremal_disc (P n) (hc n) z (hzP n)
  have hrbound : ∀ r : ℝ, 0 < r → r < 1 →
      (discDensity (u z) * ‖deriv u z‖) * r ≤ ell := by
    intro r hr hr1
    obtain ⟨M, hM⟩ := omitted_pair_bounded_subdisc hab hp
      (fun n w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) ha))
      (fun n w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) hb)) h0 hr.le hr1
    have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
    have hpR := fun n => (hp n).mono hsub
    obtain ⟨φ, g, hφ, hl, hgd⟩ := bounded_holomorphic_subsequence isOpen_ball hpR hM
    have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
    have hg0 : g 0 = z := by
      have h := hl.tendsto_at hzero
      have heq : (fun n => p (φ n) 0) = fun _ => z := funext (fun n => h0 (φ n))
      rw [heq] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    have hd := (hl.deriv (Eventually.of_forall (fun n => hpR (φ n))) isOpen_ball).tendsto_at hzero
    have heprod : ell * ‖deriv g 0‖ = 2 := by
      have h := (ht.comp hφ.tendsto_atTop).mul hd.norm
      have heq : (fun n => G.density (P (φ n)) z * ‖deriv (p (φ n)) 0‖) =
          fun _ => (2 : ℝ) := funext (fun n => he (φ n))
      simp only [Function.comp_apply] at h
      rw [heq] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    have hdpos : 0 < ‖deriv g 0‖ := by nlinarith [norm_nonneg (deriv g 0)]
    have hgnot : ¬∃ c, ∀ w ∈ ball (0 : ℂ) r, g w = c := by
      rintro ⟨c, hh⟩
      have hge : g =ᶠ[𝓝 0] fun _ => c := Filter.mem_of_superset (ball_mem_nhds _ hr) (fun w hw => hh w hw)
      have hder : deriv g 0 = 0 := by rw [hge.deriv_eq]; simp
      simp [hder] at hdpos
    have homit : ∀ c ∈ ⋃ n, (↑(P n) : Set ℂ),
        ∀ᶠ n in atTop, ∀ w ∈ ball (0 : ℂ) r, p (φ n) w ≠ c := by
      intro c hc
      obtain ⟨k, hk⟩ := mem_iUnion.mp hc
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k)] with n hn
      intro w hw heq
      exact hm (φ n) (hsub hw) (heq ▸ hP hn hk)
    have havoid := nonconstant_limit_avoids_closure isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected (fun n => hpR (φ n)) hl homit hgnot
    have hgU : MapsTo g (ball 0 r) U := by
      apply mapsTo_iff_image_subset.mpr
      exact ((convex_ball (0 : ℂ) r).isPreconnected.image g hgd.continuousOn).subset_connectedComponentIn
        ⟨0, hzero, hg0⟩ (fun w hw => fun hwA => disjoint_left.mp havoid hw hwA)
    have hs := disc_schwarz_centre hr (hu.comp hgd hgU) (hum.comp hgU)
    have hder : deriv (u ∘ g) 0 = deriv u z * deriv g 0 := by
      rw [deriv_comp 0 (hu.differentiableAt (hU.mem_nhds (hg0 ▸ hzU)))
        (hgd.differentiableAt (ball_mem_nhds _ hr)), hg0]
    rw [Function.comp_apply, hg0, hder, norm_mul] at hs
    have hh := (le_div_iff₀ hr).mp hs
    apply (mul_le_mul_iff_left₀ hdpos).mp
    calc
      (discDensity (u z) * ‖deriv u z‖ * r) * ‖deriv g 0‖ =
          (discDensity (u z) * (‖deriv u z‖ * ‖deriv g 0‖)) * r := by ring
      _ ≤ 2 := hh
      _ = ell * ‖deriv g 0‖ := heprod.symm
  refine ⟨ell, hell, ht, ?_⟩
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  let T := discDensity (u z) * ‖deriv u z‖
  have hT : 0 < T := hell.trans hlt
  have hratio : ell / T < 1 := (div_lt_one hT).mpr hlt
  have h := hrbound ((ell / T + 1) / 2) (by positivity) (by linarith)
  have he : T * ((ell / T + 1) / 2) = (ell + T) / 2 := by field_simp
  change T * ((ell / T + 1) / 2) ≤ ell at h
  rw [he] at h
  linarith

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.density_limit_lower
