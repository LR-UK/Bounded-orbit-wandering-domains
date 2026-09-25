/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.KernelDomains
import BoundedWanderingDomains.Surfaces.KernelNormal

/-! # Kernel convergence of intrinsic densities in a covered ambient surface

Decreasing covered domains containing a fixed component and omitting an
increasing dense family of finite punctures converge to its intrinsic
Poincaré density. The proof derives convergence from normal families,
Hurwitz and Schwarz–Pick; convergence is not an input assumption.
-/

open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem density_tendsto_of_dense_punctures (p : DiscCover M)
    (V : ℕ → TopologicalSpace.Opens M) (hV : Antitone V)
    (q : ∀ n, DiscCover (V n))
    {U : TopologicalSpace.Opens M} (r : DiscCover U) (x : U)
    (hUV : ∀ n, U ≤ V n)
    (P : ℕ → Finset M) (hP : Monotone P) {A : Set M}
    (hA : closure (⋃ n, (↑(P n) : Set M)) = A)
    (homit : ∀ n y, y ∈ V n → y ∉ (↑(P n) : Set M))
    (hU : (U : Set M) = connectedComponentIn Aᶜ (x : M))
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hx : (x : M) ∈ c.source) :
    Tendsto (fun n => (q n).density
      (c.subtypeRestr ⟨⟨(x : M), hUV n x.property⟩⟩)
      ⟨(x : M), hUV n x.property⟩) atTop
      (𝓝 (r.density (c.subtypeRestr ⟨x⟩) x)) := by
  classical
  let xn : ∀ n, V n := fun n => ⟨(x : M), hUV n x.property⟩
  let cn := fun n => c.subtypeRestr (show Nonempty (V n) from ⟨xn n⟩)
  let d := c.subtypeRestr (show Nonempty U from ⟨x⟩)
  let a : ℕ → ℝ := fun n => (q n).density (cn n) (xn n)
  let B := r.density d x
  have hcn : ∀ n, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (cn n) (cn n).source :=
    fun n => mdifferentiableOn_subtypeRestr ⟨xn n⟩ hc
  have hxn : ∀ n, xn n ∈ (cn n).source := fun n => by
    simpa only [cn, xn, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source :=
    mdifferentiableOn_subtypeRestr ⟨x⟩ hc
  have hxd : x ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hbd : ∀ n, a n ≤ B := fun n =>
    density_nested_subdomains (hUV n) (q n) r ⟨xn n⟩ ⟨x⟩ hc hx
  have hmono : Monotone a := by
    intro i j hij
    exact density_nested_subdomains (hV hij) (q i) (q j)
      ⟨xn i⟩ ⟨xn j⟩ hc (x := xn j) hx
  have hbounded : BddAbove (range a) := ⟨B, by
    rintro _ ⟨n,rfl⟩
    exact hbd n⟩
  let ell : ℝ := ⨆ n, a n
  have ht : Tendsto a atTop (𝓝 ell) := tendsto_atTop_ciSup hmono hbounded
  have hell : 0 < ell := ((q 0).density_pos (hcn 0) (hxn 0)).trans_le
    (le_ciSup hbounded 0)
  have hellB : ell ≤ B := ciSup_le hbd
  obtain ⟨w,hw⟩ := p.surjective (x : M)
  choose G hG hG0 hscale H hH hH0 hfac using fun n =>
    p.density_extremal_ambient_lift (q n) (hcn n) (hxn n) w hw
  have hscaleH : ∀ n, a n *
      (‖deriv (planeExtension (c ∘ p.projection)) w‖ *
        ‖deriv (planeExtension (fun v => (H n v : ℂ))) 0‖) = 2 := by
    intro n
    exact p.extremal_ambient_lift_derivative (q n) hc hx w hw
      (G n) (hG n) (hG0 n) (hscale n) (H n) (hH n) (hH0 n) (hfac n)
  obtain ⟨φ,g,hφ,hl,hgd,hg0⟩ := ambient_disc_lifts_normal_at_centre
    H hH w hH0 (by norm_num : (0 : ℝ) < 1) le_rfl
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have hdiff : ∀ n, DifferentiableOn ℂ
      (planeExtension (fun v => (H (φ n) v : ℂ))) (ball 0 1) :=
    fun n => planeExtension_differentiableOn
      ((mdifferentiable_subtype_val unitDisc).comp (hH (φ n)))
  have hderlim := (hl.deriv (Eventually.of_forall hdiff) isOpen_ball).tendsto_at hzero
  let C := ‖deriv (planeExtension (c ∘ p.projection)) w‖
  have hprod : ell * (C * ‖deriv g 0‖) = 2 := by
    have hp := (ht.comp hφ.tendsto_atTop).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hderlim.norm)
    have he : (fun n => a (φ n) *
        (C * ‖deriv (planeExtension (fun v => (H (φ n) v : ℂ))) 0‖)) =
        fun _ : ℕ => (2 : ℝ) := funext (fun n => hscaleH (φ n))
    change Tendsto (fun n => a (φ n) *
      (C * ‖deriv (planeExtension (fun v => (H (φ n) v : ℂ))) 0‖))
      atTop (𝓝 (ell * (C * ‖deriv g 0‖))) at hp
    rw [he] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  have hgder : deriv g 0 ≠ 0 := by
    intro he
    rw [he, norm_zero, mul_zero, mul_zero] at hprod
    norm_num at hprod
  have hgn := normal_limit_nonconstant (by norm_num : (0 : ℝ) < 1) hgder
  have hgm := normal_lift_limit_maps_disc H w hl hgd hg0
  let Hlim : unitDisc → unitDisc := fun z => ⟨g z, hgm z.property⟩
  have hHlim : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Hlim := by
    apply (mdifferentiable_subtypeVal_comp_iff unitDisc Hlim).mp
    intro z
    apply mdifferentiableAt_subtype_iff.mpr
    exact (hgd.differentiableAt (isOpen_ball.mem_nhds z.property)).mdifferentiableAt
  have hHlim0 : Hlim discZero = w := Subtype.ext hg0
  have havoidH : ∀ n v, p.projection (H n v) ∉ (↑(P n) : Set M) := by
    intro n v
    have he : p.projection (H n v) = (G n v : M) := congrFun (hfac n) v
    rw [he]
    exact homit n _ (G n v).property
  have havoid : ∀ v : unitDisc, p.projection (Hlim v) ∉ A := by
    intro v
    exact p.ambient_hurwitz_avoidance P hP hA H hH havoidH
      (by norm_num : (0 : ℝ) < 1) le_rfl hφ hl hgn v.property (hgm v.property)
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  have hrange : range (p.projection ∘ Hlim) ⊆ (U : Set M) := by
    rw [hU]
    apply (isPreconnected_range (p.continuous.comp hHlim.continuous)).subset_connectedComponentIn
    · exact ⟨discZero, by simp only [comp_apply, hHlim0, hw]⟩
    · rintro _ ⟨v,rfl⟩
      exact havoid v
  let F : unitDisc → U := fun v => ⟨p.projection (Hlim v), hrange (mem_range_self v)⟩
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    (mdifferentiable_subtypeVal_comp_iff U F).mp (p.holomorphic.comp hHlim)
  have hF0 : F discZero = x := Subtype.ext (by
    change p.projection (Hlim discZero) = (x : M)
    rw [hHlim0, hw])
  have hs := r.density_schwarz_disc hF hd discZero (hF0.symm ▸ hxd)
  have hpcoord := ((hc _ (hw ▸ hx)).mdifferentiableAt
    (c.open_source.mem_nhds (hw ▸ hx))).comp w (p.holomorphic w)
  have hchain := planeExtension_deriv_comp (g := c ∘ p.projection)
    (h := Hlim) (w := discZero) (hHlim0.symm ▸ hpcoord) (hHlim discZero)
  have hcoord : d ∘ F = (c ∘ p.projection) ∘ Hlim := rfl
  have hreading : planeExtension (fun v => (Hlim v : ℂ)) =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [isOpen_ball.mem_nhds hzero] with z hz
    exact planeExtension_coe _ ⟨z,hz⟩
  rw [hcoord, hchain, hF0, hHlim0, norm_mul] at hs
  have hs' : B * (C * ‖deriv g 0‖) ≤ 2 := by
    simpa only [show (discZero : ℂ) = 0 from rfl, hreading.deriv_eq,
      discDensity, discDenom, map_zero, sub_zero, div_one] using hs
  have hpositive : 0 < C * ‖deriv g 0‖ := by
    apply (mul_pos_iff_of_pos_left hell).mp
    rw [hprod]
    norm_num
  have hBlell : B ≤ ell :=
    (mul_le_mul_iff_left₀ hpositive).mp (hs'.trans_eq hprod.symm)
  have he : ell = B := le_antisymm hellB hBlell
  change Tendsto a atTop (𝓝 B)
  rw [← he]
  exact ht

end AreaDeficit.Surfaces.DiscCover
