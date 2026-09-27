/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import FunctionTheory.NormalFamilies.ZalcmanMontel
import FunctionTheory.Analytic.UniformPreimageStability
import Mathlib.Topology.LocallyConstant.Basic
import BoundedWanderingDomains.ChartDiscs
import BoundedWanderingDomains.SphericalClusterSet

/-!
# Spherical shrinking for disjoint holomorphic images

This file supplies the normal-family step used for intrinsic discs in a
wandering sequence.  A locally uniform spherical limit of holomorphic maps
with pairwise disjoint images is locally constant.  Montel's theorem then
turns this into uniform spherical shrinking on compact subsets.
-/

open Set Filter Metric Function OnePoint
open scoped Topology Uniformity UniformConvergence

namespace AreaDeficit

open NoWanderingDomains FunctionTheory

private theorem coe_chartFiniteMap_of_ne_infty (p : OnePoint ℂ) (hp : p ≠ ∞) :
    ((chartFiniteMap p : ℂ) : OnePoint ℂ) = p := by
  cases p with
  | infty => exact False.elim (hp rfl)
  | coe z => rfl

/-- At a finite value of the limit, pairwise disjoint images force the
limit germ to be constant.  The proof uses persistence of a prescribed
value under locally uniform holomorphic approximation. -/
theorem eventuallyEq_limit_of_disjoint_images_of_ne_infty
    {F : ℕ → ℂ → OnePoint ℂ} {G : ℂ → OnePoint ℂ} {U : Set ℂ} {x : ℂ}
    (hU : IsOpen U) (hx : x ∈ U)
    (hF : ∀ n, SphereHolomorphicOn (F n) U)
    (hFG : TendstoLocallyUniformlyOn F G atTop U)
    (hdis : Pairwise (fun n m => Disjoint (F n '' U) (F m '' U)))
    (hxfin : G x ≠ ∞) :
    ∀ᶠ y in 𝓝 x, G y = G x := by
  have hGc : ContinuousOn G U :=
    hFG.continuousOn (Frequently.of_forall fun n => (hF n).continuousOn)
  obtain ⟨r, hr, hrU, hGfin, hFfin, hconv⟩ :=
    exists_finite_chart_convergence hU hGc hFG hx hxfin
  have hGhol : SphereHolomorphicOn G U :=
    sphereHolomorphicOn_of_tendstoLocallyUniformlyOn hU hF hFG
  have hGball : SphereHolomorphicOn G (ball x r) :=
    sphereHolomorphicOn_mono hGhol isOpen_ball
      (ball_subset_closedBall.trans hrU)
  have hGdiff : DifferentiableOn ℂ (fun z => chartFiniteMap (G z)) (ball x r) :=
    hGball.differentiableOn_chartFiniteMap
      (fun z hz => hGfin z (ball_subset_closedBall hz))
  by_contra hnot
  have hnc : ¬∀ᶠ z in 𝓝 x, chartFiniteMap (G z) = chartFiniteMap (G x) := by
    intro hchart
    apply hnot
    filter_upwards [hchart, ball_mem_nhds x hr] with z hz hzball
    have hzfin := hGfin z (ball_subset_closedBall hzball)
    exact (coe_chartFiniteMap_of_ne_infty (G z) hzfin).symm.trans
      ((congrArg (fun w : ℂ => (w : OnePoint ℂ)) hz).trans
        (coe_chartFiniteMap_of_ne_infty (G x) hxfin))
  obtain ⟨δ, hδ, hstable⟩ := exists_stable_local_image isOpen_ball
    (hGdiff.analyticOnNhd isOpen_ball) (mem_ball_self hr) hnc hr
  have hclose : ∀ᶠ n in atTop, ∀ z ∈ ball x r,
      ‖chartFiniteMap (G z) - chartFiniteMap (F n z)‖ < δ := by
    have hu := Metric.tendstoUniformlyOn_iff.mp hconv δ hδ
    exact hu.mono fun n hn z hz => by
      simpa only [dist_eq_norm] using hn z (ball_subset_closedBall hz)
  have hevent : ∀ᶠ n in atTop,
      (∀ z ∈ closedBall x r, F n z ≠ ∞) ∧
      (∀ z ∈ ball x r,
        ‖chartFiniteMap (G z) - chartFiniteMap (F n z)‖ < δ) :=
    hFfin.and hclose
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have obtain_preimage : ∀ n ≥ N, ∃ z ∈ ball x r,
      F n z = G x := by
    intro n hn
    have hdata := hN n hn
    have hFball : SphereHolomorphicOn (F n) (ball x r) :=
      sphereHolomorphicOn_mono (hF n) isOpen_ball
        (ball_subset_closedBall.trans hrU)
    have hFdiff : DifferentiableOn ℂ (fun z => chartFiniteMap (F n z))
        (ball x r) :=
      hFball.differentiableOn_chartFiniteMap
        (fun z hz => hdata.1 z (ball_subset_closedBall hz))
    obtain ⟨z, hz, hzval⟩ := hstable
      (fun w => chartFiniteMap (F n w))
      (hFdiff.analyticOnNhd isOpen_ball) hdata.2
      (chartFiniteMap (G x)) (by simp [hδ])
    refine ⟨z, hz.1, ?_⟩
    have hzfin := hdata.1 z (ball_subset_closedBall hz.1)
    exact (coe_chartFiniteMap_of_ne_infty (F n z) hzfin).symm.trans
      ((congrArg (fun w : ℂ => (w : OnePoint ℂ)) hzval).trans
        (coe_chartFiniteMap_of_ne_infty (G x) hxfin))
  obtain ⟨z, hz, hzval⟩ := obtain_preimage N le_rfl
  obtain ⟨w, hw, hwval⟩ := obtain_preimage (N + 1) (Nat.le_succ N)
  have hzU : z ∈ U := hrU (ball_subset_closedBall hz)
  have hwU : w ∈ U := hrU (ball_subset_closedBall hw)
  exact disjoint_left.mp (hdis (Nat.ne_add_one N))
    (hzval ▸ mem_image_of_mem (F N) hzU)
    (hwval ▸ mem_image_of_mem (F (N + 1)) hwU)

/-- Pairwise disjoint images force every spherical locally uniform limit to
be constant on a preconnected source domain. -/
theorem limit_constant_of_disjoint_sphere_images
    {F : ℕ → ℂ → OnePoint ℂ} {G : ℂ → OnePoint ℂ} {U : Set ℂ} {x : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hF : ∀ n, SphereHolomorphicOn (F n) U)
    (hFG : TendstoLocallyUniformlyOn F G atTop U)
    (hdis : Pairwise (fun n m => Disjoint (F n '' U) (F m '' U))) :
    ∀ z ∈ U, G z = G x := by
  have hinj : Injective (fun p : OnePoint ℂ => inversionGL • p) :=
    MulAction.injective inversionGL
  have hlocal : ∀ z ∈ U, ∀ᶠ w in 𝓝 z, G w = G z := by
    intro z hz
    by_cases hzfin : G z ≠ ∞
    · exact eventuallyEq_limit_of_disjoint_images_of_ne_infty
        hU hz hF hFG hdis hzfin
    · have hzinf : G z = ∞ := not_ne_iff.mp hzfin
      let FI : ℕ → ℂ → OnePoint ℂ := fun n w => inversionGL • F n w
      let GI : ℂ → OnePoint ℂ := fun w => inversionGL • G w
      have hFhol : ∀ n, SphereHolomorphicOn (FI n) U :=
        fun n => (hF n).gl_smul inversionGL
      have hconv : TendstoLocallyUniformlyOn FI GI atTop U :=
        tendstoLocallyUniformlyOn_sphere_inversion hFG
      have hdisI : Pairwise (fun n m => Disjoint (FI n '' U) (FI m '' U)) := by
        intro n m hnm
        apply disjoint_left.mpr
        rintro p ⟨a, ha, hap⟩ ⟨b, hb, hbp⟩
        have hab : F n a = F m b := hinj (hap.trans hbp.symm)
        exact disjoint_left.mp (hdis hnm)
          (mem_image_of_mem (F n) ha) (hab ▸ mem_image_of_mem (F m) hb)
      have hGIz : GI z ≠ ∞ := by
        simp only [GI, hzinf, inversionGL_smul_infty]
        exact OnePoint.coe_ne_infty 0
      have hev := eventuallyEq_limit_of_disjoint_images_of_ne_infty
        hU hz hFhol hconv hdisI hGIz
      exact hev.mono fun w hw => hinj hw
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hlc : IsLocallyConstant (fun z : U => G z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    exact (continuous_subtype_val.tendsto z).eventually (hlocal z z.property)
  intro z hz
  exact hlc.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨x, hx⟩

/-- Pointwise normality near a compact set can be glued over a finite open
cover. -/
theorem exists_normal_open_superset_of_compact
    {𝓕 : Set (ℂ → OnePoint ℂ)} {K : Set ℂ} (hK : IsCompact K)
    (hN : ∀ z ∈ K, IsNormalAt 𝓕 z) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ IsNormal 𝓕 V := by
  classical
  choose W hWmem hWnormal using fun z : K => hN z z.property
  let V : K → Set ℂ := fun z => interior (W z)
  have hVopen : ∀ z, IsOpen (V z) := fun z => isOpen_interior
  have hVz : ∀ z : K, (z : ℂ) ∈ V z := fun z =>
    mem_interior_iff_mem_nhds.mpr (hWmem z)
  have hVnormal : ∀ z, IsNormal 𝓕 (V z) := fun z =>
    (hWnormal z).mono interior_subset
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen (fun z hz =>
    mem_iUnion.mpr ⟨⟨z, hz⟩, hVz ⟨z, hz⟩⟩)
  have hfinite : ∀ s : Finset K, IsNormal 𝓕 (⋃ z ∈ s, V z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro seq
        refine ⟨id, strictMono_id, (seq 0 : ℂ → OnePoint ℂ), ?_⟩
        intro u hu x hx
        obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hx
        exact False.elim (Finset.notMem_empty i hi)
    | insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        exact IsNormal.union (hVopen a)
          (isOpen_biUnion fun z _ => hVopen z) (hVnormal a) ih
  exact ⟨⋃ z ∈ t, V z, isOpen_biUnion fun z _ => hVopen z, ht, hfinite t⟩

/-- Sphere-valued holomorphic maps of the unit disc that omit two fixed
finite values and have pairwise disjoint images shrink uniformly on every
smaller closed disc, relative to their centre values. -/
theorem disjoint_sphere_images_shrink
    {F : ℕ → ℂ → OnePoint ℂ} {a b : ℂ} (hab : a ≠ b)
    (hF : ∀ n, SphereHolomorphicOn (F n) (ball 0 1))
    (homit : ∀ n z, z ∈ ball (0 : ℂ) 1 →
      F n z ≠ (a : OnePoint ℂ) ∧ F n z ≠ (b : OnePoint ℂ) ∧ F n z ≠ ∞)
    (hdis : Pairwise (fun n m =>
      Disjoint (F n '' ball (0 : ℂ) 1) (F m '' ball 0 1)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun n z => dist (F n z) (F n 0)) (fun _ => 0) atTop
      (closedBall (0 : ℂ) r) := by
  let s : ℝ := (r + 1) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt hr hrs
  let 𝓕 : Set (ℂ → OnePoint ℂ) := range F
  have hnormalAt : ∀ z ∈ closedBall (0 : ℂ) s, IsNormalAt 𝓕 z := by
    intro z hz
    apply isNormalAt_of_two_omitted_values hab isOpen_ball
    · rintro G ⟨n, rfl⟩
      exact hF n
    · rintro G ⟨n, rfl⟩ w hw
      exact homit n w hw
    · exact (closedBall_subset_ball hs1) hz
  obtain ⟨V, hVo, hKV, hnormalV⟩ :=
    exists_normal_open_superset_of_compact (isCompact_closedBall (0 : ℂ) s)
      hnormalAt
  have hballV : ball (0 : ℂ) s ⊆ V :=
    ball_subset_closedBall.trans hKV
  have hnormal : IsNormal 𝓕 (ball (0 : ℂ) s) := hnormalV.mono hballV
  have hLsub : closedBall (0 : ℂ) r ⊆ ball 0 s :=
    closedBall_subset_ball hrs
  let q : ℕ → (ℂ →ᵤ[{closedBall (0 : ℂ) r}] ℝ) :=
    fun n => UniformOnFun.ofFun _ (fun z => dist (F n z) (F n 0))
  suffices Tendsto q atTop
      (𝓝 (UniformOnFun.ofFun {closedBall (0 : ℂ) r} (fun _ => (0 : ℝ)))) by
    simpa [UniformOnFun.tendsto_iff_tendstoUniformlyOn, q, Function.comp_def]
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨θ, hθ, hnsθ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨φ, hφ, G, hconv⟩ := hnormal
    (fun n => ⟨F (ns (θ n)), mem_range_self (ns (θ n))⟩)
  have hidx : StrictMono (ns ∘ θ ∘ φ) := hnsθ.comp hφ
  have hhol : ∀ n, SphereHolomorphicOn (F (ns (θ (φ n)))) (ball 0 s) :=
    fun n => sphereHolomorphicOn_mono (hF _) isOpen_ball (ball_subset_ball hs1.le)
  have hdis' : Pairwise (fun n m => Disjoint
      (F (ns (θ (φ n))) '' ball (0 : ℂ) s)
      (F (ns (θ (φ m))) '' ball 0 s)) := by
    intro n m hnm
    exact (hdis (hidx.injective.ne hnm)).mono
      (image_mono (ball_subset_ball hs1.le))
      (image_mono (ball_subset_ball hs1.le))
  have hconst : ∀ z ∈ ball (0 : ℂ) s, G z = G 0 :=
    limit_constant_of_disjoint_sphere_images isOpen_ball
      (convex_ball (0 : ℂ) s).isPreconnected (mem_ball_self hs0)
      hhol hconv hdis'
  have hu : TendstoUniformlyOn (fun n => F (ns (θ (φ n)))) G atTop
      (closedBall (0 : ℂ) r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall (0 : ℂ) r)).mp (hconv.mono hLsub)
  have hx : Tendsto (fun n => F (ns (θ (φ n))) 0) atTop (𝓝 (G 0)) :=
    hconv.tendsto_at (mem_ball_self hs0)
  have hdist : TendstoUniformlyOn
      (fun n z => dist (F (ns (θ (φ n))) z) (F (ns (θ (φ n))) 0))
      (fun _ => (0 : ℝ)) atTop (closedBall (0 : ℂ) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    have hu' := Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) hε2
    have hx' := Metric.tendsto_nhds.mp hx (ε / 2) hε2
    filter_upwards [hu', hx'] with n hn hnx z hz
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
    calc
      dist (F (ns (θ (φ n))) z) (F (ns (θ (φ n))) 0)
          ≤ dist (F (ns (θ (φ n))) z) (G z) +
              dist (G 0) (F (ns (θ (φ n))) 0) := by
            rw [hconst z (hLsub hz)]
            exact dist_triangle _ _ _
      _ < ε := by
        have hzclose : dist (F (ns (θ (φ n))) z) (G z) < ε / 2 := by
          simpa only [dist_comm] using hn z hz
        have h0close : dist (G 0) (F (ns (θ (φ n))) 0) < ε / 2 := by
          simpa only [dist_comm] using hnx
        linarith
  refine ⟨θ ∘ φ, ?_⟩
  simpa [UniformOnFun.tendsto_iff_tendstoUniformlyOn, q, Function.comp_def]
    using hdist

/-- Normalised inverse Riemann maps of pairwise disjoint simply connected
domains shrink spherically on every fixed closed subdisc. -/
theorem inverse_riemann_maps_shrink
    {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun n w => dist
        ((invFunOn (u (n + 1)) (U (n + 1)) w : ℂ) : OnePoint ℂ)
        ((z (n + 1) : ℂ) : OnePoint ℂ))
      (fun _ => 0) atTop (closedBall (0 : ℂ) r) := by
  let p : ℕ → ℂ → ℂ := fun n => invFunOn (u (n + 1)) (U (n + 1))
  let p0 : ℂ → ℂ := invFunOn (u 0) (U 0)
  let c : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hc : c ∈ ball (0 : ℂ) 1 := by
    dsimp [c]
    rw [mem_ball_zero_iff]
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self one_pos
  have hp0map : MapsTo p0 (ball (0 : ℂ) 1) (U 0) := by
    intro w hw
    exact invFunOn_mem ((hub 0).surjOn hw)
  have haU : p0 0 ∈ U 0 := hp0map hzero
  have hbU : p0 c ∈ U 0 := hp0map hc
  have hab : p0 0 ≠ p0 c := by
    intro heq
    have h0 := (hub 0).surjOn.rightInvOn_invFunOn hzero
    have hc' := (hub 0).surjOn.rightInvOn_invFunOn hc
    have := congrArg (u 0) heq
    rw [h0, hc'] at this
    exact (by norm_num [c] at this)
  have hpmap : ∀ n, MapsTo (p n) (ball (0 : ℂ) 1) (U (n + 1)) := by
    intro n w hw
    exact invFunOn_mem ((hub (n + 1)).surjOn hw)
  have hpdiff : ∀ n, DifferentiableOn ℂ (p n) (ball (0 : ℂ) 1) := by
    intro n
    simpa only [(hub (n + 1)).image_eq] using
      (hu (n + 1)).invFunOn (hU (n + 1)) (hub (n + 1)).injOn
  have hpsphere : ∀ n, SphereHolomorphicOn
      (fun w => ((p n w : ℂ) : OnePoint ℂ)) (ball (0 : ℂ) 1) :=
    fun n => (hpdiff n).sphereHolomorphicOn isOpen_ball
  have hpdis : Pairwise (fun n m => Disjoint
      ((fun w => ((p n w : ℂ) : OnePoint ℂ)) '' ball (0 : ℂ) 1)
      ((fun w => ((p m w : ℂ) : OnePoint ℂ)) '' ball 0 1)) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro q ⟨a, ha, haq⟩ ⟨b, hb, hbq⟩
    have hpab : p n a = p m b := OnePoint.coe_injective (haq.trans hbq.symm)
    exact disjoint_left.mp (hdis (by omega : n + 1 ≠ m + 1))
      (hpmap n ha) (hpab ▸ hpmap m hb)
  have hpomit : ∀ n w, w ∈ ball (0 : ℂ) 1 →
      ((p n w : ℂ) : OnePoint ℂ) ≠ ((p0 0 : ℂ) : OnePoint ℂ) ∧
      ((p n w : ℂ) : OnePoint ℂ) ≠ ((p0 c : ℂ) : OnePoint ℂ) ∧
      ((p n w : ℂ) : OnePoint ℂ) ≠ ∞ := by
    intro n w hw
    have hpU := hpmap n hw
    refine ⟨?_, ?_, OnePoint.coe_ne_infty _⟩
    · intro heq
      have heq' := OnePoint.coe_injective heq
      exact disjoint_left.mp (hdis (by omega : 0 ≠ n + 1)) haU (heq' ▸ hpU)
    · intro heq
      have heq' := OnePoint.coe_injective heq
      exact disjoint_left.mp (hdis (by omega : 0 ≠ n + 1)) hbU (heq' ▸ hpU)
  have hshrink := disjoint_sphere_images_shrink hab hpsphere hpomit hpdis hr hr1
  have hpcentre : ∀ n, p n 0 = z (n + 1) := by
    intro n
    rw [← hu0 (n + 1)]
    exact (hub (n + 1)).injOn.leftInvOn_invFunOn (hz (n + 1))
  simpa only [p, hpcentre] using hshrink

/-- Every fixed intrinsic disc is eventually contained in any prescribed
open neighbourhood of the spherical cluster set of its centre orbit. -/
theorem eventually_chartDisc_subset_cluster_neighbourhood
    {U : ℕ → Set ℂ} {u : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    (hU : ∀ n, IsOpen (U n))
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1))
    (hz : ∀ n, z n ∈ U n) (hu0 : ∀ n, u n (z n) = 0)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {O : Set (OnePoint ℂ)} (hO : IsOpen O)
    (hcluster : BoundedWanderingDomains.sphericalClusterSet
      (fun n => ((z n : ℂ) : OnePoint ℂ)) ⊆ O)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop,
      ((fun w : ℂ => ((w : ℂ) : OnePoint ℂ)) ''
        chartDisc (u (n + 1)) (U (n + 1)) r) ⊆ O := by
  let K := BoundedWanderingDomains.sphericalClusterSet
    (fun n => ((z n : ℂ) : OnePoint ℂ))
  have hK : IsCompact K :=
    BoundedWanderingDomains.isCompact_sphericalClusterSet _
  obtain ⟨V, hVo, hKV, hclV⟩ :=
    hK.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hcluster)
  have hclK : IsCompact (closure V) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hclK
    (fun _ : Unit => hO) (by
      intro x hx
      exact mem_iUnion.mpr ⟨Unit.unit, hclV hx⟩)
  have hzV0 : ∀ᶠ n in atTop, ((z n : ℂ) : OnePoint ℂ) ∈ V :=
    BoundedWanderingDomains.eventually_mem_of_sphericalClusterSet_subset
      (fun n => ((z n : ℂ) : OnePoint ℂ)) hVo hKV
  have hzV : ∀ᶠ n in atTop, ((z (n + 1) : ℂ) : OnePoint ℂ) ∈ V := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hzV0
    exact eventually_atTop.mpr ⟨N, fun n hn => hN (n + 1) (hn.trans (Nat.le_succ n))⟩
  have hshrink := inverse_riemann_maps_shrink hU hu hub hz hu0 hdis hr.le hr1
  have hclose := Metric.tendstoUniformlyOn_iff.mp hshrink δ hδ
  filter_upwards [hzV, hclose] with n hzn hn
  intro q hq
  obtain ⟨x, hx, hxq⟩ := hq
  let w := u (n + 1) x
  have hwball : w ∈ ball (0 : ℂ) r := hx.2
  have hwclosed : w ∈ closedBall (0 : ℂ) r := ball_subset_closedBall hwball
  have hpval : invFunOn (u (n + 1)) (U (n + 1)) w = x :=
    (hub (n + 1)).injOn.leftInvOn_invFunOn hx.1
  have hdist : dist ((x : ℂ) : OnePoint ℂ) ((z (n + 1) : ℂ) : OnePoint ℂ) < δ := by
    have hraw := hn w hwclosed
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at hraw
    simpa only [hpval] using hraw
  obtain ⟨i, hi⟩ := hball ((z (n + 1) : ℂ) : OnePoint ℂ) (subset_closure hzn)
  rw [← hxq]
  exact hi (by simpa only [mem_ball, dist_comm] using hdist)

end AreaDeficit
