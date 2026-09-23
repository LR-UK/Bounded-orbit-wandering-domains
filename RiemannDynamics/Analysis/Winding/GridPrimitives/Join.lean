/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Winding.GridPrimitives.Basic

/-!
# Grid squares under nonzero winding, and joining grid paths

A grid square with nonzero winding number of the loop lies in the open set; the
grid path integral vanishes for null-winding loops; and grid points in a common
component are joined by grid paths.
-/

open Complex Set unitInterval

namespace RiemannDynamics

/-- **Escape lemma.** If every complementary component of the open set `T`
is unbounded, then every grid square whose center carries nonzero winding of
a grid loop in `T` lies entirely (as a closed square) inside `T`: a
complementary point in the closed square would belong to a bounded pocket of
the winding region, whose frontier lies on the loop trace — but the trace is
in `T`, so the unbounded component through that point cannot escape. -/
theorem gridSquare_subset_of_windingNumber_ne_zero {T : Set ℂ}
    (_hT : IsOpen T)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z))
    {δ : ℝ} (hδ : 0 < δ) {L : List (ℤ × ℤ)} (hL : IsGridPath L)
    (hne : L ≠ []) (hcl : L.head? = L.getLast?)
    (htrace : gridPathTrace δ L ⊆ T) {p : ℤ × ℤ}
    (hp : gridSquareCenter δ p ∉ gridPathTrace δ L)
    (hw : windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) ≠ 0) :
    gridSquare δ p ⊆ T := by
  intro z hz
  by_contra hzT
  -- Basic facts about the loop curve.
  have hclosed : gridLoopCurve δ L 0 = gridLoopCurve δ L 1 :=
    gridLoopCurve_closed hne hcl
  have hrange : Set.range (gridLoopCurve δ L) = gridPathTrace δ L :=
    range_gridLoopCurve hδ hL hne
  have hmemtr : ∀ t : I, gridLoopCurve δ L t ∈ gridPathTrace δ L := by
    intro t
    rw [← hrange]
    exact Set.mem_range_self t
  -- Coordinates of lattice points.
  have hgpre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgpim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  -- Real and imaginary parts of convex combinations.
  have hsegre : ∀ (a b : ℂ) (u v : ℝ), (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ), (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  -- Every point of the trace lies on a grid line.
  have hlines : ∀ M : List (ℤ × ℤ), IsGridPath M → ∀ w ∈ gridPathTrace δ M,
      (∃ m : ℤ, w.re = δ * m) ∨ (∃ n : ℤ, w.im = δ * n) := by
    intro M
    induction M with
    | nil => intro _ w hwtr; exact absurd hwtr (Set.notMem_empty w)
    | cons a M ih =>
      intro hM w hwtr
      cases M with
      | nil =>
        have hwa : w = gridPoint δ a := hwtr
        exact Or.inl ⟨a.1, by rw [hwa]; exact hgpre a⟩
      | cons b M' =>
        have hMc : List.IsChain GridAdj (a :: b :: M') := hM
        have hadj : GridAdj a b := (List.isChain_cons_cons.mp hMc).1
        have htl : IsGridPath (b :: M') := (List.isChain_cons_cons.mp hMc).2
        rcases hwtr with hseg | htr
        · obtain ⟨u, v, hu, hv, huv, hwe⟩ := hseg
          rcases hadj with ⟨hx, -⟩ | ⟨-, hy⟩
          · refine Or.inl ⟨a.1, ?_⟩
            rw [← hwe, hsegre, hgpre a, hgpre b, ← hx]
            calc u * (δ * (a.1 : ℝ)) + v * (δ * a.1)
                = (u + v) * (δ * a.1) := by ring
              _ = δ * a.1 := by rw [huv, one_mul]
          · refine Or.inr ⟨a.2, ?_⟩
            rw [← hwe, hsegim, hgpim a, hgpim b, ← hy]
            calc u * (δ * (a.2 : ℝ)) + v * (δ * a.2)
                = (u + v) * (δ * a.2) := by ring
              _ = δ * a.2 := by rw [huv, one_mul]
        · exact ih htl w htr
  -- The square as a product of intervals; its interior.
  have hKeq : gridSquare δ p =
      Set.Icc (δ * p.1) (δ * (p.1 + 1)) ×ℂ Set.Icc (δ * p.2) (δ * (p.2 + 1)) := rfl
  have hKint : interior (gridSquare δ p) =
      Set.Ioo (δ * p.1) (δ * (p.1 + 1)) ×ℂ Set.Ioo (δ * p.2) (δ * (p.2 + 1)) := by
    rw [hKeq, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  -- Coordinates of the square's center.
  have hhalf : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
  have hcre : (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    simp only [gridSquareCenter, gridPoint, hhalf, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im]
    ring
  have hcim : (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    simp only [gridSquareCenter, gridPoint, hhalf, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im]
    ring
  -- The center lies in the interior of the square.
  have hcint : gridSquareCenter δ p ∈ interior (gridSquare δ p) := by
    rw [hKint, Complex.mem_reProdIm, hcre, hcim]
    have e1 : δ * ((p.1 : ℝ) + 1) = δ * p.1 + δ := by ring
    have e2 : δ * ((p.2 : ℝ) + 1) = δ * p.2 + δ := by ring
    exact ⟨⟨by linarith, by rw [e1]; linarith⟩, ⟨by linarith, by rw [e2]; linarith⟩⟩
  -- The interior of the square misses the trace.
  have hIntDisj : ∀ w, w ∈ interior (gridSquare δ p) → w ∉ gridPathTrace δ L := by
    intro w hwint hwtr
    rw [hKint, Complex.mem_reProdIm] at hwint
    obtain ⟨⟨hre1, hre2⟩, him1, him2⟩ := hwint
    rcases hlines L hL w hwtr with ⟨m, hm⟩ | ⟨n, hn⟩
    · rw [hm] at hre1 hre2
      have h1 : p.1 < m := by exact_mod_cast lt_of_mul_lt_mul_left hre1 hδ.le
      have h2 : m < p.1 + 1 := by exact_mod_cast lt_of_mul_lt_mul_left hre2 hδ.le
      omega
    · rw [hn] at him1 him2
      have h1 : p.2 < n := by exact_mod_cast lt_of_mul_lt_mul_left him1 hδ.le
      have h2 : n < p.2 + 1 := by exact_mod_cast lt_of_mul_lt_mul_left him2 hδ.le
      omega
  -- The square is convex.
  have hKconv : Convex ℝ (gridSquare δ p) := by
    intro x hx y hy u v hu hv huv
    obtain ⟨⟨hxr1, hxr2⟩, hxi1, hxi2⟩ := hx
    obtain ⟨⟨hyr1, hyr2⟩, hyi1, hyi2⟩ := hy
    have hcombo : ∀ c : ℝ, c = u * c + v * c := by
      intro c
      rw [← add_mul, huv, one_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hsegre, hcombo (δ * (p.1 : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxr1 hu)
        (mul_le_mul_of_nonneg_left hyr1 hv)
    · rw [hsegre, hcombo (δ * ((p.1 : ℝ) + 1))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxr2 hu)
        (mul_le_mul_of_nonneg_left hyr2 hv)
    · rw [hsegim, hcombo (δ * (p.2 : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxi1 hu)
        (mul_le_mul_of_nonneg_left hyi1 hv)
    · rw [hsegim, hcombo (δ * ((p.2 : ℝ) + 1))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxi2 hu)
        (mul_le_mul_of_nonneg_left hyi2 hv)
  -- The square minus the trace is preconnected (star-shaped about the center).
  have hSpre : IsPreconnected (gridSquare δ p \ gridPathTrace δ L) := by
    apply isPreconnected_of_forall (gridSquareCenter δ p)
    intro y hy
    refine ⟨segment ℝ (gridSquareCenter δ p) y, ?_, left_mem_segment ℝ _ _,
      right_mem_segment ℝ _ _, (convex_segment _ _).isPreconnected⟩
    intro x hx
    rcases eq_or_ne x (gridSquareCenter δ p) with rfl | hxc
    · exact ⟨interior_subset hcint, hp⟩
    rcases eq_or_ne x y with rfl | hxy
    · exact hy
    have hxopen : x ∈ openSegment ℝ (gridSquareCenter δ p) y := by
      obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
      rcases hu.eq_or_lt with hu0 | hu0
      · have hv1 : v = 1 := by linarith
        refine absurd (Complex.ext ?_ ?_) hxy
        · rw [← hxe, hsegre, ← hu0, hv1]; ring
        · rw [← hxe, hsegim, ← hu0, hv1]; ring
      · rcases hv.eq_or_lt with hv0 | hv0
        · have hu1 : u = 1 := by linarith
          refine absurd (Complex.ext ?_ ?_) hxc
          · rw [← hxe, hsegre, ← hv0, hu1]; ring
          · rw [← hxe, hsegim, ← hv0, hu1]; ring
        · exact ⟨u, v, hu0, hv0, huv, hxe⟩
    have hxint : x ∈ interior (gridSquare δ p) :=
      hKconv.openSegment_interior_self_subset_interior hcint hy.1 hxopen
    exact ⟨interior_subset hxint, hIntDisj x hxint⟩
  -- Winding is constant on the square minus the trace: center vs `z`.
  have hznt : z ∉ gridPathTrace δ L := fun hzt => hzT (htrace hzt)
  have hzS : z ∈ gridSquare δ p \ gridPathTrace δ L := ⟨hz, hznt⟩
  have hcS : gridSquareCenter δ p ∈ gridSquare δ p \ gridPathTrace δ L :=
    ⟨interior_subset hcint, hp⟩
  have hdisjS : ∀ t : I,
      gridLoopCurve δ L t ∉ gridSquare δ p \ gridPathTrace δ L :=
    fun t ht => ht.2 (hmemtr t)
  have heq1 : windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) =
      windingNumber (gridLoopCurve δ L) z :=
    windingNumber_eq_of_preconnected hclosed hSpre hdisjS hcS hzS
  -- Winding is constant on the unbounded complementary component of `z`.
  have hzC : z ∈ connectedComponentIn Tᶜ z := mem_connectedComponentIn hzT
  have hCsub : connectedComponentIn Tᶜ z ⊆ Tᶜ := connectedComponentIn_subset _ _
  have hCpre : IsPreconnected (connectedComponentIn Tᶜ z) :=
    isPreconnected_connectedComponentIn
  have hdisjC : ∀ t : I, gridLoopCurve δ L t ∉ connectedComponentIn Tᶜ z :=
    fun t ht => (hCsub ht) (htrace (hmemtr t))
  have hcompact : IsCompact (Set.range (gridLoopCurve δ L)) :=
    isCompact_range (gridLoopCurve δ L).continuous
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall 0
  have hnsub : ¬ connectedComponentIn Tᶜ z ⊆ Metric.closedBall (0 : ℂ) (R + 1) :=
    fun hsub => hcompl z hzT (Metric.isBounded_closedBall.subset hsub)
  obtain ⟨x₀, hx₀C, hx₀out⟩ := Set.not_subset.mp hnsub
  have hx₀zero : windingNumber (gridLoopCurve δ L) x₀ = 0 := by
    refine windingNumber_eq_zero_of_ball (c := 0) (r := R + 1) hclosed ?_ ?_
    · intro t
      have ht := hR (Set.mem_range_self t)
      rw [Metric.mem_closedBall] at ht
      rw [Metric.mem_ball]
      linarith
    · exact fun hb => hx₀out (Metric.ball_subset_closedBall hb)
  have heq2 : windingNumber (gridLoopCurve δ L) z =
      windingNumber (gridLoopCurve δ L) x₀ :=
    windingNumber_eq_of_preconnected hclosed hCpre hdisjC hzC hx₀C
  exact hw (heq1.trans (heq2.trans hx₀zero))

/-- Grid-loop integrals of holomorphic functions vanish on domains with no
bounded complementary components: combine the edge-counting identity, the
escape lemma, and the rectangle Cauchy theorem. -/
theorem gridPathIntegral_eq_zero {T : Set ℂ} (hT : IsOpen T)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f T) {δ : ℝ} (hδ : 0 < δ)
    {L : List (ℤ × ℤ)} (hL : IsGridPath L) (hne : L ≠ [])
    (hcl : L.head? = L.getLast?) (htrace : gridPathTrace δ L ⊆ T) :
    gridPathIntegral f δ L = 0 := by
  -- Horizontal segment integrals as interval integrals.
  have hseg_h : ∀ x₀ x₁ y : ℝ,
      segmentIntegral f ((x₀ : ℂ) + (y : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y : ℂ) * Complex.I) =
        ∫ x in x₀..x₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x₀ x₁ y
    have e1 : (x₁ - x₀) * (0 : ℝ) + x₀ = x₀ := by ring
    have e2 : (x₁ - x₀) * (1 : ℝ) + x₀ = x₁ := by ring
    have key := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun v : ℝ => f ((v : ℂ) + (y : ℂ) * Complex.I)) (x₁ - x₀) x₀
    rw [e1, e2] at key
    have key' : ((x₁ - x₀ : ℝ) : ℂ) *
        (∫ t in (0 : ℝ)..1,
          f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = ∫ v in x₀..x₁, f ((v : ℂ) + (y : ℂ) * Complex.I) := by
      rw [← Complex.real_smul]
      exact key
    calc segmentIntegral f ((x₀ : ℂ) + (y : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, ((x₁ - x₀ : ℝ) : ℂ) *
            f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
          unfold segmentIntegral
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [Complex.real_smul]
          have harg : ((x₀ : ℂ) + (y : ℂ) * Complex.I) + (t : ℂ) *
                (((x₁ : ℂ) + (y : ℂ) * Complex.I) -
                  ((x₀ : ℂ) + (y : ℂ) * Complex.I))
              = (((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg]
          have hco : ((x₁ : ℂ) + (y : ℂ) * Complex.I) -
                ((x₀ : ℂ) + (y : ℂ) * Complex.I) = ((x₁ - x₀ : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hco]
      _ = ((x₁ - x₀ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
            f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
          intervalIntegral.integral_const_mul _ _
      _ = ∫ x in x₀..x₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := key'
  -- Vertical segment integrals as interval integrals.
  have hseg_v : ∀ x y₀ y₁ : ℝ,
      segmentIntegral f ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x : ℂ) + (y₁ : ℂ) * Complex.I) =
        Complex.I * ∫ y in y₀..y₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x y₀ y₁
    have e1 : (y₁ - y₀) * (0 : ℝ) + y₀ = y₀ := by ring
    have e2 : (y₁ - y₀) * (1 : ℝ) + y₀ = y₁ := by ring
    have key := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun v : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) (y₁ - y₀) y₀
    rw [e1, e2] at key
    have key' : ((y₁ - y₀ : ℝ) : ℂ) *
        (∫ t in (0 : ℝ)..1,
          f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I))
        = ∫ v in y₀..y₁, f ((x : ℂ) + (v : ℂ) * Complex.I) := by
      rw [← Complex.real_smul]
      exact key
    calc segmentIntegral f ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x : ℂ) + (y₁ : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, Complex.I * (((y₁ - y₀ : ℝ) : ℂ) *
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I)) := by
          unfold segmentIntegral
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [Complex.real_smul]
          have harg : ((x : ℂ) + (y₀ : ℂ) * Complex.I) + (t : ℂ) *
                (((x : ℂ) + (y₁ : ℂ) * Complex.I) -
                  ((x : ℂ) + (y₀ : ℂ) * Complex.I))
              = (x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg]
          have hco : ((x : ℂ) + (y₁ : ℂ) * Complex.I) -
                ((x : ℂ) + (y₀ : ℂ) * Complex.I)
              = Complex.I * ((y₁ - y₀ : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hco, mul_assoc]
      _ = Complex.I * ∫ t in (0 : ℝ)..1, ((y₁ - y₀ : ℝ) : ℂ) *
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I) :=
          intervalIntegral.integral_const_mul _ _
      _ = Complex.I * (((y₁ - y₀ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I)) :=
          congrArg (Complex.I * ·) (intervalIntegral.integral_const_mul _ _)
      _ = Complex.I * ∫ y in y₀..y₁, f ((x : ℂ) + (y : ℂ) * Complex.I) :=
          congrArg (Complex.I * ·) key'
  -- Cauchy's theorem for an axis-parallel square boundary, in segment form.
  have hsquare : ∀ x₀ x₁ y₀ y₁ : ℝ, x₀ ≤ x₁ → y₀ ≤ y₁ →
      DifferentiableOn ℂ f (Set.Icc x₀ x₁ ×ℂ Set.Icc y₀ y₁) →
      segmentIntegral f ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y₀ : ℂ) * Complex.I) +
        segmentIntegral f ((x₁ : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) +
        segmentIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I)
          ((x₀ : ℂ) + (y₁ : ℂ) * Complex.I) +
        segmentIntegral f ((x₀ : ℂ) + (y₁ : ℂ) * Complex.I)
          ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I) = 0 := by
    intro x₀ x₁ y₀ y₁ hx hy hdiff
    have h1 : ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re = x₀ := by simp
    have h2 : ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re = x₁ := by simp
    have h3 : ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im = y₀ := by simp
    have h4 : ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im = y₁ := by simp
    have hd : DifferentiableOn ℂ f
        (Set.uIcc ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re
            ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re ×ℂ
          Set.uIcc ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im
            ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) := by
      rw [h1, h2, h3, h4, Set.uIcc_of_le hx, Set.uIcc_of_le hy]
      exact hdiff
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I) ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) hd
    rw [h1, h2, h3, h4] at hrect
    have hrect' : (∫ x in x₀..x₁, f ((x : ℂ) + (y₀ : ℂ) * Complex.I)) -
        (∫ x in x₀..x₁, f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) +
        Complex.I * (∫ y in y₀..y₁, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in y₀..y₁, f ((x₀ : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
      hrect
    rw [hseg_h x₀ x₁ y₀, hseg_v x₁ y₀ y₁, hseg_h x₁ x₀ y₁, hseg_v x₀ y₁ y₀,
      intervalIntegral.integral_symm x₀ x₁, intervalIntegral.integral_symm y₀ y₁]
    linear_combination hrect'
  -- Edge-counting identity gives the winding-weighted sum.
  obtain ⟨S, hS, hsum⟩ := gridPathIntegral_eq_sum_windings f hδ hL hne hcl
  rw [hsum]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hw, hcen⟩ := hS p hp
  -- Escape lemma: the closed square lies in `T`.
  have hsub : gridSquare δ p ⊆ T :=
    gridSquare_subset_of_windingNumber_ne_zero hT hcompl hδ hL hne hcl htrace
      hcen hw
  have hset : (Set.Icc (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) ×ℂ
      Set.Icc (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1))) = gridSquare δ p := by
    ext z
    simp only [Complex.mem_reProdIm, gridSquare, Set.mem_ofPred_eq]
  have hdiff : DifferentiableOn ℂ f
      (Set.Icc (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) ×ℂ
        Set.Icc (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1))) :=
    hf.mono (by rw [hset]; exact hsub)
  have hxle : δ * (p.1 : ℝ) ≤ δ * ((p.1 : ℝ) + 1) := by nlinarith [hδ]
  have hyle : δ * (p.2 : ℝ) ≤ δ * ((p.2 : ℝ) + 1) := by nlinarith [hδ]
  have hsq := hsquare (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) (δ * (p.2 : ℝ))
    (δ * ((p.2 : ℝ) + 1)) hxle hyle hdiff
  -- Identify the four corners of the grid square.
  have hA : gridPoint δ p
      = ((δ * (p.1 : ℝ) : ℝ) : ℂ) + ((δ * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hB : gridPoint δ (p.1 + 1, p.2)
      = ((δ * ((p.1 : ℝ) + 1) : ℝ) : ℂ) + ((δ * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hC : gridPoint δ (p.1 + 1, p.2 + 1)
      = ((δ * ((p.1 : ℝ) + 1) : ℝ) : ℂ) +
        ((δ * ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hD : gridPoint δ (p.1, p.2 + 1)
      = ((δ * (p.1 : ℝ) : ℝ) : ℂ) + ((δ * ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  -- Unfold the square boundary integral into its four segments.
  have hb0 : gridSquareBoundaryIntegral f δ p
      = segmentIntegral f (gridPoint δ p) (gridPoint δ (p.1 + 1, p.2)) +
        (segmentIntegral f (gridPoint δ (p.1 + 1, p.2))
            (gridPoint δ (p.1 + 1, p.2 + 1)) +
          (segmentIntegral f (gridPoint δ (p.1 + 1, p.2 + 1))
              (gridPoint δ (p.1, p.2 + 1)) +
            (segmentIntegral f (gridPoint δ (p.1, p.2 + 1)) (gridPoint δ p) +
              0))) := rfl
  have hbz : gridSquareBoundaryIntegral f δ p = 0 := by
    rw [hb0, hA, hB, hC, hD]
    linear_combination hsq
  rw [hbz, mul_zero]

/-- Any two lattice points of an open connected set are joined by a grid
path inside the set, for all sufficiently fine scales. -/
theorem exists_gridPath_join {T : Set ℂ} (hT : IsOpen T)
    (hconn : IsPreconnected T) {a b : ℂ} (ha : a ∈ T) (hb : b ∈ T) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ (p q : ℤ × ℤ) (L : List (ℤ × ℤ)),
        IsGridPath L ∧ L.head? = some p ∧ L.getLast? = some q ∧
        gridPathTrace δ L ⊆ T ∧
        ‖gridPoint δ p - a‖ ≤ 2 * δ ∧ ‖gridPoint δ q - b‖ ≤ 2 * δ := by
  -- Step 1: a path from `a` to `b` inside `T`.
  have hTc : IsConnected T := ⟨⟨a, ha⟩, hconn⟩
  have hTp : IsPathConnected T := hT.isConnected_iff_isPathConnected.mp hTc
  obtain ⟨γ, hγ⟩ := hTp.joinedIn a ha b hb
  -- Step 2: Lebesgue radius for the compact trace inside the open set.
  have hKc : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hKT : Set.range γ ⊆ T := Set.range_subset_iff.mpr hγ
  obtain ⟨r, hr, hrT⟩ := hKc.exists_thickening_subset_open hT hKT
  have hball : ∀ x ∈ Set.range γ, Metric.ball x r ⊆ T := by
    intro x hx y hy
    exact hrT (Metric.mem_thickening_iff.mpr ⟨x, hx, Metric.mem_ball.mp hy⟩)
  have hUC : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  refine ⟨r / 100, div_pos hr (by norm_num), ?_⟩
  intro δ hδ hδ₀
  -- ## Combinatorial toolkit: unit steps, straight walks, gluing
  have hadjHL : ∀ p : ℤ × ℤ, GridAdj p (p.1 - 1, p.2) :=
    fun p => Or.inr ⟨show (p.1 - (p.1 - 1)).natAbs = 1 by omega, rfl⟩
  have hadjHR : ∀ p : ℤ × ℤ, GridAdj p (p.1 + 1, p.2) :=
    fun p => Or.inr ⟨show (p.1 - (p.1 + 1)).natAbs = 1 by omega, rfl⟩
  have hadjVD : ∀ p : ℤ × ℤ, GridAdj p (p.1, p.2 - 1) :=
    fun p => Or.inl ⟨rfl, show (p.2 - (p.2 - 1)).natAbs = 1 by omega⟩
  have hadjVU : ∀ p : ℤ × ℤ, GridAdj p (p.1, p.2 + 1) :=
    fun p => Or.inl ⟨rfl, show (p.2 - (p.2 + 1)).natAbs = 1 by omega⟩
  -- Horizontal straight walk from `p` by `d` steps (excluding the start).
  have hwalkH : ∀ (n : ℕ) (p : ℤ × ℤ) (d : ℤ), d.natAbs = n →
      ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
        (p :: L).getLast? = some (p.1 + d, p.2) ∧
        ∀ v ∈ p :: L, v.2 = p.2 ∧ (v.1 - p.1).natAbs ≤ d.natAbs := by
    intro n
    induction n with
    | zero =>
      intro p d hd
      have hd0 : d = 0 := by omega
      subst hd0
      refine ⟨[], List.isChain_singleton p, by simp, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨rfl, by omega⟩
    | succ m ih =>
      intro p d hd
      rcases lt_trichotomy d 0 with hneg | h0 | hpos
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1 - 1, p.2) (d + 1) (by omega)
        refine ⟨(p.1 - 1, p.2) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjHL p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          change some (p.1 - 1 + (d + 1), p.2) = some (p.1 + d, p.2)
          rw [show p.1 - 1 + (d + 1) = p.1 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h2, h1⟩ := hbd v hv'
            have h2' : v.2 = p.2 := h2
            have h1' : (v.1 - (p.1 - 1)).natAbs ≤ (d + 1).natAbs := h1
            exact ⟨h2', by omega⟩
      · exfalso; omega
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1 + 1, p.2) (d - 1) (by omega)
        refine ⟨(p.1 + 1, p.2) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjHR p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          change some (p.1 + 1 + (d - 1), p.2) = some (p.1 + d, p.2)
          rw [show p.1 + 1 + (d - 1) = p.1 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h2, h1⟩ := hbd v hv'
            have h2' : v.2 = p.2 := h2
            have h1' : (v.1 - (p.1 + 1)).natAbs ≤ (d - 1).natAbs := h1
            exact ⟨h2', by omega⟩
  -- Vertical straight walk from `p` by `d` steps (excluding the start).
  have hwalkV : ∀ (n : ℕ) (p : ℤ × ℤ) (d : ℤ), d.natAbs = n →
      ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
        (p :: L).getLast? = some (p.1, p.2 + d) ∧
        ∀ v ∈ p :: L, v.1 = p.1 ∧ (v.2 - p.2).natAbs ≤ d.natAbs := by
    intro n
    induction n with
    | zero =>
      intro p d hd
      have hd0 : d = 0 := by omega
      subst hd0
      refine ⟨[], List.isChain_singleton p, by simp, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨rfl, by omega⟩
    | succ m ih =>
      intro p d hd
      rcases lt_trichotomy d 0 with hneg | h0 | hpos
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1, p.2 - 1) (d + 1) (by omega)
        refine ⟨(p.1, p.2 - 1) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjVD p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          change some (p.1, p.2 - 1 + (d + 1)) = some (p.1, p.2 + d)
          rw [show p.2 - 1 + (d + 1) = p.2 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h1, h2⟩ := hbd v hv'
            have h1' : v.1 = p.1 := h1
            have h2' : (v.2 - (p.2 - 1)).natAbs ≤ (d + 1).natAbs := h2
            exact ⟨h1', by omega⟩
      · exfalso; omega
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1, p.2 + 1) (d - 1) (by omega)
        refine ⟨(p.1, p.2 + 1) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjVU p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          change some (p.1, p.2 + 1 + (d - 1)) = some (p.1, p.2 + d)
          rw [show p.2 + 1 + (d - 1) = p.2 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h1, h2⟩ := hbd v hv'
            have h1' : v.1 = p.1 := h1
            have h2' : (v.2 - (p.2 + 1)).natAbs ≤ (d - 1).natAbs := h2
            exact ⟨h1', by omega⟩
  -- Gluing chains along a shared junction.
  have hglue : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m : ℤ × ℤ), List.IsChain GridAdj l₁ →
      l₁.getLast? = some m → List.IsChain GridAdj (m :: l₂) →
      List.IsChain GridAdj (l₁ ++ l₂) := by
    intro l₁ l₂ m h₁ hm h₂
    obtain ⟨hhead, htail⟩ := List.isChain_cons.mp h₂
    refine h₁.append htail ?_
    intro x hx y hy
    rw [hm] at hx
    simp only [Option.mem_some_iff] at hx
    subst hx
    exact hhead y hy
  have hglueLast : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m x : ℤ × ℤ), l₁.getLast? = some m →
      (m :: l₂).getLast? = some x → (l₁ ++ l₂).getLast? = some x := by
    intro l₁ l₂ m x h₁ h₂
    cases l₂ with
    | nil =>
      simp only [List.getLast?_singleton] at h₂
      rw [List.append_nil, h₁]
      exact h₂
    | cons y l =>
      rw [List.getLast?_append_cons]
      rw [List.getLast?_cons_cons] at h₂
      exact h₂
  -- L-shaped walk joining two arbitrary lattice points.
  have hwalk : ∀ p q : ℤ × ℤ, ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
      (p :: L).getLast? = some q ∧
      ∀ v ∈ p :: L, (v.1 - p.1).natAbs ≤ (q.1 - p.1).natAbs ∧
        (v.2 - p.2).natAbs ≤ (q.2 - p.2).natAbs := by
    intro p q
    obtain ⟨L₁, hc₁, hl₁, hb₁⟩ := hwalkH (q.1 - p.1).natAbs p (q.1 - p.1) rfl
    obtain ⟨L₂, hc₂, hl₂, hb₂⟩ :=
      hwalkV (q.2 - p.2).natAbs (p.1 + (q.1 - p.1), p.2) (q.2 - p.2) rfl
    refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
    · rw [← List.cons_append]
      exact hglue (p :: L₁) L₂ (p.1 + (q.1 - p.1), p.2) hc₁ hl₁ hc₂
    · rw [← List.cons_append]
      have h := hglueLast (p :: L₁) L₂ (p.1 + (q.1 - p.1), p.2) _ hl₁ hl₂
      rw [h]
      change some (p.1 + (q.1 - p.1), p.2 + (q.2 - p.2)) = some q
      rw [show p.1 + (q.1 - p.1) = q.1 from by ring, show p.2 + (q.2 - p.2) = q.2 from by ring]
    · intro v hv
      rw [← List.cons_append] at hv
      rcases List.mem_append.mp hv with hv1 | hv2
      · obtain ⟨h2, h1⟩ := hb₁ v hv1
        exact ⟨h1, by omega⟩
      · obtain ⟨h1, h2⟩ := hb₂ v (List.mem_cons_of_mem _ hv2)
        have h1' : v.1 = p.1 + (q.1 - p.1) := h1
        have h2' : (v.2 - p.2).natAbs ≤ (q.2 - p.2).natAbs := h2
        exact ⟨by omega, h2'⟩
  -- ## Trace toolkit
  have htrace_single : ∀ p : ℤ × ℤ, gridPathTrace δ [p] = {gridPoint δ p} := fun p => rfl
  have htrace_cons : ∀ (p q : ℤ × ℤ) (L : List (ℤ × ℤ)),
      gridPathTrace δ (p :: q :: L) =
        segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: L) :=
    fun p q L => rfl
  have htraceConv : ∀ (S : Set ℂ), Convex ℝ S → ∀ L : List (ℤ × ℤ),
      (∀ v ∈ L, gridPoint δ v ∈ S) → gridPathTrace δ L ⊆ S := by
    intro S hS L
    induction L with
    | nil => intro _ w hw; cases hw
    | cons x l ih =>
      intro hv
      cases l with
      | nil =>
        rw [htrace_single]
        rw [Set.singleton_subset_iff]
        exact hv x (List.mem_singleton_self x)
      | cons y l' =>
        rw [htrace_cons]
        apply Set.union_subset
        · exact hS.segment_subset (hv x (by simp)) (hv y (by simp))
        · exact ih fun v hv' => hv v (List.mem_cons_of_mem x hv')
  have htraceApp : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m : ℤ × ℤ), l₁.getLast? = some m →
      gridPathTrace δ (l₁ ++ l₂) ⊆ gridPathTrace δ l₁ ∪ gridPathTrace δ (m :: l₂) := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ m hm; simp at hm
    | cons x l ih =>
      intro l₂ m hm
      cases l with
      | nil =>
        have hx : x = m := by
          simp only [List.getLast?_singleton, Option.some.injEq] at hm
          exact hm
        subst hx
        intro w hw
        rw [List.singleton_append] at hw
        exact Set.mem_union_right _ hw
      | cons y l' =>
        have hm' : (y :: l').getLast? = some m := by
          rwa [List.getLast?_cons_cons] at hm
        intro w hw
        rw [List.cons_append, List.cons_append, htrace_cons] at hw
        rcases hw with hw | hw
        · exact Set.mem_union_left _ (by rw [htrace_cons]; exact Set.mem_union_left _ hw)
        · have hw2 : w ∈ gridPathTrace δ ((y :: l') ++ l₂) := by
            rw [List.cons_append]; exact hw
          rcases ih l₂ m hm' hw2 with h | h
          · exact Set.mem_union_left _ (by rw [htrace_cons]; exact Set.mem_union_right _ h)
          · exact Set.mem_union_right _ h
  -- ## Metric toolkit
  have hgpre : ∀ p : ℤ × ℤ, (gridPoint δ p).re = δ * (p.1 : ℝ) ∧
      (gridPoint δ p).im = δ * (p.2 : ℝ) := by
    intro p
    constructor <;> simp [gridPoint, Complex.mul_re, Complex.mul_im]
  have hgpsub : ∀ p q : ℤ × ℤ, (gridPoint δ q - gridPoint δ p).re = δ * ((q.1 : ℝ) - (p.1 : ℝ)) ∧
      (gridPoint δ q - gridPoint δ p).im = δ * ((q.2 : ℝ) - (p.2 : ℝ)) := by
    intro p q
    rw [Complex.sub_re, Complex.sub_im, (hgpre p).1, (hgpre p).2, (hgpre q).1, (hgpre q).2]
    constructor <;> ring
  have hgp_le : ∀ p q : ℤ × ℤ, ‖gridPoint δ q - gridPoint δ p‖ ≤
      δ * |(q.1 : ℝ) - (p.1 : ℝ)| + δ * |(q.2 : ℝ) - (p.2 : ℝ)| := by
    intro p q
    calc ‖gridPoint δ q - gridPoint δ p‖
        ≤ |(gridPoint δ q - gridPoint δ p).re| + |(gridPoint δ q - gridPoint δ p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = δ * |(q.1 : ℝ) - (p.1 : ℝ)| + δ * |(q.2 : ℝ) - (p.2 : ℝ)| := by
          rw [(hgpsub p q).1, (hgpsub p q).2, abs_mul, abs_mul, abs_of_pos hδ]
  have hgp_ge1 : ∀ p q : ℤ × ℤ, δ * |(q.1 : ℝ) - (p.1 : ℝ)| ≤
      ‖gridPoint δ q - gridPoint δ p‖ := by
    intro p q
    have h := Complex.abs_re_le_norm (gridPoint δ q - gridPoint δ p)
    rwa [(hgpsub p q).1, abs_mul, abs_of_pos hδ] at h
  have hgp_ge2 : ∀ p q : ℤ × ℤ, δ * |(q.2 : ℝ) - (p.2 : ℝ)| ≤
      ‖gridPoint δ q - gridPoint δ p‖ := by
    intro p q
    have h := Complex.abs_im_le_norm (gridPoint δ q - gridPoint δ p)
    rwa [(hgpsub p q).2, abs_mul, abs_of_pos hδ] at h
  have hfloor : ∀ u : ℝ, |δ * ((⌊u / δ⌋ : ℤ) : ℝ) - u| ≤ δ := by
    intro u
    have h1 : ((⌊u / δ⌋ : ℤ) : ℝ) ≤ u / δ := Int.floor_le _
    have h2 : u / δ < ((⌊u / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hcancel : δ * (u / δ) = u := by field_simp
    have h1' : δ * ((⌊u / δ⌋ : ℤ) : ℝ) ≤ u := by
      have := mul_le_mul_of_nonneg_left h1 hδ.le
      rwa [hcancel] at this
    have h2' : u < δ * ((⌊u / δ⌋ : ℤ) : ℝ) + δ := by
      have := mul_lt_mul_of_pos_left h2 hδ
      rw [hcancel] at this
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  have hsnapz : ∀ z : ℂ, ‖gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z‖ ≤ 2 * δ := by
    intro z
    have hre : (gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋)).re = δ * ((⌊z.re / δ⌋ : ℤ) : ℝ) :=
      (hgpre _).1
    have him : (gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋)).im = δ * ((⌊z.im / δ⌋ : ℤ) : ℝ) :=
      (hgpre _).2
    calc ‖gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z‖
        ≤ |(gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z).re| +
          |(gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ δ + δ := by
          rw [Complex.sub_re, Complex.sub_im, hre, him]
          exact add_le_add (hfloor z.re) (hfloor z.im)
      _ = 2 * δ := by ring
  have cast_bound : ∀ x y w : ℤ, (x - y).natAbs ≤ (w - y).natAbs →
      |(x : ℝ) - (y : ℝ)| ≤ |(w : ℝ) - (y : ℝ)| := by
    intro x y w h
    have h1 : |x - y| ≤ |w - y| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h
    have h2 : ((|x - y| : ℤ) : ℝ) ≤ ((|w - y| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs, Int.cast_abs] at h2
    push_cast at h2
    exact h2
  -- ## Sampling the path
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuous_iff.mp hUC δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNη : 1 / (N : ℝ) < η := by
    have hn' : 1 / η < (N : ℝ) := lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n)
    rw [div_lt_iff₀ hη] at hn'
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact hn'
  have hmem : ∀ k : ℕ, k ≤ N → ((k : ℝ) / (N : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_one hNpos]
      exact_mod_cast hk
  let τ : ℕ → I := fun k => Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ))
  have hτ : ∀ k : ℕ, k ≤ N → ((τ k : ℝ)) = (k : ℝ) / (N : ℝ) := by
    intro k hk
    change ((Set.projIcc (0 : ℝ) 1 zero_le_one ((k : ℝ) / (N : ℝ)) : Set.Icc (0 : ℝ) 1) : ℝ) =
      (k : ℝ) / (N : ℝ)
    rw [Set.projIcc_of_mem zero_le_one (hmem k hk)]
  let zf : ℕ → ℂ := fun k => γ (τ k)
  let pt : ℕ → ℤ × ℤ := fun k => (⌊(zf k).re / δ⌋, ⌊(zf k).im / δ⌋)
  have hzK : ∀ k, zf k ∈ Set.range γ := fun k => ⟨τ k, rfl⟩
  have hz0 : zf 0 = a := by
    have h0 : τ 0 = 0 := by
      apply Subtype.ext
      rw [hτ 0 (Nat.zero_le N)]
      simp
    change γ (τ 0) = a
    rw [h0]
    exact γ.source
  have hzN : zf N = b := by
    have h1 : τ N = 1 := by
      apply Subtype.ext
      rw [hτ N le_rfl, div_self (ne_of_gt hNpos)]
      simp
    change γ (τ N) = b
    rw [h1]
    exact γ.target
  have hstep : ∀ k : ℕ, k < N → ‖zf (k + 1) - zf k‖ ≤ δ := by
    intro k hk
    have e1 : ((τ (k + 1) : ℝ)) = ((k : ℝ) + 1) / (N : ℝ) := by
      rw [hτ (k + 1) (by omega)]
      push_cast
      ring
    have e2 : ((τ k : ℝ)) = (k : ℝ) / (N : ℝ) := hτ k (by omega)
    have hd : dist (τ (k + 1)) (τ k) < η := by
      rw [Subtype.dist_eq, e1, e2, Real.dist_eq]
      rw [show ((k : ℝ) + 1) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) from by ring]
      rw [abs_of_pos (div_pos one_pos hNpos)]
      exact hNη
    have h := hmod hd
    rw [dist_eq_norm] at h
    exact h.le
  have hsnap : ∀ k : ℕ, ‖gridPoint δ (pt k) - zf k‖ ≤ 2 * δ := fun k => hsnapz (zf k)
  -- ## Main induction: grid path from `pt 0` to `pt k` with trace in `T`
  have hmain : ∀ k : ℕ, k ≤ N → ∃ L : List (ℤ × ℤ), List.IsChain GridAdj L ∧
      L.head? = some (pt 0) ∧ L.getLast? = some (pt k) ∧ gridPathTrace δ L ⊆ T := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[pt 0], List.isChain_singleton _, by simp, by simp, ?_⟩
      intro w hw
      rw [htrace_single] at hw
      have hw' : w = gridPoint δ (pt 0) := hw
      apply hball (zf 0) (hzK 0)
      rw [Metric.mem_ball, dist_eq_norm, hw']
      calc ‖gridPoint δ (pt 0) - zf 0‖ ≤ 2 * δ := hsnap 0
        _ < r := by linarith
    | succ k ih =>
      intro hk1
      have hk' : k < N := by omega
      obtain ⟨L, hLc, hLh, hLl, hLt⟩ := ih (by omega)
      obtain ⟨W, hWc, hWl, hWb⟩ := hwalk (pt k) (pt (k + 1))
      -- distance between consecutive snapped points
      have h5 : ‖gridPoint δ (pt (k + 1)) - gridPoint δ (pt k)‖ ≤ 5 * δ := by
        have e1 := hsnap k
        have e2 := hsnap (k + 1)
        have e3 := hstep k hk'
        have hsplit : gridPoint δ (pt (k + 1)) - gridPoint δ (pt k) =
            (gridPoint δ (pt (k + 1)) - zf (k + 1)) +
              ((zf (k + 1) - zf k) + (zf k - gridPoint δ (pt k))) := by ring
        rw [hsplit]
        have t1 := norm_add_le (gridPoint δ (pt (k + 1)) - zf (k + 1))
          ((zf (k + 1) - zf k) + (zf k - gridPoint δ (pt k)))
        have t2 := norm_add_le (zf (k + 1) - zf k) (zf k - gridPoint δ (pt k))
        have t3 : ‖zf k - gridPoint δ (pt k)‖ = ‖gridPoint δ (pt k) - zf k‖ :=
          norm_sub_rev _ _
        rw [t3] at t2
        linarith
      -- every vertex of the walk stays near `zf k`
      have hvert : ∀ v ∈ pt k :: W, gridPoint δ v ∈ Metric.ball (zf k) r := by
        intro v hv
        obtain ⟨hb1, hb2⟩ := hWb v hv
        have hc1 := cast_bound v.1 (pt k).1 (pt (k + 1)).1 hb1
        have hc2 := cast_bound v.2 (pt k).2 (pt (k + 1)).2 hb2
        rw [Metric.mem_ball, dist_eq_norm]
        have hle := hgp_le (pt k) v
        have hge1 := hgp_ge1 (pt k) (pt (k + 1))
        have hge2 := hgp_ge2 (pt k) (pt (k + 1))
        have hsn := hsnap k
        have htri : ‖gridPoint δ v - zf k‖ ≤
            ‖gridPoint δ v - gridPoint δ (pt k)‖ + ‖gridPoint δ (pt k) - zf k‖ := by
          rw [show gridPoint δ v - zf k = (gridPoint δ v - gridPoint δ (pt k)) +
            (gridPoint δ (pt k) - zf k) from by ring]
          exact norm_add_le _ _
        have hmul1 : δ * |(v.1 : ℝ) - ((pt k).1 : ℝ)| ≤
            δ * |((pt (k + 1)).1 : ℝ) - ((pt k).1 : ℝ)| :=
          mul_le_mul_of_nonneg_left hc1 hδ.le
        have hmul2 : δ * |(v.2 : ℝ) - ((pt k).2 : ℝ)| ≤
            δ * |((pt (k + 1)).2 : ℝ) - ((pt k).2 : ℝ)| :=
          mul_le_mul_of_nonneg_left hc2 hδ.le
        have hr12 : 12 * δ < r := by linarith
        linarith
      have hWtr : gridPathTrace δ (pt k :: W) ⊆ T := by
        intro w hw
        exact hball (zf k) (hzK k)
          (htraceConv (Metric.ball (zf k) r) (convex_ball _ _) (pt k :: W) hvert hw)
      refine ⟨L ++ W, hglue L W (pt k) hLc hLl hWc, ?_,
        hglueLast L W (pt k) (pt (k + 1)) hLl hWl, ?_⟩
      · cases L with
        | nil => simp at hLh
        | cons x L' =>
          rw [List.cons_append, List.head?_cons]
          rw [List.head?_cons] at hLh
          exact hLh
      · intro w hw
        rcases htraceApp L W (pt k) hLl hw with h | h
        · exact hLt h
        · exact hWtr h
  obtain ⟨L, hc, hh, hl, ht⟩ := hmain N le_rfl
  refine ⟨pt 0, pt N, L, hc, hh, hl, ht, ?_, ?_⟩
  · have h := hsnap 0
    rwa [hz0] at h
  · have h := hsnap N
    rwa [hzN] at h

end RiemannDynamics
