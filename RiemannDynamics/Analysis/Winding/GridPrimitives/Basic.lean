/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Winding.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import RMT4.has_sqrt

/-!
# Grid paths and the winding decomposition of the path integral

Axis-aligned grid paths in the plane, their realized loop curves, and the
decomposition of the grid path integral of a holomorphic function as a sum of
grid-square boundary integrals weighted by winding numbers.
-/

open Complex Set unitInterval

namespace RiemannDynamics

/-- The line-segment contour integral from `a` to `b`. -/
noncomputable def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (b - a) * f (a + t • (b - a))

/-- The lattice point of the `δ`-grid indexed by `p : ℤ × ℤ`. -/
def gridPoint (δ : ℝ) (p : ℤ × ℤ) : ℂ :=
  δ * (p.1 + p.2 * Complex.I)

/-- Two lattice indices are adjacent when they differ by one unit step in
exactly one coordinate. -/
def GridAdj (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1) ∨ ((p.1 - q.1).natAbs = 1 ∧ p.2 = q.2)

/-- A grid path: a list of pairwise-consecutively adjacent lattice indices. -/
def IsGridPath (L : List (ℤ × ℤ)) : Prop :=
  L.IsChain GridAdj

/-- The integral of `f` along the `δ`-realization of a grid path. -/
noncomputable def gridPathIntegral (f : ℂ → ℂ) (δ : ℝ) :
    List (ℤ × ℤ) → ℂ
  | [] => 0
  | [_] => 0
  | p :: q :: L =>
      segmentIntegral f (gridPoint δ p) (gridPoint δ q) +
        gridPathIntegral f δ (q :: L)

/-- The `δ`-realization of a grid path as a set: the union of its closed
segments. -/
def gridPathTrace (δ : ℝ) : List (ℤ × ℤ) → Set ℂ
  | [] => ∅
  | [p] => {gridPoint δ p}
  | p :: q :: L =>
      segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: L)

/-- The closed `δ`-square with lower-left lattice corner `p`. -/
def gridSquare (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (δ * p.1) (δ * (p.1 + 1)) ∧
    z.im ∈ Set.Icc (δ * p.2) (δ * (p.2 + 1))}

/-- The center of the `δ`-square with lower-left corner `p`. -/
noncomputable def gridSquareCenter (δ : ℝ) (p : ℤ × ℤ) : ℂ :=
  gridPoint δ p + (δ / 2) * (1 + Complex.I)

/-- The boundary contour integral of `f` around the `δ`-square at `p`,
traversed counterclockwise. -/
noncomputable def gridSquareBoundaryIntegral (f : ℂ → ℂ) (δ : ℝ)
    (p : ℤ × ℤ) : ℂ :=
  gridPathIntegral f δ
    [p, (p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1, p.2 + 1), p]

/-- The affine segment from `a` to `b` as a path. -/
noncomputable def segmentPath (a b : ℂ) : Path a b where
  toFun t := a + ((t : ℝ) : ℂ) * (b - a)
  continuous_toFun := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp
      continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

/-- The last vertex of a grid path with a given head, structurally. -/
def gridLast : (ℤ × ℤ) → List (ℤ × ℤ) → ℤ × ℤ
  | p, [] => p
  | _, q :: L => gridLast q L

/-- The piecewise-linear realization of a grid path from a head vertex,
folding segment paths by concatenation. -/
noncomputable def gridPathRealize (δ : ℝ) :
    (p : ℤ × ℤ) → (L : List (ℤ × ℤ)) →
      Path (gridPoint δ p) (gridPoint δ (gridLast p L))
  | _, [] => Path.refl _
  | p, q :: L => (segmentPath (gridPoint δ p) (gridPoint δ q)).trans
      (gridPathRealize δ q L)

/-- A grid path realizes as a continuous curve on the unit interval (the
empty path realizes as the constant curve at the origin's lattice point). -/
noncomputable def gridLoopCurve (δ : ℝ) (L : List (ℤ × ℤ)) : C(I, ℂ) :=
  match L with
  | [] => ContinuousMap.const I (gridPoint δ (0, 0))
  | p :: L => (gridPathRealize δ p L).toContinuousMap

/-- The realization of a nonempty closed grid path is a closed curve
starting and ending at its head vertex. -/
theorem gridLoopCurve_closed {δ : ℝ} {L : List (ℤ × ℤ)}
    (hne : L ≠ []) (hcl : L.head? = L.getLast?) :
    gridLoopCurve δ L 0 = gridLoopCurve δ L 1 := by
  obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlast : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (r :: M).getLast? = some (gridLast r M) := by
    intro r M
    induction M generalizing r with
    | nil => simp [gridLast]
    | cons q M ih =>
      rw [List.getLast?_cons_cons, ih]
      rfl
  have hp : p = gridLast p L' := by
    have h := hcl
    rw [List.head?_cons, hlast] at h
    exact Option.some.inj h
  have h0 : gridLoopCurve δ (p :: L') 0 = gridPoint δ p :=
    (gridPathRealize δ p L').source
  have h1 : gridLoopCurve δ (p :: L') 1 = gridPoint δ (gridLast p L') :=
    (gridPathRealize δ p L').target
  rw [h0, h1, ← hp]

/-- The realization's range is the grid-path trace. -/
theorem range_gridLoopCurve {δ : ℝ} (_hδ : 0 < δ) {L : List (ℤ × ℤ)}
    (hL : IsGridPath L) (hne : L ≠ []) :
    Set.range (gridLoopCurve δ L) = gridPathTrace δ L := by
  obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hseg : ∀ a b : ℂ, Set.range (segmentPath a b) = segment ℝ a b := by
    intro a b
    have h1 : ⇑(segmentPath a b)
        = (fun θ : ℝ => a + θ • (b - a)) ∘ ((↑) : I → ℝ) := by
      funext t
      change a + ((t : ℝ) : ℂ) * (b - a) = a + (t : ℝ) • (b - a)
      rw [Complex.real_smul]
    rw [h1, Set.range_comp, Subtype.range_coe]
    exact (segment_eq_image' ℝ a b).symm
  have key : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      Set.range (gridPathRealize δ r M) = gridPathTrace δ (r :: M) := by
    intro r M
    induction M generalizing r with
    | nil =>
      change Set.range (Path.refl (gridPoint δ r)) = ({gridPoint δ r} : Set ℂ)
      exact Path.refl_range
    | cons q M ih =>
      change Set.range ((segmentPath (gridPoint δ r) (gridPoint δ q)).trans
          (gridPathRealize δ q M)) = _
      rw [Path.trans_range, hseg, ih]
      rfl
  exact key p L'

set_option maxHeartbeats 400000 in
-- The edge-counting identity elaborates as one large declaration whose nested
-- winding-weighted-sum `have` chains exceed the default heartbeat budget.
/-- **Edge-counting identity.** The integral of any function along a closed
grid loop equals the winding-weighted sum of square-boundary integrals over
the squares of nonzero winding: on both sides the coefficient of each
directed edge is the net signed traversal count, which equals the winding
difference of the two adjacent squares. The sum is finite because the
winding region is bounded. -/
theorem gridPathIntegral_eq_sum_windings (f : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    {L : List (ℤ × ℤ)} (hL : IsGridPath L) (hne : L ≠ [])
    (hcl : L.head? = L.getLast?) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ p ∈ S,
        windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) ≠ 0 ∧
          gridSquareCenter δ p ∉ gridPathTrace δ L) ∧
      gridPathIntegral f δ L =
        ∑ p ∈ S,
          (windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) : ℂ) *
            gridSquareBoundaryIntegral f δ p := by
  classical
  set γ : C(unitInterval, ℂ) := gridLoopCurve δ L with hγ_def
  set w : ℤ × ℤ → ℤ := fun p => windingNumber γ (gridSquareCenter δ p) with hw_def
  set prs : List ((ℤ × ℤ) × (ℤ × ℤ)) := L.zip L.tail with hprs_def
  -- ================================================================
  -- STAGE 0: coordinate helpers.
  -- ================================================================
  have hgre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hsegre : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  have hhalf_ne : ∀ n : ℤ, δ / 2 ≠ δ * n := by
    intro n heq
    have h' : δ * (1 / 2 : ℝ) = δ * (n : ℝ) := by linarith
    have h2 : (1 / 2 : ℝ) = (n : ℝ) := mul_left_cancel₀ (ne_of_gt hδ) h'
    have h3 : (2 * n : ℝ) = 1 := by linarith
    have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hcen_re : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_re, hgre]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((δ : ℂ) / 2 * (1 + Complex.I)).re = δ / 2 := by
      rw [hh]
      simp [Complex.mul_re]
    rw [h2]
  have hcen_im : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_im, hgim]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((δ : ℂ) / 2 * (1 + Complex.I)).im = δ / 2 := by
      rw [hh]
      simp [Complex.mul_im]
    rw [h2]
  -- (0) all square centers avoid all grid-path traces
  have hcenter : ∀ (p : ℤ × ℤ) (M : List (ℤ × ℤ)), IsGridPath M →
      ∀ x ∈ gridPathTrace δ M, gridSquareCenter δ p ≠ x := by
    intro p M
    induction M with
    | nil =>
      intro _ x hx
      simp [gridPathTrace] at hx
    | cons r M ih =>
      intro hpath x hx heq
      cases M with
      | nil =>
        have hxr : x = gridPoint δ r := hx
        have hre := congrArg Complex.re heq
        rw [hcen_re, hxr, hgre] at hre
        exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
      | cons s M' =>
        rcases hx with hseg | htr
        · have hadj : GridAdj r s := (List.isChain_cons_cons.mp hpath).1
          obtain ⟨u, v', hu, hv', huv, hxe⟩ := hseg
          rcases hadj with ⟨h1, -⟩ | ⟨-, h2⟩
          · have hxre : x.re = δ * r.1 := by
              rw [← hxe, hsegre, hgre, hgre, ← h1]
              have hcomb : u * (δ * (r.1 : ℝ)) + v' * (δ * (r.1 : ℝ)) =
                  (u + v') * (δ * r.1) := by ring
              rw [hcomb, huv, one_mul]
            have hre := congrArg Complex.re heq
            rw [hcen_re, hxre] at hre
            exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
          · have hxim : x.im = δ * r.2 := by
              rw [← hxe, hsegim, hgim, hgim, ← h2]
              have hcomb : u * (δ * (r.2 : ℝ)) + v' * (δ * (r.2 : ℝ)) =
                  (u + v') * (δ * r.2) := by ring
              rw [hcomb, huv, one_mul]
            have him := congrArg Complex.im heq
            rw [hcen_im, hxim] at him
            exact hhalf_ne (r.2 - p.2) (by push_cast; linarith)
        · exact ih (List.isChain_cons_cons.mp hpath).2 x htr heq
  have hgp_ne_cen : ∀ r p : ℤ × ℤ,
      gridPoint δ r - gridSquareCenter δ p ≠ 0 := by
    intro r p h
    have h1 := congrArg Complex.re h
    rw [Complex.sub_re, hgre, hcen_re, Complex.zero_re] at h1
    exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
  -- ================================================================
  -- STAGE 1: segment antisymmetry, LHS/RHS decompositions.
  -- ================================================================
  have hanti : ∀ a b : ℂ, segmentIntegral f b a = -segmentIntegral f a b := by
    intro a b
    have harg : ∀ t : ℝ, b + (1 - t) • (a - b) = a + t • (b - a) := by
      intro t
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hflip := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun s : ℝ => (a - b) * f (b + s • (a - b))) 1
    simp only [sub_self, sub_zero] at hflip
    have hcong : (∫ t in (0:ℝ)..1, (a - b) * f (b + (1 - t) • (a - b)))
        = ∫ t in (0:ℝ)..1, -((b - a) * f (a + t • (b - a))) :=
      intervalIntegral.integral_congr (fun t _ => by rw [harg t]; ring)
    calc segmentIntegral f b a
        = ∫ t in (0:ℝ)..1, (a - b) * f (b + t • (a - b)) := rfl
      _ = ∫ t in (0:ℝ)..1, (a - b) * f (b + (1 - t) • (a - b)) := hflip.symm
      _ = ∫ t in (0:ℝ)..1, -((b - a) * f (a + t • (b - a))) := hcong
      _ = -segmentIntegral f a b := by
          rw [intervalIntegral.integral_neg]; rfl
  have hLHS : ∀ M : List (ℤ × ℤ), gridPathIntegral f δ M =
      ((M.zip M.tail).map
        (fun e => segmentIntegral f (gridPoint δ e.1) (gridPoint δ e.2))).sum := by
    intro M
    induction M with
    | nil => simp [gridPathIntegral]
    | cons p M ih =>
      cases M with
      | nil => simp [gridPathIntegral]
      | cons q M' =>
        change segmentIntegral f (gridPoint δ p) (gridPoint δ q) +
            gridPathIntegral f δ (q :: M') = _
        rw [ih]
        simp only [List.tail_cons, List.zip_cons_cons, List.map_cons,
          List.sum_cons]
  -- consecutive-pair facts
  have hpair_adj : ∀ M : List (ℤ × ℤ), IsGridPath M →
      ∀ e ∈ M.zip M.tail, GridAdj e.1 e.2 := by
    intro M
    induction M with
    | nil => intro _ e he; simp at he
    | cons a M ih =>
      intro hM e he
      cases M with
      | nil => simp at he
      | cons b M' =>
        have hz : (a :: b :: M').zip (a :: b :: M').tail =
            (a, b) :: ((b :: M').zip M') := rfl
        rw [hz] at he
        rcases List.mem_cons.mp he with rfl | he'
        · exact (List.isChain_cons_cons.mp hM).1
        · refine ih (List.isChain_cons_cons.mp hM).2 e ?_
          show e ∈ (b :: M').zip (b :: M').tail
          exact he'
  have hpair_mem : ∀ (M : List (ℤ × ℤ)) (e : (ℤ × ℤ) × (ℤ × ℤ)),
      e ∈ M.zip M.tail → e.1 ∈ M ∧ e.2 ∈ M := by
    rintro M ⟨x, y⟩ he
    have h := List.of_mem_zip he
    exact ⟨h.1, List.mem_of_mem_tail h.2⟩
  have hpair_seg : ∀ (M : List (ℤ × ℤ)) (e : (ℤ × ℤ) × (ℤ × ℤ)),
      e ∈ M.zip M.tail →
      segment ℝ (gridPoint δ e.1) (gridPoint δ e.2) ⊆ gridPathTrace δ M := by
    intro M
    induction M with
    | nil => intro e he; simp at he
    | cons a M ih =>
      intro e he
      cases M with
      | nil => simp at he
      | cons b M' =>
        have hz : (a :: b :: M').zip (a :: b :: M').tail =
            (a, b) :: ((b :: M').zip M') := rfl
        rw [hz] at he
        rcases List.mem_cons.mp he with rfl | he'
        · intro z hz'
          exact Or.inl hz'
        · intro z hz'
          refine Or.inr (ih e ?_ hz')
          show e ∈ (b :: M').zip (b :: M').tail
          exact he'
  have hshape : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), GridAdj e.1 e.2 →
      (e.2 = (e.1.1 + 1, e.1.2)) ∨ (e.1 = (e.2.1 + 1, e.2.2)) ∨
      (e.2 = (e.1.1, e.1.2 + 1)) ∨ (e.1 = (e.2.1, e.2.2 + 1)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ he
    simp only [GridAdj] at he
    simp only [Prod.mk.injEq]
    omega
  have hseg_h : ∀ (i j : ℤ), ∀ x ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i + 1, j)),
      x.im = δ * j ∧ δ * i ≤ x.re ∧ x.re ≤ δ * (i + 1) := by
    intro i j x hx
    obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
    have hv1 : v ≤ 1 := by linarith
    have hre : x.re = δ * i + v * δ := by
      rw [← hxe, hsegre, hgre, hgre]
      push_cast
      linear_combination (δ * (i : ℝ)) * huv
    have him : x.im = δ * j := by
      rw [← hxe, hsegim, hgim, hgim]
      change u * (δ * (j : ℝ)) + v * (δ * (j : ℝ)) = δ * j
      linear_combination (δ * (j : ℝ)) * huv
    refine ⟨him, ?_, ?_⟩
    · rw [hre]
      nlinarith
    · rw [hre]
      nlinarith
  have hseg_v : ∀ (i j : ℤ), ∀ x ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i, j + 1)),
      x.re = δ * i ∧ δ * j ≤ x.im ∧ x.im ≤ δ * (j + 1) := by
    intro i j x hx
    obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
    have hv1 : v ≤ 1 := by linarith
    have him : x.im = δ * j + v * δ := by
      rw [← hxe, hsegim, hgim, hgim]
      push_cast
      linear_combination (δ * (j : ℝ)) * huv
    have hre : x.re = δ * i := by
      rw [← hxe, hsegre, hgre, hgre]
      change u * (δ * (i : ℝ)) + v * (δ * (i : ℝ)) = δ * i
      linear_combination (δ * (i : ℝ)) * huv
    refine ⟨hre, ?_, ?_⟩
    · rw [him]
      nlinarith
    · rw [him]
      nlinarith
  -- ================================================================
  -- STAGE 2: per-edge principal-log increments and the lift gluing.
  -- ================================================================
  have hslit : ∀ a b q : ℂ, (∀ x ∈ segment ℝ a b, q ≠ x) →
      (b - q) / (a - q) ∈ Complex.slitPlane := by
    intro a b q hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr fun h => hoff a (left_mem_segment ℝ a b) h.symm
    by_contra hns
    rw [Complex.mem_slitPlane_iff] at hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    set r : ℝ := ((b - q) / (a - q)).re with hr_def
    have hratio : (b - q) / (a - q) = ((r : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]
        exact him
    have hbq : b - q = ((r : ℝ) : ℂ) * (a - q) := by
      rw [← hratio, div_mul_cancel₀ _ haq]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hqseg : q ∈ segment ℝ a b := by
      refine ⟨-r / (1 - r), 1 / (1 - r), div_nonneg (by linarith) h1r.le,
        by positivity, ?_, ?_⟩
      · field_simp
        ring
      · rw [Complex.real_smul, Complex.real_smul]
        push_cast
        have hcne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
          have h0 : ((1 - r : ℝ) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt h1r)
          push_cast at h0
          exact h0
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          div_eq_iff hcne]
        linear_combination hbq
    exact hoff q hqseg rfl
  set inc : (ℤ × ℤ) × (ℤ × ℤ) → ℂ → ℂ := fun e q =>
    Complex.log ((gridPoint δ e.2 - q) / (gridPoint δ e.1 - q)) with hinc_def
  have hsegmem : ∀ (a b : ℂ) (s : unitInterval),
      segmentPath a b s ∈ segment ℝ a b := by
    intro a b s
    refine ⟨1 - (s : ℝ), (s : ℝ), by linarith [s.2.2], s.2.1, by ring, ?_⟩
    change (1 - (s : ℝ)) • a + (s : ℝ) • b = a + ((s : ℝ) : ℂ) * (b - a)
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hseglift : ∀ a b q : ℂ, (∀ x ∈ segment ℝ a b, q ≠ x) →
      ∃ g : C(unitInterval, ℂ),
        (∀ s : unitInterval, Complex.exp (g s) = segmentPath a b s - q) ∧
        g 1 - g 0 = Complex.log ((b - q) / (a - q)) ∧
        Complex.exp (g 1) = b - q := by
    intro a b q hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hoff a (left_mem_segment ℝ a b)))
    have hgmem : ∀ s : unitInterval,
        (segmentPath a b s - q) / (a - q) ∈ Complex.slitPlane := by
      intro s
      refine hslit a (segmentPath a b s) q ?_
      intro x hx
      exact hoff x ((convex_segment a b).segment_subset
        (left_mem_segment ℝ a b) (hsegmem a b s) hx)
    have hgcont : Continuous fun s : unitInterval =>
        (segmentPath a b s - q) / (a - q) :=
      ((segmentPath a b).continuous.sub continuous_const).div_const _
    have hgcont' : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath a b s - q) / (a - q)) +
          Complex.log (a - q) := by
      refine Continuous.add ?_ continuous_const
      rw [continuous_iff_continuousAt]
      intro s
      exact hgcont.continuousAt.clog (hgmem s)
    refine ⟨⟨fun s => Complex.log ((segmentPath a b s - q) / (a - q)) +
      Complex.log (a - q), hgcont'⟩, ?_, ?_, ?_⟩
    · intro s
      change Complex.exp (Complex.log ((segmentPath a b s - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [Complex.exp_add, Complex.exp_log haq,
        Complex.exp_log (Complex.slitPlane_ne_zero (hgmem s)),
        div_mul_cancel₀ _ haq]
    · change (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) - (Complex.log ((segmentPath a b 0 - q) /
          (a - q)) + Complex.log (a - q)) = _
      rw [(segmentPath a b).source, (segmentPath a b).target,
        div_self haq, Complex.log_one]
      ring
    · change Complex.exp (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [(segmentPath a b).target, Complex.exp_add, Complex.exp_log haq]
      have hbq : b - q ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hoff b (right_mem_segment ℝ a b)))
      rw [Complex.exp_log (by
        exact div_ne_zero hbq haq), div_mul_cancel₀ _ haq]
  have hliftInd : ∀ (Lst : List (ℤ × ℤ)) (p : ℤ × ℤ),
      IsGridPath (p :: Lst) →
      ∀ q : ℂ, (∀ x ∈ gridPathTrace δ (p :: Lst), q ≠ x) →
      ∃ Lf : C(unitInterval, ℂ),
        IsLogLiftOf Lf
          (shiftedCurve (gridPathRealize δ p Lst).toContinuousMap q) ∧
        Lf 1 - Lf 0 = (((p :: Lst).zip Lst).map (fun e => inc e q)).sum := by
    intro Lst
    induction Lst with
    | nil =>
      intro p _ q hoff
      have hqp : q ≠ gridPoint δ p := hoff _ rfl
      refine ⟨ContinuousMap.const unitInterval
        (Complex.log (gridPoint δ p - q)), ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        rw [Complex.exp_log (sub_ne_zero.mpr (Ne.symm hqp))]
        change gridPoint δ p - q = (Path.refl (gridPoint δ p)) t - q
        simp
      · simp
    | cons r M ih =>
      intro p hpath q hoff
      have htail : IsGridPath (r :: M) :=
        (List.isChain_cons_cons.mp hpath).2
      have hofftrace : ∀ x ∈ gridPathTrace δ (r :: M), q ≠ x :=
        fun x hx => hoff x (Or.inr hx)
      have hoffseg : ∀ x ∈ segment ℝ (gridPoint δ p) (gridPoint δ r),
          q ≠ x := fun x hx => hoff x (Or.inl hx)
      obtain ⟨Lrest, hLrest, hLrest_inc⟩ := ih r htail q hofftrace
      obtain ⟨fseg, hfseg_lift, hfseg_inc, hfseg1⟩ :=
        hseglift (gridPoint δ p) (gridPoint δ r) q hoffseg
      have hbq : gridPoint δ r - q ≠ 0 := by
        rw [← hfseg1]
        exact Complex.exp_ne_zero _
      have hLrest0 : Complex.exp (Lrest 0) = gridPoint δ r - q := by
        have h := hLrest 0
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] at h
        rw [h, (gridPathRealize δ r M).source]
      have hexpc : Complex.exp (fseg 1 - Lrest 0) = 1 := by
        rw [Complex.exp_sub, hfseg1, hLrest0, div_self hbq]
      have hstart : (Lrest + ContinuousMap.const unitInterval
          (fseg 1 - Lrest 0)) 0 = fseg 1 := by
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        ring
      have hLrest'_lift : ∀ t, Complex.exp ((Lrest +
          ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) t) =
          (gridPathRealize δ r M) t - q := by
        intro t
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [Complex.exp_add, hexpc, mul_one]
        have h := hLrest t
        simpa only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] using h
      refine ⟨((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
        (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
          hstart, rfl⟩ : Path (fseg 1) ((Lrest +
            ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
          ).toContinuousMap, ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        change Complex.exp _ =
          ((segmentPath (gridPoint δ p) (gridPoint δ r)).trans
            (gridPathRealize δ r M)) t - q
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs with ht
        · exact hfseg_lift _
        · exact hLrest'_lift _
      · have h0 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 0 = fseg 0 := by simp
        have h1 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 1 = (Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1 := by
          simp
        rw [h0, h1]
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ← hLrest_inc]
        have hincpr : inc (p, r) q =
            Complex.log ((gridPoint δ r - q) / (gridPoint δ p - q)) := rfl
        rw [hincpr, ← hfseg_inc]
        ring
  have hlift : ∀ (M : List (ℤ × ℤ)), IsGridPath M → M ≠ [] →
      M.head? = M.getLast? →
      ∀ q : ℂ, (∀ x ∈ gridPathTrace δ M, q ≠ x) →
      (2 * Real.pi * Complex.I) * windingNumber (gridLoopCurve δ M) q =
        ((M.zip M.tail).map (fun e => inc e q)).sum := by
    intro M hM hMne hMcl q hoff
    obtain ⟨p, M', rfl⟩ := List.exists_cons_of_ne_nil hMne
    obtain ⟨Lf, hLf, hLf_inc⟩ := hliftInd M' p hM q hoff
    have hclosed : gridLoopCurve δ (p :: M') 0 = gridLoopCurve δ (p :: M') 1 :=
      gridLoopCurve_closed (by simp) hMcl
    have hrange : Set.range (gridLoopCurve δ (p :: M')) =
        gridPathTrace δ (p :: M') := range_gridLoopCurve hδ hM (by simp)
    have hq : ∀ t : unitInterval, gridLoopCurve δ (p :: M') t ≠ q := by
      intro t heq
      exact hoff _ (hrange ▸ Set.mem_range_self t) heq.symm
    have hspec := windingNumber_spec hclosed hq hLf
    rw [← hspec]
    exact hLf_inc
  -- ================================================================
  -- STAGE 3: list-sum utilities and telescoping over the closed loop.
  -- ================================================================
  have hmapsub : ∀ (P : List ((ℤ × ℤ) × (ℤ × ℤ)))
      (g₁ g₂ : (ℤ × ℤ) × (ℤ × ℤ) → ℂ),
      (P.map (fun x => g₁ x - g₂ x)).sum = (P.map g₁).sum - (P.map g₂).sum := by
    intro P g₁ g₂
    induction P with
    | nil => simp
    | cons e P ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  have hmapc : ∀ (P : List ((ℤ × ℤ) × (ℤ × ℤ)))
      (g : (ℤ × ℤ) × (ℤ × ℤ) → ℂ) (n : (ℤ × ℤ) × (ℤ × ℤ) → ℤ) (c : ℂ),
      (∀ x ∈ P, g x = c * n x) →
      (P.map g).sum = c * ((P.map n).sum : ℤ) := by
    intro P g n c
    induction P with
    | nil => intro _; simp
    | cons e P ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        h e List.mem_cons_self]
      push_cast
      ring
  have hlastq : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (r :: M).getLast? = some (gridLast r M) := by
    intro r M
    induction M generalizing r with
    | nil => simp [gridLast]
    | cons q M ih =>
      rw [List.getLast?_cons_cons, ih]
      rfl
  have htele : ∀ (G : ℤ × ℤ → ℂ) (x : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (((x :: M).zip M).map (fun e => G e.2 - G e.1)).sum =
        G (gridLast x M) - G x := by
    intro G x M
    induction M generalizing x with
    | nil => simp [gridLast]
    | cons y M' ih =>
      have hz : ((x :: y :: M').zip (y :: M')) =
          (x, y) :: ((y :: M').zip M') := rfl
      rw [hz, List.map_cons, List.sum_cons, ih y]
      change G y - G x + (G (gridLast y M') - G y) =
        G (gridLast x (y :: M')) - G x
      have hgl : gridLast x (y :: M') = gridLast y M' := rfl
      rw [hgl]
      ring
  have hteleL : ∀ G : ℤ × ℤ → ℂ,
      (prs.map (fun e => G e.2 - G e.1)).sum = 0 := by
    intro G
    obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h := htele G p L'
    have hp : p = gridLast p L' := by
      have h2 := hcl
      rw [List.head?_cons, hlastq] at h2
      exact Option.some.inj h2
    rw [hprs_def]
    change (((p :: L').zip L').map (fun e => G e.2 - G e.1)).sum = 0
    rw [h, ← hp, sub_self]
  -- signed traversal indicator of a canonical directed edge
  set ind : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) → ℤ := fun E e =>
    if e = E then 1 else if e = (E.2, E.1) then -1 else 0 with hind_def
  -- ================================================================
  -- STAGE 4: the jump engine.
  -- ================================================================
  -- division shortcuts for the crossing-edge Gaussian ratios
  have hdivI : ∀ x y : ℂ, y ≠ 0 → x = Complex.I * y → x / y = Complex.I := by
    intro x y hy hxy
    rw [hxy, mul_div_assoc, div_self hy, mul_one]
  have hdivnI : ∀ x y : ℂ, y ≠ 0 → x = -Complex.I * y → x / y = -Complex.I := by
    intro x y hy hxy
    rw [hxy, mul_div_assoc, div_self hy, mul_one]
  have hdivI' : ∀ x y : ℂ, x ≠ 0 → y = Complex.I * x → x / y = -Complex.I := by
    intro x y hx hxy
    rw [hxy, div_mul_eq_div_div_swap, div_self hx, one_div, Complex.inv_I]
  have hdivnI' : ∀ x y : ℂ, x ≠ 0 → y = -Complex.I * x → x / y = Complex.I := by
    intro x y hx hxy
    rw [hxy, div_mul_eq_div_div_swap, div_self hx, one_div, inv_neg,
      Complex.inv_I, neg_neg]
  -- the defect vanishes on edges avoiding the branch cut [cm, cp]
  have hD_zero : ∀ A B cp cm : ℂ,
      (∀ x ∈ segment ℝ A B, cp ≠ x) →
      (∀ x ∈ segment ℝ A B, cm ≠ x) →
      (∀ z ∈ segment ℝ A B, ∀ y ∈ segment ℝ cm cp, z ≠ y) →
      Complex.log ((B - cp) / (A - cp)) - Complex.log ((B - cm) / (A - cm)) -
        (Complex.log ((B - cp) / (B - cm)) -
          Complex.log ((A - cp) / (A - cm))) = 0 := by
    intro A B cp cm hcp hcm hcut
    have hAcp : A - cp ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hcp A (left_mem_segment ℝ A B)))
    have hAcm : A - cm ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hcm A (left_mem_segment ℝ A B)))
    have hz_ne_cp : ∀ s : unitInterval, segmentPath A B s - cp ≠ 0 := fun s =>
      sub_ne_zero.mpr (Ne.symm (hcp _ (hsegmem A B s)))
    have hz_ne_cm : ∀ s : unitInterval, segmentPath A B s - cm ≠ 0 := fun s =>
      sub_ne_zero.mpr (Ne.symm (hcm _ (hsegmem A B s)))
    have humem : ∀ s : unitInterval,
        (segmentPath A B s - cp) / (A - cp) ∈ Complex.slitPlane := by
      intro s
      refine hslit A (segmentPath A B s) cp ?_
      intro x hx
      exact hcp x ((convex_segment A B).segment_subset
        (left_mem_segment ℝ A B) (hsegmem A B s) hx)
    have hvmem : ∀ s : unitInterval,
        (segmentPath A B s - cm) / (A - cm) ∈ Complex.slitPlane := by
      intro s
      refine hslit A (segmentPath A B s) cm ?_
      intro x hx
      exact hcm x ((convex_segment A B).segment_subset
        (left_mem_segment ℝ A B) (hsegmem A B s) hx)
    have hwmem : ∀ s : unitInterval,
        (segmentPath A B s - cp) / (segmentPath A B s - cm) ∈
          Complex.slitPlane := by
      intro s
      have h1 : (cp - segmentPath A B s) / (cm - segmentPath A B s) ∈
          Complex.slitPlane :=
        hslit cm cp (segmentPath A B s)
          (fun y hy => hcut _ (hsegmem A B s) y hy)
      have h2 : (segmentPath A B s - cp) / (segmentPath A B s - cm) =
          (cp - segmentPath A B s) / (cm - segmentPath A B s) := by
        rw [← neg_sub cp (segmentPath A B s), ← neg_sub cm (segmentPath A B s),
          neg_div_neg_eq]
      rw [h2]
      exact h1
    have hφcont : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath A B s - cp) / (A - cp)) -
          Complex.log ((segmentPath A B s - cm) / (A - cm)) -
          Complex.log ((segmentPath A B s - cp) / (segmentPath A B s - cm)) +
          Complex.log ((A - cp) / (A - cm)) := by
      have hc1 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cp) / (A - cp)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (((segmentPath A B).continuous.sub
          continuous_const).div_const _).continuousAt.clog (humem s)
      have hc2 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cm) / (A - cm)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (((segmentPath A B).continuous.sub
          continuous_const).div_const _).continuousAt.clog (hvmem s)
      have hc3 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cp) /
            (segmentPath A B s - cm)) := by
        rw [continuous_iff_continuousAt]
        intro s
        refine ContinuousAt.clog ?_ (hwmem s)
        exact (((segmentPath A B).continuous.sub continuous_const).div
          ((segmentPath A B).continuous.sub continuous_const)
          (fun t => hz_ne_cm t)).continuousAt
      exact ((hc1.sub hc2).sub hc3).add continuous_const
    set φ : C(unitInterval, ℂ) := ⟨fun s =>
      Complex.log ((segmentPath A B s - cp) / (A - cp)) -
        Complex.log ((segmentPath A B s - cm) / (A - cm)) -
        Complex.log ((segmentPath A B s - cp) / (segmentPath A B s - cm)) +
        Complex.log ((A - cp) / (A - cm)), hφcont⟩ with hφ_def
    have hφlift : IsLogLiftOf φ (ContinuousMap.const unitInterval 1) := by
      intro s
      simp only [hφ_def, ContinuousMap.coe_mk, ContinuousMap.const_apply]
      rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub,
        Complex.exp_log (div_ne_zero (hz_ne_cp s) hAcp),
        Complex.exp_log (div_ne_zero (hz_ne_cm s) hAcm),
        Complex.exp_log (div_ne_zero (hz_ne_cp s) (hz_ne_cm s)),
        Complex.exp_log (div_ne_zero hAcp hAcm)]
      field_simp [hz_ne_cp s, hz_ne_cm s, hAcp, hAcm]
    have h0lift : IsLogLiftOf (ContinuousMap.const unitInterval 0)
        (ContinuousMap.const unitInterval 1) := by
      intro s
      simp
    have hincr := isLogLiftOf_increment_eq hφlift h0lift
    have hφ0 : φ 0 = 0 := by
      simp only [hφ_def, ContinuousMap.coe_mk]
      rw [(segmentPath A B).source, div_self hAcp, div_self hAcm,
        Complex.log_one]
      ring
    have hφ1 : φ 1 = Complex.log ((B - cp) / (A - cp)) -
        Complex.log ((B - cm) / (A - cm)) -
        Complex.log ((B - cp) / (B - cm)) +
        Complex.log ((A - cp) / (A - cm)) := by
      simp only [hφ_def, ContinuousMap.coe_mk]
      rw [(segmentPath A B).target]
    rw [hφ0, hφ1] at hincr
    simp only [ContinuousMap.const_apply, sub_zero, sub_self] at hincr
    linear_combination hincr
  -- the engine: winding difference across an edge = signed traversal count
  have hENGINE : ∀ (t₀ h₀ : ℤ × ℤ) (cp cm : ℂ),
      (∀ x ∈ gridPathTrace δ L, cp ≠ x) →
      (∀ x ∈ gridPathTrace δ L, cm ≠ x) →
      gridPoint δ t₀ - cp ≠ 0 → gridPoint δ t₀ - cm ≠ 0 →
      gridPoint δ h₀ - cp ≠ 0 → gridPoint δ h₀ - cm ≠ 0 →
      gridPoint δ h₀ - cp = Complex.I * (gridPoint δ t₀ - cp) →
      gridPoint δ h₀ - cm = -Complex.I * (gridPoint δ t₀ - cm) →
      gridPoint δ t₀ - cp = Complex.I * (gridPoint δ t₀ - cm) →
      gridPoint δ h₀ - cp = -Complex.I * (gridPoint δ h₀ - cm) →
      (∀ e ∈ prs, e ≠ (t₀, h₀) → e ≠ (h₀, t₀) →
        ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
          ∀ y ∈ segment ℝ cm cp, z ≠ y) →
      (windingNumber γ cp : ℤ) - windingNumber γ cm =
        (prs.map (ind (t₀, h₀))).sum := by
    intro t₀ h₀ cp cm hcpoff hcmoff hAcp hAcm hBcp hBcm hr1 hr2 hr3 hr4 hcut
    set G : ℤ × ℤ → ℂ := fun r =>
      Complex.log ((gridPoint δ r - cp) / (gridPoint δ r - cm)) with hG_def
    -- the two crossed-edge defect values
    have hDcan : inc (t₀, h₀) cp - inc (t₀, h₀) cm - (G h₀ - G t₀) =
        2 * Real.pi * Complex.I := by
      have h1 : inc (t₀, h₀) cp = Complex.log Complex.I := by
        change Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ t₀ - cp)) = _
        rw [hdivI _ _ hAcp hr1]
      have h2 : inc (t₀, h₀) cm = Complex.log (-Complex.I) := by
        change Complex.log ((gridPoint δ h₀ - cm) / (gridPoint δ t₀ - cm)) = _
        rw [hdivnI _ _ hAcm hr2]
      have h3 : G t₀ = Complex.log Complex.I := by
        change Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ t₀ - cm)) = _
        rw [hdivI _ _ hAcm hr3]
      have h4 : G h₀ = Complex.log (-Complex.I) := by
        change Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI _ _ hBcm hr4]
      rw [h1, h2, h3, h4, Complex.log_I, Complex.log_neg_I]
      ring
    have hDswap : inc (h₀, t₀) cp - inc (h₀, t₀) cm - (G t₀ - G h₀) =
        -(2 * Real.pi * Complex.I) := by
      have h1 : inc (h₀, t₀) cp = Complex.log (-Complex.I) := by
        change Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ h₀ - cp)) = _
        rw [hdivI' _ _ hAcp hr1]
      have h2 : inc (h₀, t₀) cm = Complex.log Complex.I := by
        change Complex.log ((gridPoint δ t₀ - cm) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI' _ _ hAcm hr2]
      have h3 : G t₀ = Complex.log Complex.I := by
        change Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ t₀ - cm)) = _
        rw [hdivI _ _ hAcm hr3]
      have h4 : G h₀ = Complex.log (-Complex.I) := by
        change Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI _ _ hBcm hr4]
      rw [h1, h2, h3, h4, Complex.log_I, Complex.log_neg_I]
      ring
    -- the crossed edge has distinct endpoints
    have hth : t₀ ≠ h₀ := by
      intro h
      subst h
      have h1 : (1 - Complex.I) * (gridPoint δ t₀ - cp) = 0 := by
        linear_combination hr1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · have h3 := congrArg Complex.re h2
        simp [Complex.sub_re] at h3
      · exact hAcp h2
    -- pointwise defect values along the loop
    have hDval : ∀ e ∈ prs, inc e cp - inc e cm - (G e.2 - G e.1) =
        (2 * Real.pi * Complex.I) * ((ind (t₀, h₀) e : ℤ) : ℂ) := by
      intro e he
      by_cases hcan : e = (t₀, h₀)
      · subst hcan
        have hival : ind (t₀, h₀) (t₀, h₀) = 1 := by
          simp [hind_def]
        rw [hival]
        change inc (t₀, h₀) cp - inc (t₀, h₀) cm - (G h₀ - G t₀) =
          2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ)
        rw [hDcan, Int.cast_one, mul_one]
      · by_cases hswap : e = (h₀, t₀)
        · subst hswap
          have hne2 : ((h₀, t₀) : (ℤ × ℤ) × (ℤ × ℤ)) ≠ (t₀, h₀) :=
            fun hh => hth ((Prod.ext_iff.mp hh).1).symm
          have hival : ind (t₀, h₀) (h₀, t₀) = -1 := by
            simp only [hind_def]
            rw [ite_eq_right hne2]
            simp
          rw [hival]
          change inc (h₀, t₀) cp - inc (h₀, t₀) cm - (G t₀ - G h₀) =
            2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
          rw [hDswap]
          push_cast
          ring
        · have hival : ind (t₀, h₀) e = 0 := by
            simp only [hind_def]
            rw [ite_eq_right hcan, ite_eq_right (fun hh => hswap hh)]
          rw [hival, Int.cast_zero, mul_zero]
          have hcpoffseg : ∀ x ∈ segment ℝ (gridPoint δ e.1)
              (gridPoint δ e.2), cp ≠ x :=
            fun x hx => hcpoff x (hpair_seg L e he hx)
          have hcmoffseg : ∀ x ∈ segment ℝ (gridPoint δ e.1)
              (gridPoint δ e.2), cm ≠ x :=
            fun x hx => hcmoff x (hpair_seg L e he hx)
          exact hD_zero (gridPoint δ e.1) (gridPoint δ e.2) cp cm
            hcpoffseg hcmoffseg (hcut e he hcan hswap)
    -- sum the defects and cancel 2πi
    have h1 : (prs.map (fun e => inc e cp - inc e cm - (G e.2 - G e.1))).sum =
        (2 * Real.pi * Complex.I) * ((prs.map (ind (t₀, h₀))).sum : ℤ) :=
      hmapc prs _ _ _ hDval
    have h2 : (prs.map (fun e => inc e cp - inc e cm - (G e.2 - G e.1))).sum =
        (2 * Real.pi * Complex.I) * (windingNumber γ cp : ℤ) -
        (2 * Real.pi * Complex.I) * (windingNumber γ cm : ℤ) := by
      rw [hmapsub prs (fun e => inc e cp - inc e cm) (fun e => G e.2 - G e.1),
        hmapsub prs (fun e => inc e cp) (fun e => inc e cm), hteleL G,
        sub_zero, hprs_def, hγ_def]
      rw [← hlift L hL hne hcl cp hcpoff, ← hlift L hL hne hcl cm hcmoff]
    have h4 : (((windingNumber γ cp : ℤ) - windingNumber γ cm : ℤ) : ℂ) =
        (((prs.map (ind (t₀, h₀))).sum : ℤ) : ℂ) := by
      have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      apply mul_left_cancel₀ h2πi
      rw [Int.cast_sub, mul_sub, ← h2]
      exact h1
    exact_mod_cast h4
  -- cut segments: coordinates
  have hcutH : ∀ v : ℤ × ℤ, ∀ y ∈ segment ℝ
      (gridSquareCenter δ (v.1, v.2 - 1)) (gridSquareCenter δ v),
      y.re = δ * v.1 + δ / 2 ∧
        δ * v.2 - δ / 2 ≤ y.im ∧ y.im ≤ δ * v.2 + δ / 2 := by
    intro v y hy
    obtain ⟨u, u', hu, hu', huu, hye⟩ := hy
    have hare : (gridSquareCenter δ (v.1, v.2 - 1)).re = δ * v.1 + δ / 2 :=
      hcen_re _
    have haim : (gridSquareCenter δ (v.1, v.2 - 1)).im = δ * v.2 - δ / 2 := by
      rw [hcen_im]
      change δ * ((v.2 - 1 : ℤ) : ℝ) + δ / 2 = δ * v.2 - δ / 2
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [← hye, hsegre, hare, hcen_re]
      linear_combination (δ * (v.1 : ℝ) + δ / 2) * huu
    · rw [← hye, hsegim, haim, hcen_im]
      have hu1 : u = 1 - u' := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu']
    · rw [← hye, hsegim, haim, hcen_im]
      have hu1 : u' = 1 - u := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu]
  have hcutU : ∀ v : ℤ × ℤ, ∀ y ∈ segment ℝ
      (gridSquareCenter δ v) (gridSquareCenter δ (v.1 - 1, v.2)),
      y.im = δ * v.2 + δ / 2 ∧
        δ * v.1 - δ / 2 ≤ y.re ∧ y.re ≤ δ * v.1 + δ / 2 := by
    intro v y hy
    obtain ⟨u, u', hu, hu', huu, hye⟩ := hy
    have hbre : (gridSquareCenter δ (v.1 - 1, v.2)).re = δ * v.1 - δ / 2 := by
      rw [hcen_re]
      change δ * ((v.1 - 1 : ℤ) : ℝ) + δ / 2 = δ * v.1 - δ / 2
      push_cast
      ring
    have hbim : (gridSquareCenter δ (v.1 - 1, v.2)).im = δ * v.2 + δ / 2 :=
      hcen_im _
    refine ⟨?_, ?_, ?_⟩
    · rw [← hye, hsegim, hbim, hcen_im]
      linear_combination (δ * (v.2 : ℝ) + δ / 2) * huu
    · rw [← hye, hsegre, hbre, hcen_re]
      have hu1 : u' = 1 - u := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu]
    · rw [← hye, hsegre, hbre, hcen_re]
      have hu1 : u = 1 - u' := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu']
  -- cut avoidance: the cut only crosses the grid inside the crossed edge
  have havoidH : ∀ v : ℤ × ℤ, ∀ e ∈ prs,
      e ≠ (v, (v.1 + 1, v.2)) → e ≠ ((v.1 + 1, v.2), v) →
      ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
        ∀ y ∈ segment ℝ (gridSquareCenter δ (v.1, v.2 - 1))
          (gridSquareCenter δ v), z ≠ y := by
    intro v e he hecan heswap z hz y hy heq
    obtain ⟨hyre, hyim1, hyim2⟩ := hcutH v y hy
    have hadj := hpair_adj L hL e he
    rcases hshape e hadj with h | h | h | h
    · -- canonical horizontal edge based at e.1
      rw [h] at hz
      obtain ⟨hzim, hzre1, hzre2⟩ := hseg_h e.1.1 e.1.2 z hz
      have him1 : δ * (v.2 : ℝ) - δ / 2 ≤ δ * e.1.2 := by
        rw [← hzim, heq]; exact hyim1
      have him2 : δ * (e.1.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hzim, heq]; exact hyim2
      have hre1 : δ * (e.1.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hyre, ← heq]; exact hzre1
      have hre2 : δ * v.1 + δ / 2 ≤ δ * ((e.1.1 : ℝ) + 1) := by
        rw [← hyre, ← heq]; exact hzre2
      have hj : e.1.2 = v.2 := by
        have a1 : (2 * v.2 - 1 : ℝ) ≤ 2 * e.1.2 := by nlinarith
        have a2 : (2 * e.1.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have b1 : (2 * v.2 - 1 : ℤ) ≤ 2 * e.1.2 := by exact_mod_cast a1
        have b2 : (2 * e.1.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a2
        omega
      have hi : e.1.1 = v.1 := by
        have a1 : (2 * e.1.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have a2 : (2 * v.1 + 1 : ℝ) ≤ 2 * e.1.1 + 2 := by nlinarith
        have b1 : (2 * e.1.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.1 + 1 : ℤ) ≤ 2 * e.1.1 + 2 := by exact_mod_cast a2
        omega
      exact hecan (Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨hi, hj⟩,
        by rw [h, hi, hj]⟩)
    · -- reversed horizontal edge based at e.2
      rw [h, segment_symm] at hz
      obtain ⟨hzim, hzre1, hzre2⟩ := hseg_h e.2.1 e.2.2 z hz
      have him1 : δ * (v.2 : ℝ) - δ / 2 ≤ δ * e.2.2 := by
        rw [← hzim, heq]; exact hyim1
      have him2 : δ * (e.2.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hzim, heq]; exact hyim2
      have hre1 : δ * (e.2.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hyre, ← heq]; exact hzre1
      have hre2 : δ * v.1 + δ / 2 ≤ δ * ((e.2.1 : ℝ) + 1) := by
        rw [← hyre, ← heq]; exact hzre2
      have hj : e.2.2 = v.2 := by
        have a1 : (2 * v.2 - 1 : ℝ) ≤ 2 * e.2.2 := by nlinarith
        have a2 : (2 * e.2.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have b1 : (2 * v.2 - 1 : ℤ) ≤ 2 * e.2.2 := by exact_mod_cast a1
        have b2 : (2 * e.2.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a2
        omega
      have hi : e.2.1 = v.1 := by
        have a1 : (2 * e.2.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have a2 : (2 * v.1 + 1 : ℝ) ≤ 2 * e.2.1 + 2 := by nlinarith
        have b1 : (2 * e.2.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.1 + 1 : ℤ) ≤ 2 * e.2.1 + 2 := by exact_mod_cast a2
        omega
      exact heswap (Prod.ext_iff.mpr ⟨by rw [h, hi, hj],
        Prod.ext_iff.mpr ⟨hi, hj⟩⟩)
    · -- vertical edges never meet the horizontal-jump cut
      rw [h] at hz
      obtain ⟨hzre, -, -⟩ := hseg_v e.1.1 e.1.2 z hz
      have hh : δ * (e.1.1 : ℝ) = δ * v.1 + δ / 2 := by
        rw [← hzre, heq, hyre]
      exact hhalf_ne (e.1.1 - v.1) (by push_cast; linarith)
    · rw [h, segment_symm] at hz
      obtain ⟨hzre, -, -⟩ := hseg_v e.2.1 e.2.2 z hz
      have hh : δ * (e.2.1 : ℝ) = δ * v.1 + δ / 2 := by
        rw [← hzre, heq, hyre]
      exact hhalf_ne (e.2.1 - v.1) (by push_cast; linarith)
  have havoidU : ∀ v : ℤ × ℤ, ∀ e ∈ prs,
      e ≠ (v, (v.1, v.2 + 1)) → e ≠ ((v.1, v.2 + 1), v) →
      ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
        ∀ y ∈ segment ℝ (gridSquareCenter δ v)
          (gridSquareCenter δ (v.1 - 1, v.2)), z ≠ y := by
    intro v e he hecan heswap z hz y hy heq
    obtain ⟨hyim, hyre1, hyre2⟩ := hcutU v y hy
    have hadj := hpair_adj L hL e he
    rcases hshape e hadj with h | h | h | h
    · -- horizontal edges never meet the vertical-jump cut
      rw [h] at hz
      obtain ⟨hzim, -, -⟩ := hseg_h e.1.1 e.1.2 z hz
      have hh : δ * (e.1.2 : ℝ) = δ * v.2 + δ / 2 := by
        rw [← hzim, heq, hyim]
      exact hhalf_ne (e.1.2 - v.2) (by push_cast; linarith)
    · rw [h, segment_symm] at hz
      obtain ⟨hzim, -, -⟩ := hseg_h e.2.1 e.2.2 z hz
      have hh : δ * (e.2.2 : ℝ) = δ * v.2 + δ / 2 := by
        rw [← hzim, heq, hyim]
      exact hhalf_ne (e.2.2 - v.2) (by push_cast; linarith)
    · -- canonical vertical edge based at e.1
      rw [h] at hz
      obtain ⟨hzre, hzim1, hzim2⟩ := hseg_v e.1.1 e.1.2 z hz
      have hre1 : δ * (v.1 : ℝ) - δ / 2 ≤ δ * e.1.1 := by
        rw [← hzre, heq]; exact hyre1
      have hre2 : δ * (e.1.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hzre, heq]; exact hyre2
      have him1 : δ * (e.1.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hyim, ← heq]; exact hzim1
      have him2 : δ * v.2 + δ / 2 ≤ δ * ((e.1.2 : ℝ) + 1) := by
        rw [← hyim, ← heq]; exact hzim2
      have hi : e.1.1 = v.1 := by
        have a1 : (2 * v.1 - 1 : ℝ) ≤ 2 * e.1.1 := by nlinarith
        have a2 : (2 * e.1.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have b1 : (2 * v.1 - 1 : ℤ) ≤ 2 * e.1.1 := by exact_mod_cast a1
        have b2 : (2 * e.1.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a2
        omega
      have hj : e.1.2 = v.2 := by
        have a1 : (2 * e.1.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have a2 : (2 * v.2 + 1 : ℝ) ≤ 2 * e.1.2 + 2 := by nlinarith
        have b1 : (2 * e.1.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.2 + 1 : ℤ) ≤ 2 * e.1.2 + 2 := by exact_mod_cast a2
        omega
      exact hecan (Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨hi, hj⟩,
        by rw [h, hi, hj]⟩)
    · -- reversed vertical edge based at e.2
      rw [h, segment_symm] at hz
      obtain ⟨hzre, hzim1, hzim2⟩ := hseg_v e.2.1 e.2.2 z hz
      have hre1 : δ * (v.1 : ℝ) - δ / 2 ≤ δ * e.2.1 := by
        rw [← hzre, heq]; exact hyre1
      have hre2 : δ * (e.2.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hzre, heq]; exact hyre2
      have him1 : δ * (e.2.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hyim, ← heq]; exact hzim1
      have him2 : δ * v.2 + δ / 2 ≤ δ * ((e.2.2 : ℝ) + 1) := by
        rw [← hyim, ← heq]; exact hzim2
      have hi : e.2.1 = v.1 := by
        have a1 : (2 * v.1 - 1 : ℝ) ≤ 2 * e.2.1 := by nlinarith
        have a2 : (2 * e.2.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have b1 : (2 * v.1 - 1 : ℤ) ≤ 2 * e.2.1 := by exact_mod_cast a1
        have b2 : (2 * e.2.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a2
        omega
      have hj : e.2.2 = v.2 := by
        have a1 : (2 * e.2.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have a2 : (2 * v.2 + 1 : ℝ) ≤ 2 * e.2.2 + 2 := by nlinarith
        have b1 : (2 * e.2.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.2 + 1 : ℤ) ≤ 2 * e.2.2 + 2 := by exact_mod_cast a2
        omega
      exact heswap (Prod.ext_iff.mpr ⟨by rw [h, hi, hj],
        Prod.ext_iff.mpr ⟨hi, hj⟩⟩)
  -- the two jump lemmas
  have hjumpR : ∀ v : ℤ × ℤ, (w v : ℤ) - w (v.1, v.2 - 1) =
      (prs.map (ind (v, (v.1 + 1, v.2)))).sum := by
    intro v
    have hr1 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ v =
        Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr2 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ (v.1, v.2 - 1) =
        -Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr3 : gridPoint δ v - gridSquareCenter δ v =
        Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination (-(δ : ℂ) / 2) * Complex.I_sq
    have hr4 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ v =
        -Complex.I *
          (gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    exact hENGINE v (v.1 + 1, v.2) (gridSquareCenter δ v)
      (gridSquareCenter δ (v.1, v.2 - 1)) (hcenter v L hL)
      (hcenter (v.1, v.2 - 1) L hL) (hgp_ne_cen v v)
      (hgp_ne_cen v (v.1, v.2 - 1)) (hgp_ne_cen (v.1 + 1, v.2) v)
      (hgp_ne_cen (v.1 + 1, v.2) (v.1, v.2 - 1)) hr1 hr2 hr3 hr4 (havoidH v)
  have hjumpU : ∀ v : ℤ × ℤ, (w (v.1 - 1, v.2) : ℤ) - w v =
      (prs.map (ind (v, (v.1, v.2 + 1)))).sum := by
    intro v
    have hr1 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ (v.1 - 1, v.2) =
        Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1 - 1, v.2)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr2 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ v =
        -Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination (-(δ : ℂ) / 2) * Complex.I_sq
    have hr3 : gridPoint δ v - gridSquareCenter δ (v.1 - 1, v.2) =
        Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr4 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ (v.1 - 1, v.2) =
        -Complex.I *
          (gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    exact hENGINE v (v.1, v.2 + 1) (gridSquareCenter δ (v.1 - 1, v.2))
      (gridSquareCenter δ v) (hcenter (v.1 - 1, v.2) L hL)
      (hcenter v L hL) (hgp_ne_cen v (v.1 - 1, v.2))
      (hgp_ne_cen v v) (hgp_ne_cen (v.1, v.2 + 1) (v.1 - 1, v.2))
      (hgp_ne_cen (v.1, v.2 + 1) v) hr1 hr2 hr3 hr4 (havoidU v)
  -- ================================================================
  -- STAGE 5: finiteness — the support box, S, and V.
  -- ================================================================
  have hclosedγ : γ 0 = γ 1 := gridLoopCurve_closed hne hcl
  have hrangeγ : Set.range γ = gridPathTrace δ L :=
    range_gridLoopCurve hδ hL hne
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p : ℤ × ℤ, w p ≠ 0 →
      -(K : ℤ) ≤ p.1 ∧ p.1 ≤ K ∧ -(K : ℤ) ≤ p.2 ∧ p.2 ≤ K := by
    obtain ⟨R, hR⟩ := (isBounded_windingRegion hclosedγ).subset_closedBall 0
    obtain ⟨K, hKgt⟩ := exists_nat_gt ((R + δ) / δ)
    rw [div_lt_iff₀ hδ] at hKgt
    have hKδ : R + δ ≤ δ * K := by nlinarith
    refine ⟨K, fun p hwp => ?_⟩
    have hnotin : gridSquareCenter δ p ∉ Set.range γ := by
      rw [hrangeγ]
      intro hmem
      exact hcenter p L hL _ hmem rfl
    have hin : gridSquareCenter δ p ∈ Metric.closedBall (0 : ℂ) R :=
      hR ⟨hnotin, hwp⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hin
    have hre : |(gridSquareCenter δ p).re| ≤ R :=
      le_trans (Complex.abs_re_le_norm _) hin
    have him : |(gridSquareCenter δ p).im| ≤ R :=
      le_trans (Complex.abs_im_le_norm _) hin
    rw [hcen_re, abs_le] at hre
    rw [hcen_im, abs_le] at him
    have h1 : (-(K : ℤ) : ℝ) ≤ (p.1 : ℝ) := by push_cast; nlinarith [hre.1]
    have h2 : (p.1 : ℝ) ≤ (K : ℝ) := by nlinarith [hre.2]
    have h3 : (-(K : ℤ) : ℝ) ≤ (p.2 : ℝ) := by push_cast; nlinarith [him.1]
    have h4 : (p.2 : ℝ) ≤ (K : ℝ) := by nlinarith [him.2]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4⟩
  set S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(K : ℤ), -(K : ℤ)) ((K : ℤ), (K : ℤ))).filter
      (fun p => w p ≠ 0) with hS_def
  set V : Finset (ℤ × ℤ) :=
    Finset.Icc (-(K : ℤ) - 1, -(K : ℤ) - 1) ((K : ℤ) + 1, (K : ℤ) + 1) ∪
      L.toFinset with hV_def
  have hSmem : ∀ p : ℤ × ℤ, p ∈ S ↔ w p ≠ 0 := by
    intro p
    rw [hS_def, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hwp
      refine ⟨?_, hwp⟩
      obtain ⟨h1, h2, h3, h4⟩ := hK p hwp
      rw [Finset.mem_Icc]
      constructor
      · rw [Prod.le_def]
        exact ⟨by omega, by omega⟩
      · rw [Prod.le_def]
        exact ⟨by omega, by omega⟩
  have hwzero : ∀ p : ℤ × ℤ, p ∉ S → w p = 0 := by
    intro p hp
    by_contra h
    exact hp ((hSmem p).mpr h)
  have hSbox : ∀ p ∈ S, -(K : ℤ) ≤ p.1 ∧ p.1 ≤ K ∧
      -(K : ℤ) ≤ p.2 ∧ p.2 ≤ K := by
    intro p hp
    exact hK p ((hSmem p).mp hp)
  have hSV : S ⊆ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hSupV : ∀ p ∈ S, (p.1, p.2 + 1) ∈ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hSrtV : ∀ p ∈ S, (p.1 + 1, p.2) ∈ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  -- ================================================================
  -- STAGE 6: assembly over the common vertex Finset V.
  -- ================================================================
  set segR : ℤ × ℤ → ℂ := fun v =>
    segmentIntegral f (gridPoint δ v) (gridPoint δ (v.1 + 1, v.2)) with hsegR_def
  set segU : ℤ × ℤ → ℂ := fun v =>
    segmentIntegral f (gridPoint δ v) (gridPoint δ (v.1, v.2 + 1)) with hsegU_def
  have hbdry : ∀ p : ℤ × ℤ, gridSquareBoundaryIntegral f δ p =
      segR p + segU (p.1 + 1, p.2) - segR (p.1, p.2 + 1) - segU p := by
    intro p
    change segmentIntegral f (gridPoint δ p) (gridPoint δ (p.1 + 1, p.2)) +
        (segmentIntegral f (gridPoint δ (p.1 + 1, p.2))
          (gridPoint δ (p.1 + 1, p.2 + 1)) +
          (segmentIntegral f (gridPoint δ (p.1 + 1, p.2 + 1))
            (gridPoint δ (p.1, p.2 + 1)) +
            (segmentIntegral f (gridPoint δ (p.1, p.2 + 1))
              (gridPoint δ p) + 0))) = _
    simp only [hsegR_def, hsegU_def]
    rw [hanti (gridPoint δ (p.1, p.2 + 1)) (gridPoint δ (p.1 + 1, p.2 + 1)),
      hanti (gridPoint δ p) (gridPoint δ (p.1, p.2 + 1))]
    ring
  -- LHS regrouping: path integral as V-indexed coefficient sum
  have hclaimA : ∀ P : List ((ℤ × ℤ) × (ℤ × ℤ)),
      (∀ e ∈ P, GridAdj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V) →
      (P.map (fun e =>
        segmentIntegral f (gridPoint δ e.1) (gridPoint δ e.2))).sum =
      ∑ v ∈ V, (((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℂ) * segR v +
        ((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℂ) * segU v) := by
    intro P
    induction P with
    | nil =>
      intro _
      simp
    | cons e P ih =>
      intro hall
      have hE := hall e List.mem_cons_self
      have htail : ∀ x ∈ P, GridAdj x.1 x.2 ∧ x.1 ∈ V ∧ x.2 ∈ V :=
        fun x hx => hall x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail]
      rcases hshape e hE.1 with h | h | h | h
      · -- rightward canonical edge based at e.1
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e =
            (if v = e.1 then 1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.1 then segR e.1 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.1
          · subst hv
            rw [ite_eq_left rfl, ite_eq_left rfl]
            push_cast
            ring
          · rw [ite_eq_right hv, ite_eq_right hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.1, ite_eq_left hE.2.1, h]
        simp only [hsegR_def]
        ring
      · -- reversed rightward edge based at e.2
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e =
            (if v = e.2 then -1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.2 then -segR e.2 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.2
          · subst hv
            rw [ite_eq_left rfl, ite_eq_left rfl]
            push_cast
            ring
          · rw [ite_eq_right hv, ite_eq_right hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.2, ite_eq_left hE.2.2,
          hanti (gridPoint δ e.2) (gridPoint δ e.1), h]
        simp only [hsegR_def]
        ring
      · -- upward canonical edge based at e.1
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e =
            (if v = e.1 then 1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.1 then segU e.1 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.1
          · subst hv
            rw [ite_eq_left rfl, ite_eq_left rfl]
            push_cast
            ring
          · rw [ite_eq_right hv, ite_eq_right hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.1, ite_eq_left hE.2.1, h]
        simp only [hsegU_def]
        ring
      · -- reversed upward edge based at e.2
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e =
            (if v = e.2 then -1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.2 then -segU e.2 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.2
          · subst hv
            rw [ite_eq_left rfl, ite_eq_left rfl]
            push_cast
            ring
          · rw [ite_eq_right hv, ite_eq_right hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.2, ite_eq_left hE.2.2,
          hanti (gridPoint δ e.2) (gridPoint δ e.1), h]
        simp only [hsegU_def]
        ring
  have hpairsV : ∀ e ∈ prs, GridAdj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    refine ⟨hpair_adj L hL e he, ?_, ?_⟩
    · rw [hV_def, Finset.mem_union]
      right
      rw [List.mem_toFinset]
      exact (hpair_mem L e he).1
    · rw [hV_def, Finset.mem_union]
      right
      rw [List.mem_toFinset]
      exact (hpair_mem L e he).2
  -- RHS regrouping: shifted sums reindexed over V
  have himgUp : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1, p.2 + 1)) ↔ (v.1, v.2 - 1) ∈ S := by
    intro v
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have hpv : p = (v.1, v.2 - 1) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← hpv]
      exact hp
    · intro h
      exact ⟨(v.1, v.2 - 1), h, Prod.ext_iff.mpr ⟨rfl, by omega⟩⟩
  have himgRt : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1 + 1, p.2)) ↔ (v.1 - 1, v.2) ∈ S := by
    intro v
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have hpv : p = (v.1 - 1, v.2) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← hpv]
      exact hp
    · intro h
      exact ⟨(v.1 - 1, v.2), h, Prod.ext_iff.mpr ⟨by omega, rfl⟩⟩
  have hT2 : ∑ p ∈ V, (w p : ℂ) * segR (p.1, p.2 + 1) =
      ∑ v ∈ V, (w (v.1, v.2 - 1) : ℂ) * segR v := by
    have e1 : ∑ p ∈ V, (w p : ℂ) * segR (p.1, p.2 + 1) =
        ∑ p ∈ S, (w p : ℂ) * segR (p.1, p.2 + 1) := by
      refine (Finset.sum_subset hSV ?_).symm
      intro p _ hpS
      rw [hwzero p hpS]
      simp
    have hinj : ∀ x ∈ S, ∀ y ∈ S,
        (fun p : ℤ × ℤ => (p.1, p.2 + 1)) x =
          (fun p : ℤ × ℤ => (p.1, p.2 + 1)) y → x = y := by
      intro x _ y _ h
      have h' : ((x.1, x.2 + 1) : ℤ × ℤ) = (y.1, y.2 + 1) := h
      have h1 := congrArg Prod.fst h'
      have h2 := congrArg Prod.snd h'
      exact Prod.ext_iff.mpr ⟨by omega, by omega⟩
    have e2 : ∑ v ∈ S.image (fun p => (p.1, p.2 + 1)),
        (w (v.1, v.2 - 1) : ℂ) * segR v =
        ∑ p ∈ S, (w p : ℂ) * segR (p.1, p.2 + 1) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have hpp : p = (((p.1, p.2 + 1) : ℤ × ℤ).1,
          ((p.1, p.2 + 1) : ℤ × ℤ).2 - 1) := Prod.ext_iff.mpr ⟨rfl, by omega⟩
      exact (congrArg (fun q : ℤ × ℤ =>
        (w q : ℂ) * segR (p.1, p.2 + 1)) hpp).symm
    have e3 : ∑ v ∈ S.image (fun p => (p.1, p.2 + 1)),
        (w (v.1, v.2 - 1) : ℂ) * segR v =
        ∑ v ∈ V, (w (v.1, v.2 - 1) : ℂ) * segR v := by
      refine Finset.sum_subset ?_ ?_
      · intro v hv
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hv
        rw [← heq]
        exact hSupV p hp
      · intro v _ hvimg
        have hns : (v.1, v.2 - 1) ∉ S := fun hmem => hvimg ((himgUp v).mpr hmem)
        rw [hwzero _ hns]
        simp
    rw [e1, ← e2, e3]
  have hT3 : ∑ p ∈ V, (w p : ℂ) * segU (p.1 + 1, p.2) =
      ∑ v ∈ V, (w (v.1 - 1, v.2) : ℂ) * segU v := by
    have e1 : ∑ p ∈ V, (w p : ℂ) * segU (p.1 + 1, p.2) =
        ∑ p ∈ S, (w p : ℂ) * segU (p.1 + 1, p.2) := by
      refine (Finset.sum_subset hSV ?_).symm
      intro p _ hpS
      rw [hwzero p hpS]
      simp
    have hinj : ∀ x ∈ S, ∀ y ∈ S,
        (fun p : ℤ × ℤ => (p.1 + 1, p.2)) x =
          (fun p : ℤ × ℤ => (p.1 + 1, p.2)) y → x = y := by
      intro x _ y _ h
      have h' : ((x.1 + 1, x.2) : ℤ × ℤ) = (y.1 + 1, y.2) := h
      have h1 := congrArg Prod.fst h'
      have h2 := congrArg Prod.snd h'
      exact Prod.ext_iff.mpr ⟨by omega, by omega⟩
    have e2 : ∑ v ∈ S.image (fun p => (p.1 + 1, p.2)),
        (w (v.1 - 1, v.2) : ℂ) * segU v =
        ∑ p ∈ S, (w p : ℂ) * segU (p.1 + 1, p.2) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have hpp : p = (((p.1 + 1, p.2) : ℤ × ℤ).1 - 1,
          ((p.1 + 1, p.2) : ℤ × ℤ).2) := Prod.ext_iff.mpr ⟨by omega, rfl⟩
      exact (congrArg (fun q : ℤ × ℤ =>
        (w q : ℂ) * segU (p.1 + 1, p.2)) hpp).symm
    have e3 : ∑ v ∈ S.image (fun p => (p.1 + 1, p.2)),
        (w (v.1 - 1, v.2) : ℂ) * segU v =
        ∑ v ∈ V, (w (v.1 - 1, v.2) : ℂ) * segU v := by
      refine Finset.sum_subset ?_ ?_
      · intro v hv
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hv
        rw [← heq]
        exact hSrtV p hp
      · intro v _ hvimg
        have hns : (v.1 - 1, v.2) ∉ S := fun hmem => hvimg ((himgRt v).mpr hmem)
        rw [hwzero _ hns]
        simp
    rw [e1, ← e2, e3]
  -- the main identity over V
  have hmain : gridPathIntegral f δ L =
      ∑ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p := by
    rw [hLHS L, ← hprs_def, hclaimA prs hpairsV]
    have step1 : ∀ v ∈ V,
        (((prs.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
        (((prs.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
        ((w v : ℂ) * segR v - (w (v.1, v.2 - 1) : ℂ) * segR v) +
        ((w (v.1 - 1, v.2) : ℂ) * segU v - (w v : ℂ) * segU v) := by
      intro v _
      rw [← hjumpR v, ← hjumpU v]
      push_cast
      ring
    have step2 : ∀ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p =
        ((w p : ℂ) * segR p - (w p : ℂ) * segR (p.1, p.2 + 1)) +
        ((w p : ℂ) * segU (p.1 + 1, p.2) - (w p : ℂ) * segU p) := by
      intro p _
      rw [hbdry p]
      ring
    rw [Finset.sum_congr rfl step1, Finset.sum_congr rfl step2,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, hT2, hT3]
  have hshrink : ∑ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p =
      ∑ p ∈ S, (w p : ℂ) * gridSquareBoundaryIntegral f δ p := by
    refine (Finset.sum_subset hSV ?_).symm
    intro p _ hpS
    rw [hwzero p hpS]
    simp
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    refine ⟨(hSmem p).mp hp, ?_⟩
    intro hmem
    exact hcenter p L hL _ hmem rfl
  · exact hmain.trans hshrink

end RiemannDynamics
