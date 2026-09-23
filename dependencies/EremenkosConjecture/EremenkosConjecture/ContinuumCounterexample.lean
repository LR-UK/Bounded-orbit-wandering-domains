import EremenkosConjecture.ContinuumEntireLimit
import EremenkosConjecture.ContinuumFrontierSequence
import EremenkosConjecture.ContinuumNormalization

open Set Metric Function Filter ComplexDynamics
open scoped Topology

namespace EremenkosConjecture

open Scaffolding

theorem ContinuumEntireConstruction.constructionData {X : Set ℂ}
    {D : ContinuumNeighbourhoods X rayBase (1 / 16)} (C : ContinuumEntireConstruction D)
    (hconn : IsConnected X) (hζ : rayBase ∈ X) : ContinuumConstructionData C.f X rayBase := by
  let B : ℕ → Set ℂ := fun j => D.region ((C.chain.stage j).depth + 1)
  have hBinside (j : ℕ) : X ∪ horizontalRay rayBase ⊆ interior (B j) :=
    (D.geometry _).2.1
  have hBinter : (⋂ j, B j) = X ∪ horizontalRay rayBase := by
    have hI : (⋂ n, D.region n) = X ∪ horizontalRay rayBase := D.intersection
    apply Subset.antisymm
    · intro z hz
      rw [← hI]
      apply mem_iInter.mpr
      intro n
      apply D.region_antitone (C.depths_strictMono.id_le n |>.trans (Nat.le_succ _))
      exact mem_iInter.mp hz n
    · intro z hz
      exact mem_iInter.mpr fun j => interior_subset (hBinside j hz)
  obtain ⟨u, hu, hlim⟩ := D.exists_frontier_sequence ((C.chain.stage 0).depth + 1)
  refine ⟨C.entire, hconn, hζ,
    ⟨B, fun j => (D.geometry _).1.isClosed, hBinside, hBinter,
      fun j => (C.property j).barrier, u, hu, hlim⟩,
    C.trapping, ?_, fun j => (C.property j).returnMap, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
        intro z hz
        have hi := abs_le.mp (D.region_bounds 0 z
          (interior_subset ((D.geometry 0).2.1 hz))).2
        change height 0 + 7 < 4 * z.im ∧ 4 * z.im < height 0 + 11
        norm_num [height, rayBase] at hi ⊢
        constructor <;> linarith [hi.1, hi.2]
    | succ j => exact (C.property j).excursion
  · intro z hz
    have hzray : z ∈ horizontalRay rayBase := hz.1.resolve_left hz.2
    have hne : z ≠ rayBase := fun he => hz.2 (he.symm ▸ hζ)
    let x := z.re - rayBase.re
    have hx : 0 < x := by
      by_contra hn
      have hn' : x ≤ 0 := le_of_not_gt hn
      apply hne
      apply Complex.ext
      · dsimp [x] at hn'
        linarith [hzray.1]
      · exact hzray.2
    have hzrepr : z = rayBase + (x : ℂ) := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re]
        dsimp [x]
        ring
      · simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hzray.2
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / x) x)
    have hN₁ : 1 / x < (N : ℝ) := (le_max_left _ _).trans_lt hN
    have hN₂ : x < (N : ℝ) := (le_max_right _ _).trans_lt hN
    have hprod : 1 < (N : ℝ) * x := (div_lt_iff₀ hx).mp hN₁
    filter_upwards [eventually_ge_atTop N] with j hj
    have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
    rw [hzrepr]
    apply (C.property j).bounded x
    · apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
      nlinarith
    · linarith
  · intro z hz j n hlo hhi
    exact (C.property j).escape z hz n hlo hhi

theorem exists_continuumConstructionData_normalized {X : Set ℂ}
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : rayBase ∈ X) (hmax : ∀ z ∈ X, z.re ≤ rayBase.re)
    (hball : X ⊆ ball rayBase (1 / 16)) :
    ∃ f : ℂ → ℂ, ContinuumConstructionData f X rayBase := by
  obtain ⟨D⟩ := exists_continuumNeighbourhoods hX hconn hfull hζ hmax
    (by norm_num : (0 : ℝ) < 1 / 16) hball
  obtain ⟨C⟩ := exists_continuumEntireConstruction D hX hconn hfull hζ hmax hball
  exact ⟨C.f, C.constructionData hconn hζ⟩

/-- Theorem 1.2: every full compact continuum in the plane is a connected
component of the escaping set of a transcendental entire function. -/
theorem theorem1_2 (X : Set ℂ) (hX : IsCompact X) (hconn : IsConnected X)
    (hfull : IsConnected Xᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ ∃ z ∈ escapingSet f,
      connectedComponentIn (escapingSet f) z = X := by
  apply continuum_realization_of_normalized_disk_case rayBase
    (by norm_num : (0 : ℝ) < 1 / 16) ?_ X hX hconn hfull
  intro Y hY hYconn hYfull hball hbase hmax
  obtain ⟨f, hdata⟩ := exists_continuumConstructionData_normalized hY hYconn hYfull
    hbase hmax hball
  obtain ⟨hf, hI, _, _, hcomp⟩ := hdata.conclusions
  exact ⟨f, hf, rayBase, hI hbase, hcomp⟩

end EremenkosConjecture
