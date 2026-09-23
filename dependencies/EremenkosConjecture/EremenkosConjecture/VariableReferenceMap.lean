import EremenkosConjecture.VariableConstructionData
import EremenkosConjecture.HolomorphicGluing
import EremenkosConjecture.DisjointFullUnions

/-! # The piecewise holomorphic reference map in Proposition 3.2 -/

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture
namespace VariableConstruction

structure ReferenceMapData (D : UniformEscapeData) {n : ℕ} (S : DiscSchedule n) (b : ℝ) (f : ℂ → ℂ) where
  A : Set ℂ
  U : Set ℂ
  g : ℂ → ℂ
  compact : IsCompact A
  full : IsConnected Aᶜ
  isOpen : IsOpen U
  subset : A ⊆ U
  holomorphic : DifferentiableOn ℂ g U
  control : variableControlDisc (S.radius n) ⊆ interior A
  next : (f^[n]) '' D.K (n + 1) ⊆ interior A
  points : (f^[n]) '' D.P n ⊆ interior A
  old_eq : ∀ z ∈ variableControlDisc (S.radius n), g =ᶠ[𝓝 z] f
  translate_eq : ∀ z ∈ (f^[n]) '' D.K (n + 1), g =ᶠ[𝓝 z] (fun w => w + ((b - S.center n : ℝ) : ℂ))
  trap_eq : ∀ z ∈ (f^[n]) '' D.P n, g =ᶠ[𝓝 z] (fun _ => -3)

theorem exists_reference_map (D : UniformEscapeData) {n : ℕ} (S : DiscSchedule n) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hs : StageProperty D S f) :
    Nonempty (ReferenceMapData D S b f) := by
  obtain ⟨L, hLc, hLf, hnextL, hL⟩ := exists_full_compact_neighbourhood
    (D.K (n + 1)) (interior (D.K n)) (D.compact _) (D.full _) isOpen_interior (D.nested n)
  have hLKn : L ⊆ D.K n := hL.trans interior_subset
  let M := (f^[n]) '' L
  let Q := (f^[n]) '' D.P n
  have hMc : IsCompact M := hLc.image (hf.continuous.iterate n)
  have hMf : IsConnected Mᶜ := (hs.2.2.1 n le_rfl).mono hLKn |>.isFull_image hLf
  have hQc : IsCompact Q := (D.compactP n).image (hf.continuous.iterate n)
  have hQfull : IsConnected Qᶜ := (hs.2.2.1 n le_rfl).mono (D.points_subset n) |>.isFull_image (D.fullP n)
  have hMD : M ⊆ variableTargetDisc (S.center n) := by
    rintro z ⟨w, hw, rfl⟩
    exact hs.2.1 n le_rfl (hLKn hw)
  have hQD : Q ⊆ variableTargetDisc (S.center n) := by
    rintro z ⟨w, hw, rfl⟩
    exact hs.2.1 n le_rfl (D.points_subset n hw)
  have hsep : ∀ z ∈ variableControlDisc (S.radius n), z.re < (S.center n - 3 / 2 : ℝ) := by
    intro z hz
    have H := variableControlDisc_re_bound hz
    have Hr := S.center_radius (j := n) le_rfl
    linarith
  have hsep' : ∀ z ∈ variableTargetDisc (S.center n), (S.center n - 3 / 2 : ℝ) < z.re := by
    intro z hz
    have H := (variableTargetDisc_re_bounds hz).1
    linarith
  have hCM : Disjoint (variableControlDisc (S.radius n)) M := Set.disjoint_left.mpr (fun z hz hzm =>
    (not_lt_of_ge (hsep z hz).le) (hsep' z (hMD hzm)))
  have hCQ : Disjoint (variableControlDisc (S.radius n)) Q := Set.disjoint_left.mpr (fun z hz hzq =>
    (not_lt_of_ge (hsep z hz).le) (hsep' z (hQD hzq)))
  have hMQ : Disjoint M Q := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq : y = x := (hs.2.2.1 n le_rfl).injOn (D.points_subset n hy) (hLKn hx) hxy
    have hyfront := D.boundary n hy
    exact hyfront.2 (heq ▸ hL hx)
  have hCMfull : IsConnected (variableControlDisc (S.radius n) ∪ M)ᶜ :=
    isConnected_compl_union_separated _ _ (isCompact_closedBall _ _) hMc
      (isConnected_compl_closedBall _ _) hMf (S.center n - 3 / 2) hsep (fun z hz => hsep' z (hMD hz))
  have hCMQ : Disjoint (variableControlDisc (S.radius n) ∪ M) Q := disjoint_union_left.mpr ⟨hCQ, hMQ⟩
  have hcompact : IsCompact ((variableControlDisc (S.radius n) ∪ M) ∪ Q) :=
    ((isCompact_closedBall _ _).union hMc).union hQc
  have hfull : IsConnected ((variableControlDisc (S.radius n) ∪ M) ∪ Q)ᶜ :=
    isConnected_compl_union_disjoint _ Q ((isCompact_closedBall _ _).union hMc) hQc hCMfull hQfull hCMQ
  obtain ⟨W₁, g₁, hW₁, hCW₁, hg₁, hold₁, htranslate₁⟩ :=
    exists_holomorphic_gluing (variableControlDisc (S.radius n)) M univ univ (isCompact_closedBall _ _) hMc hCM
      isOpen_univ isOpen_univ (subset_univ _) (subset_univ _) f (fun z => z + ((b - S.center n : ℝ) : ℂ))
      hf.differentiableOn (differentiable_id.add_const ((b - S.center n : ℝ) : ℂ)).differentiableOn
  obtain ⟨W, g, hW, hCW, hg, hpiece, htrap⟩ :=
    exists_holomorphic_gluing (variableControlDisc (S.radius n) ∪ M) Q W₁ univ
      ((isCompact_closedBall _ _).union hMc) hQc hCMQ hW₁ isOpen_univ
      hCW₁ (subset_univ _) g₁ (fun _ => -3) hg₁ (differentiableOn_const (-3))
  obtain ⟨A, hAc, hAf, hCA, hAW⟩ :=
    exists_full_compact_neighbourhood _ W hcompact hfull hW hCW
  have hnextM : (f^[n]) '' D.K (n + 1) ⊆ M := image_mono (hnextL.trans interior_subset)
  exact ⟨{
    A := A
    U := W
    g := g
    compact := hAc
    full := hAf
    isOpen := hW
    subset := hAW
    holomorphic := hg
    control := fun z hz => hCA (Or.inl (Or.inl hz))
    next := fun z hz => hCA (Or.inl (Or.inr (hnextM hz)))
    points := fun z hz => hCA (Or.inr hz)
    old_eq := fun z hz => (hpiece z (Or.inl hz)).trans (hold₁ z hz)
    translate_eq := fun z hz => (hpiece z (Or.inr (hnextM hz))).trans (htranslate₁ z (hnextM hz))
    trap_eq := htrap
  }⟩

end VariableConstruction
end EremenkosConjecture


