import FunctionTheory.Conformal.KernelSeparation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform escape from convergence on a closed strip

This isolates the boundary-convergence input needed for the whole-continuum
estimate. Convergence on the open strip alone does not suffice: the compact
rectangles below include their horizontal boundary segments.
-/

open Set Metric Filter
open scoped Topology

namespace FunctionTheory

theorem eventually_abs_re_gt_of_inverse_closed_strip_convergence
    {ι : Type*} {l : Filter ι} {f g : ι → ℂ → ℂ} {g₀ : ℂ → ℂ}
    {A : Set ℂ} {M : ℝ}
    (hA : IsClosed A)
    (himage : ∀ n, MapsTo (f n) A {w : ℂ | |w.im| ≤ M})
    (hinv : ∀ n, LeftInvOn (g n) (f n) A)
    (hg₀ : ContinuousOn g₀ {w : ℂ | |w.im| ≤ M})
    (hdisj : Disjoint (g₀ '' {w : ℂ | |w.im| ≤ M}) A)
    (hconv : TendstoLocallyUniformlyOn g g₀ l {w : ℂ | |w.im| ≤ M}) :
    ∀ R : ℝ, ∀ᶠ n in l, ∀ z ∈ A, R < |(f n z).re| := by
  intro R
  let K : Set ℂ := {w | |w.re| ≤ R ∧ |w.im| ≤ M}
  have hK : IsCompact K := by
    apply isCompact_iff_isClosed_bounded.mpr
    refine ⟨(isClosed_le Complex.continuous_re.abs continuous_const).inter
      (isClosed_le Complex.continuous_im.abs continuous_const), ?_⟩
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨R + M, fun z hz => (Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hz.1 hz.2)⟩
  have hKD : K ⊆ {w : ℂ | |w.im| ≤ M} := fun _ hz => hz.2
  filter_upwards [eventually_disjoint_direct_image_of_inverse_convergence
    hK hKD hg₀ hA hdisj hconv hinv] with n hn
  intro z hz
  by_contra h
  exact disjoint_left.mp hn (mem_image_of_mem _ hz)
    ⟨le_of_not_gt h, himage n hz⟩

end FunctionTheory
