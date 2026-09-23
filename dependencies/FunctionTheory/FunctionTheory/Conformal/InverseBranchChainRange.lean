import FunctionTheory.Conformal.InverseBranchChain

open Set

namespace FunctionTheory

set_option autoImplicit false

/-- Every nonfinal point of a pulled-back orbit lies in the image of the
corresponding inverse branch, not merely in its ambient domain. -/
theorem iterate_pullbackChain_mem_branch_image {α : Type*} {f : α → α}
    {β : ℕ → α → α} {D : ℕ → Set α} {n : ℕ}
    (hb : ∀ j < n, MapsTo (β j) (D (j+1)) (D j))
    (hi : ∀ j < n, ∀ z ∈ D (j+1), f (β j z) = z) :
    ∀ z ∈ D n, ∀ j < n, f^[j] (pullbackChain β n z) ∈ β j '' D (j+1) := by
  induction n with
  | zero => intro z hz j hj; omega
  | succ n ih =>
    intro z hz j hj
    by_cases hjn : j=n
    · subst j
      change f^[n] (pullbackChain β n (β n z)) ∈ β n '' D (n+1)
      rw [iterate_pullbackChain_rightInv
        (fun j hj => hb j (by omega)) (fun j hj => hi j (by omega))
        _ (hb n (by omega) hz)]
      exact mem_image_of_mem _ hz
    · change f^[j] (pullbackChain β n (β n z)) ∈ β j '' D (j+1)
      exact ih (fun j hj => hb j (by omega)) (fun j hj => hi j (by omega))
        _ (hb n (by omega) hz) j (by omega)

end FunctionTheory
