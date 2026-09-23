import Mathlib.Data.Set.Image
import Mathlib.Logic.Function.Iterate

open Set Function

namespace FunctionTheory

set_option autoImplicit false

/-- Injectivity at every intermediate image implies injectivity of the
whole finite composition of iterates. No invariance of the starting set
or global injectivity is required. -/
theorem injOn_iterate_of_injOn_images
    {E : Type*} (f : E → E) (K : Set E) (n : ℕ)
    (hi : ∀ j<n, InjOn f ((f^[j]) '' K)) : InjOn (f^[n]) K := by
  induction n with
  | zero => intro x hx y hy hxy; exact hxy
  | succ n ih =>
    intro x hx y hy hxy
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply'] at hxy
    apply ih (fun j hj => hi j (Nat.lt_succ_of_lt hj)) hx hy
    exact hi n (Nat.lt_succ_self n) (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy

end FunctionTheory
