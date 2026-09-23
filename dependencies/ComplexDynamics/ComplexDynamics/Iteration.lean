import ComplexDynamics.Basic

open Function Set
open Filter
open scoped Topology

namespace ComplexDynamics

/-- Holomorphy of a finite iterate on its actual region of definition. -/
theorem differentiableOn_iterate_of_mapsTo (f : ℂ → ℂ) (U G : Set ℂ)
    (hf : DifferentiableOn ℂ f U) (n : ℕ)
    (horbit : ∀ k < n, MapsTo (f^[k]) G U) : DifferentiableOn ℂ (f^[n]) G := by
  induction n with
  | zero => simpa using differentiableOn_id (s := G)
  | succ n ih =>
      simpa only [Function.iterate_succ'] using hf.comp
        (ih (fun k hk => horbit k (Nat.lt_succ_of_lt hk))) (horbit n (Nat.lt_succ_self n))

theorem continuousOn_iterate_of_mapsTo {X : Type*} [TopologicalSpace X]
    (f : X → X) (U G : Set X) (hf : ContinuousOn f U) (n : ℕ)
    (horbit : ∀ k < n, MapsTo (f^[k]) G U) : ContinuousOn (f^[n]) G := by
  induction n with
  | zero => simpa using continuousOn_id (s := G)
  | succ n ih =>
      simpa only [Function.iterate_succ'] using hf.comp
        (ih (fun k hk => horbit k (Nat.lt_succ_of_lt hk))) (horbit n (Nat.lt_succ_self n))

/-- Points whose first `n` inputs lie in the domain of the map. -/
def iterateDomain {X : Type*} (f : X → X) (U : Set X) : ℕ → Set X
  | 0 => univ
  | n + 1 => U ∩ f ⁻¹' iterateDomain f U n

theorem mem_iterateDomain_iff {X : Type*} (f : X → X) (U : Set X) (n : ℕ) (z : X) :
    z ∈ iterateDomain f U n ↔ ∀ k < n, (f^[k]) z ∈ U := by
  induction n generalizing z with
  | zero => simp [iterateDomain]
  | succ n ih =>
    change (z ∈ U ∧ f z ∈ iterateDomain f U n) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hz, hrest⟩ k hk
      cases k with
      | zero => exact hz
      | succ k => simpa only [iterate_succ_apply] using hrest k (by omega)
    · intro h
      refine ⟨h 0 (Nat.zero_lt_succ n), fun k hk => ?_⟩
      simpa only [iterate_succ_apply] using h (k + 1) (by omega)

theorem isOpen_iterateDomain {X : Type*} [TopologicalSpace X]
    (f : X → X) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U) (n : ℕ) :
    IsOpen (iterateDomain f U n) := by
  induction n with
  | zero => exact isOpen_univ
  | succ n ih => exact hf.isOpen_inter_preimage hU ih

theorem mapsTo_iterateDomain {X : Type*} (f : X → X) (U : Set X)
    {n k : ℕ} (hk : k < n) : MapsTo (f^[k]) (iterateDomain f U n) U :=
  fun z hz => (mem_iterateDomain_iff f U n z).mp hz k hk

theorem iterate_eqOn_of_mapsTo {X : Type*} (f g : X → X) (U K : Set X)
    (hfg : EqOn f g U) (n : ℕ) (horbit : ∀ k < n, MapsTo (g^[k]) K U) :
    EqOn (f^[n]) (g^[n]) K := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro z hz
    rw [iterate_succ_apply', iterate_succ_apply', ih (fun k hk => horbit k (by omega)) hz]
    exact hfg (horbit n (Nat.lt_succ_self n) hz)

/-- Local agreement at the finitely many reference-orbit points implies local
agreement of the corresponding iterates. -/
theorem eventuallyEq_iterate_of_orbit {X : Type*} [TopologicalSpace X]
    (f g : X → X) (hf : Continuous f) (n : ℕ) (z : X)
    (hfg : ∀ k < n, g =ᶠ[𝓝 ((f^[k]) z)] f) :
    (g^[n]) =ᶠ[𝓝 z] (f^[n]) := by
  induction n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n ih =>
    have hi := ih (fun k hk => hfg k (Nat.lt_succ_of_lt hk))
    have hc := (hfg n (Nat.lt_succ_self n)).comp_tendsto (hf.iterate n).continuousAt
    simpa only [iterate_succ'] using (hi.fun_comp g).trans hc

end ComplexDynamics
