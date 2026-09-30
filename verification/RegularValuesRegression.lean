module

public import BoundedWanderingDomains.Surfaces.LocalDynamics

@[expose] public section

open Set Topology

/- Empty-preimage neighbourhoods are regular, including an entirely empty source. -/
example (g : Empty → ℂ) : SurfaceDynamics.Map.singularValues g = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have h := SurfaceDynamics.Map.singularValues_subset_closure_range g hy
  have he : range g = ∅ := Set.eq_empty_of_forall_notMem (by
    rintro b ⟨a, _⟩
    exact Empty.elim a)
  simp only [he, closure_empty, mem_empty_iff_false] at h

/- An empty fibre which is approached by image points remains singular. -/
example : (0 : ℂ) ∈ SurfaceDynamics.Map.singularValues
    (Subtype.val : ({0}ᶜ : Set ℂ) → ℂ) := by
  intro hr
  have hc : (0 : ℂ) ∈ closure (range (Subtype.val : ({0}ᶜ : Set ℂ) → ℂ)) := by
    rw [Subtype.range_val, closure_compl_singleton]
    exact mem_univ _
  obtain ⟨z, hz⟩ := SurfaceDynamics.Map.mem_range_of_regular_of_mem_closure _ hr hc
  exact z.2 (show (z : ℂ) ∈ ({0} : Set ℂ) from hz)
