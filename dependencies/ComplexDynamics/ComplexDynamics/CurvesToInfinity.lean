import ComplexDynamics.PathComponents

open Set Metric Filter

namespace ComplexDynamics

/-- A curve in a set cannot tend to infinity if its starting path component is bounded. -/
theorem not_curve_to_infinity_of_bounded_pathComponent {S : Set ℂ} {x : ℂ}
    (hbounded : Bornology.IsBounded (pathComponentIn S x)) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Ici 0)) (hstart : γ 0 = x) (hmem : MapsTo γ (Ici 0) S) :
    ¬ Tendsto (fun t => ‖γ t‖) atTop atTop := by
  have himage : IsPathConnected (γ '' Ici 0) :=
    ((convex_Ici (0 : ℝ)).isPathConnected nonempty_Ici).image' hγ
  have hsub : γ '' Ici 0 ⊆ pathComponentIn S x :=
    himage.subset_pathComponentIn ⟨0, by simp, hstart⟩ (image_subset_iff.mpr hmem)
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  intro hlim
  obtain ⟨t, ht, hnorm⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (eventually_gt_atTop R))).exists
  exact (not_lt_of_ge (hR (γ t) (hsub ⟨t, ht, rfl⟩))) hnorm

end ComplexDynamics
