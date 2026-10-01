module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ComponentwiseDiscImages

@[expose] public section

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.ComponentwiseDiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

/-- Among disjoint discs with compact centres, those centred in one closed
set eventually avoid every disjoint closed set on each fixed smaller disc. -/
theorem eventually_avoids_closed_of_centre
    (p : ComponentwiseDiscCover X) {K L H : Set X} (hK : IsCompact K)
    (hL : IsClosed L) (hH : IsClosed H) (hLH : Disjoint L H)
    (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, F n discZero ∈ L →
      ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → F n z ∉ H := by
  classical
  let V : Bool → Set X := fun b => if b then Hᶜ else Lᶜ
  have hV : ∀ b, IsOpen (V b) := by
    intro b
    cases b
    · exact hL.isOpen_compl
    · exact hH.isOpen_compl
  have hcover : K ⊆ ⋃ b, V b := by
    intro x hx
    by_cases hxL : x ∈ L
    · exact mem_iUnion.mpr ⟨true, disjoint_left.mp hLH hxL⟩
    · exact mem_iUnion.mpr ⟨false, hxL⟩
  filter_upwards [p.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    V hV hcover hr1] with n hn hnL z hz
  obtain ⟨b, hb⟩ := hn
  cases b
  · exact False.elim (hb discZero (by change ‖(0 : ℂ)‖ ≤ r; simpa using hr) hnL)
  · exact hb z hz

end AreaDeficit.Surfaces.ComponentwiseDiscCover
