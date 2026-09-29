module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.AlmostEverywhere.Definitions

@[expose] public section

/-! # Comparing chart-null exceptional sets -/

open Set Function MeasureTheory

namespace SurfaceDynamics

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem ChartAlmostEverywhere.mono {A : Set X} {P Q : X → Prop}
    (h : ChartAlmostEverywhere A P) (hPQ : ∀ x ∈ A, P x → Q x) :
    ChartAlmostEverywhere A Q := by
  intro p
  apply measure_mono_null (image_mono (inter_subset_inter_left _ ?_)) (h p)
  rintro x ⟨hx, hn⟩
  exact ⟨hx, fun hp => hn (hPQ x hx hp)⟩

theorem chartAlmostEverywhere_of_countable_null_cover
    {ι : Type*} [Countable ι] {A : Set X} {P : X → Prop} (B : ι → Set X)
    (hcover : {x ∈ A | ¬ P x} ⊆ ⋃ n, B n)
    (hnull : ∀ n p, volume ((chartAt ℂ p) '' (B n ∩ (chartAt ℂ p).source)) = 0) :
    ChartAlmostEverywhere A P := by
  intro p
  apply measure_mono_null (image_mono (inter_subset_inter_left _ hcover))
  rw [iUnion_inter, image_iUnion]
  exact measure_iUnion_null (fun n => hnull n p)

theorem HasPositiveChartArea.exists_of_chartAlmostEverywhere
    {A : Set X} {P : X → Prop} (hpos : HasPositiveChartArea A)
    (h : ChartAlmostEverywhere A P) : ∃ x ∈ A, P x := by
  by_contra hn
  have he : {x ∈ A | ¬ P x} = A := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun hp => hn ⟨x, hx, hp⟩⟩⟩
  obtain ⟨p, hp⟩ := hpos
  have hh := h p
  rw [he] at hh
  exact (ne_of_gt hp) hh

end SurfaceDynamics

