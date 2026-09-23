import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Thickening

/-! # Separation under convergence of inverse conformal maps

The separation argument needed in a kernel-convergence proof is purely
topological. If inverse maps converge locally uniformly, compact sets in their
domain eventually have images disjoint from any closed set omitted by the limit.
Consequently the direct maps send that closed set out of every such compact set.
The existence and identification of a conformal limit are separate obligations.
-/

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

theorem locallyUniformOn_reindex
    {ι κ X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {l : Filter ι} {m : Filter κ} {F : ι → X → Y} {f : X → Y} {U : Set X}
    (h : TendstoLocallyUniformlyOn F f l U) {σ : κ → ι} (hσ : Tendsto σ m l) :
    TendstoLocallyUniformlyOn (fun n => F (σ n)) f m U := by
  intro u hu x hx
  obtain ⟨V, hV, hevent⟩ := h u hu x hx
  exact ⟨V, hV, hσ.eventually hevent⟩

theorem eventually_disjoint_image_of_tendstoUniformlyOn
    {ι X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {g : ι → X → Y} {g₀ : X → Y} {K : Set X} {A : Set Y}
    (hK : IsCompact K) (hg₀ : ContinuousOn g₀ K) (hA : IsClosed A)
    (hdisj : Disjoint (g₀ '' K) A) (hconv : TendstoUniformlyOn g g₀ l K) :
    ∀ᶠ n in l, Disjoint (g n '' K) A := by
  have hsub : g₀ '' K ⊆ Aᶜ := disjoint_left.mp hdisj
  obtain ⟨ε, hε, hεsub⟩ := (hK.image_of_continuousOn hg₀).exists_thickening_subset_open
    hA.isOpen_compl hsub
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) ε hε] with n hn
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩
  apply hεsub
  exact mem_thickening_iff.mpr ⟨g₀ z, mem_image_of_mem _ hz, by simpa only [dist_comm] using hn z hz⟩

theorem eventually_disjoint_image_of_tendstoLocallyUniformlyOn
    {ι X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {g : ι → X → Y} {g₀ : X → Y} {D K : Set X} {A : Set Y}
    (hK : IsCompact K) (hKD : K ⊆ D) (hg₀ : ContinuousOn g₀ D) (hA : IsClosed A)
    (hdisj : Disjoint (g₀ '' D) A) (hconv : TendstoLocallyUniformlyOn g g₀ l D) :
    ∀ᶠ n in l, Disjoint (g n '' K) A := by
  apply eventually_disjoint_image_of_tendstoUniformlyOn hK (hg₀.mono hKD) hA
    (hdisj.mono_left (image_mono hKD))
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hKD)

/-- If `g n` inverts `f n` on `A`, convergence of the inverse maps away from `A`
forces `f n '' A` to leave each compact subset of the inverse-map domain. -/
theorem eventually_disjoint_direct_image_of_inverse_convergence
    {ι X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {f : ι → Y → X} {g : ι → X → Y} {g₀ : X → Y}
    {D K : Set X} {A : Set Y}
    (hK : IsCompact K) (hKD : K ⊆ D) (hg₀ : ContinuousOn g₀ D) (hA : IsClosed A)
    (hdisj : Disjoint (g₀ '' D) A) (hconv : TendstoLocallyUniformlyOn g g₀ l D)
    (hinv : ∀ n, LeftInvOn (g n) (f n) A) :
    ∀ᶠ n in l, Disjoint (f n '' A) K := by
  filter_upwards [eventually_disjoint_image_of_tendstoLocallyUniformlyOn
    hK hKD hg₀ hA hdisj hconv] with n hn
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hKz
  apply disjoint_left.mp hn (mem_image_of_mem (g n) hKz)
  simpa only [hinv n hz] using hz

end FunctionTheory
