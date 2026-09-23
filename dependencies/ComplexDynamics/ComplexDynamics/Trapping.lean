import ComplexDynamics.UniformEscape
import Mathlib.Topology.UniformSpace.UniformApproximation

open Function Filter Set Metric
open scoped Topology Uniformity OnePoint

namespace ComplexDynamics

/-- Points whose orbits eventually remain in the specified set. -/
def trappedSet (f : ℂ → ℂ) (B : Set ℂ) : Set ℂ :=
  {z | ∀ᶠ n : ℕ in atTop, (f^[n]) z ∈ B}

/-- An escaping point accumulated by orbits trapped in one compact set is a
Julia point. The proof directly excludes local normality. -/
theorem mem_juliaSet_of_escape_of_closure_trappedSet {f : ℂ → ℂ}
    (hf : Continuous f) {B : Set ℂ} (hB : IsCompact B) {z : ℂ}
    (hz : z ∈ escapingSet f) (hacc : z ∈ closure (trappedSet f B)) :
    z ∈ juliaSet f := by
  rintro ⟨U, hU, hzU, hnormal⟩
  obtain ⟨ψ, hψ, g, hg⟩ := hnormal id strictMono_id
  have hgc : Continuous g := hg.continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      OnePoint.continuous_coe.comp ((hf.iterate (ψ n)).comp continuous_subtype_val)))
  let S : Set RiemannSphere := (fun w : ℂ => (w : RiemannSphere)) '' B
  have hS : IsClosed S := (hB.image OnePoint.continuous_coe).isClosed
  have hpoint : ∀ w : U, Tendsto (fun n => sphericalIterate f (ψ n) w) atTop (𝓝 (g w)) :=
    fun w => hg.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ w)
  have hsub : ((↑) : U → ℂ) ⁻¹' trappedSet f B ⊆ g ⁻¹' S := by
    intro w hw
    apply hS.mem_of_tendsto (hpoint w)
    exact (hψ.tendsto_atTop.eventually hw).mono fun n hn => ⟨(f^[ψ n]) w, hn, rfl⟩
  have hcl : (⟨z, hzU⟩ : U) ∈ closure (((↑) : U → ℂ) ⁻¹' trappedSet f B) :=
    hU.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage hacc
  have hmem : g ⟨z, hzU⟩ ∈ S := closure_minimal hsub (hS.preimage hgc) hcl
  have heq : g ⟨z, hzU⟩ = (∞ : RiemannSphere) :=
    tendsto_nhds_unique (hpoint ⟨z, hzU⟩)
      ((tendsto_sphericalIterate_of_mem_escapingSet hz).comp hψ.tendsto_atTop)
  rw [heq] at hmem
  exact OnePoint.infty_notMem_image_coe hmem

/-- Mapping into a forward-invariant set eventually traps the orbit. -/
theorem mem_trappedSet_of_iterate_mem {f : ℂ → ℂ} {B : Set ℂ}
    (hB : MapsTo f B B) {z : ℂ} {n : ℕ} (hz : (f^[n]) z ∈ B) :
    z ∈ trappedSet f B := by
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hB.iterate k hz

end ComplexDynamics
