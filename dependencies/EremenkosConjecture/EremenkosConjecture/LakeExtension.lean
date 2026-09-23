import EremenkosConjecture.DiskMargins
import EremenkosConjecture.DryLand

open Set Metric Function

namespace EremenkosConjecture

theorem mapsTo_of_fixes_compl (H : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hfix : ∀ z ∉ U, H z = z) : MapsTo H U U := by
  intro z hz
  by_contra Hnot
  have Hsame := hfix (H z) Hnot
  have heq : H z = z := H.injective Hsame
  exact Hnot (heq.symm ▸ hz)

/-- Enlarge one lake to contain a prescribed point, without touching the obstacles. -/
theorem AmbientDisk.enlarge_to_point (M D : AmbientDisk) {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) (hAM : A ⊆ M.inside)
    (hDM : D.carrier ⊆ M.inside) (hAD : Disjoint A D.carrier)
    {q : ℂ} (hq : q ∈ M.inside \ A) :
    ∃ E : AmbientDisk, D.carrier ⊆ E.inside ∧ E.carrier ⊆ M.inside \ A ∧ q ∈ E.inside := by
  have hDV : D.carrier ⊆ M.inside \ A := fun z hz =>
    ⟨hDM hz, fun hzA => Set.disjoint_left.mp hAD hzA hz⟩
  obtain ⟨E, hDE, hEV, p, hpE, hpD⟩ := D.exists_larger
    (M.open_inside.sdiff hA.isClosed) hDV
  by_cases hqE : q ∈ E.inside
  · exact ⟨E, hDE, hEV, hqE⟩
  let U := M.inside \ (A ∪ D.carrier)
  have hAcD : IsCompact (A ∪ D.carrier) := hA.union D.compact
  have hAfD : IsConnected (A ∪ D.carrier)ᶜ :=
    isConnected_compl_union_disjoint A D.carrier hA D.compact hfull D.full hAD
  have hADin : A ∪ D.carrier ⊆ M.inside := union_subset hAM hDM
  have hUopen : IsOpen U := M.open_inside.sdiff hAcD.isClosed
  have hUconn : IsConnected U := (M.pathConnected_sdiff hAcD hAfD hADin).isConnected
  have hpU : p ∈ U := ⟨(hEV (E.inside_subset hpE)).1,
    fun H => H.elim (hEV (E.inside_subset hpE)).2 hpD⟩
  have hqU : q ∈ U := ⟨hq.1, fun H => H.elim hq.2 (fun H' => hqE (hDE H'))⟩
  obtain ⟨H, hHp, hfix⟩ := exists_supportedMove hUopen hUconn.isPreconnected hpU hqU
  refine ⟨E.map H, ?_, ?_, ?_⟩
  · intro z hz
    rw [E.inside_map]
    exact ⟨z, hDE hz, hfix z (fun hzU => hzU.2 (Or.inr hz))⟩
  · rw [E.carrier_map]
    rintro z ⟨w, hw, rfl⟩
    apply mapsTo_of_fixes_compl H _ (hEV hw)
    intro v hv
    exact hfix v (fun hvU => hv ⟨hvU.1, fun hvA => hvU.2 (Or.inl hvA)⟩)
  · rw [E.inside_map]
    exact ⟨p, hpE, hHp⟩

/-- Enlarge the sea by shrinking its complementary disk around all obstacles. -/
theorem AmbientDisk.shrink_away_point (M : AmbientDisk) {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) (hAM : A ⊆ M.inside)
    {q : ℂ} (hq : q ∉ A) :
    ∃ E : AmbientDisk, A ⊆ E.inside ∧ E.carrier ⊆ M.inside ∧ q ∉ E.carrier := by
  obtain ⟨E, hAE, hEM, p, hpM, hpE⟩ := M.exists_smaller hA hAM
  by_cases hqE : q ∈ E.carrier
  · let U := M.inside \ A
    have hUopen : IsOpen U := M.open_inside.sdiff hA.isClosed
    have hUconn : IsConnected U := (M.pathConnected_sdiff hA hfull hAM).isConnected
    have hpU : p ∈ U := ⟨hpM, fun H => hpE (E.inside_subset (hAE H))⟩
    have hqU : q ∈ U := ⟨hEM hqE, hq⟩
    obtain ⟨H, hHp, hfix⟩ := exists_supportedMove hUopen hUconn.isPreconnected hpU hqU
    refine ⟨E.map H, ?_, ?_, ?_⟩
    · intro z hz
      rw [E.inside_map]
      exact ⟨z, hAE hz, hfix z (fun hzU => hzU.2 hz)⟩
    · rw [E.carrier_map]
      rintro z ⟨w, hw, rfl⟩
      apply mapsTo_of_fixes_compl H _ (hEM hw)
      intro v hv
      exact hfix v (fun hvU => hv hvU.1)
    · rw [E.carrier_map]
      rintro ⟨w, hw, hwq⟩
      have hpw : p = w := H.injective (hHp.trans hwq.symm)
      exact hpE (hpw.symm ▸ hw)
  · exact ⟨E, hAE, hEM, hqE⟩

end EremenkosConjecture
