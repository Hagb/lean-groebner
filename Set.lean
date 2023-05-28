import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic

namespace Set

lemma subset_image {α : Type _} {β : Type _} {f : α → β}
  {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
  f '' (s ∩ f⁻¹' t) = t := by
  have := Set.image_inter_preimage f s t
  rw [Set.inter_eq_right_iff_subset.mpr h] at this
  exact this

lemma finset_subset_preimage_of_finite_image {α : Type _} {β : Type _}
  {s : Set α} {f : α → β} (h : (f '' s).Finite) :
  ∃ (s' : Finset α), s'.toSet ⊆ s ∧ f '' s' = f '' s := by
  have hfin := h.coe_toFinset
  have :=  s.mem_image f
  rw [←hfin] at this
  by_cases h' : s = ∅
  ·
    use ∅
    simp at h'
    simp [h']
  ·
    classical
    cases' Set.nonempty_iff_ne_empty.mpr h' with a ha
    let s' := h.toFinset.image fun (x : β) =>
      if hx : x ∈ h.toFinset
        then ((this x).mp (hx)).choose
        else a
    have hs' : s'.toSet ⊆ s := by
      simp
      intro x hx
      simp
      have fact : ∃ x_1, x_1 ∈ s ∧ f x_1 = f x := ⟨x, hx, rfl⟩
      simp [fact, fact.choose_spec]
    use s'
    constructor
    ·exact hs'
    apply Set.eq_of_subset_of_subset
    ·exact Set.image_subset _ hs'
    ·
      intro y hy
      simp at hy
      let ⟨x,hx, hxy⟩ := hy
      simp
      use x
      constructor
      ·exact hx
      rw [←hxy] at hy
      simp [hy]
      generalize_proofs h₁
      simp [h₁.choose_spec]
      exact hxy

end Set
