import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Pwo
import Mathlib.RingTheory.Finiteness
import Multideg
import Ideal
import Division
import Set

open Classical
open BigOperators
open Ideal

namespace MvPolynomial

variable {σ : Type _} {s : σ →₀ ℕ} {k : Type _} [Field k]
variable [term_order_class: TermOrderClass (TermOrder (σ→₀ℕ))]
variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k))


def is_groebner_basis :=
  G'.toSet ⊆ I ∧ leading_term_ideal I = leading_term_ideal G'.toSet

theorem exists_groebner_basis [Finite σ] :
  ∃ G' : Finset (MvPolynomial σ k), is_groebner_basis G' I := by  
  let ltideal : Ideal (MvPolynomial σ k) := leading_term_ideal I
  have key : Ideal.Fg ltideal := (inferInstance : IsNoetherian _ _).noetherian _
  simp only [leading_term_ideal] at key  
  rw [Ideal.fg_span_iff_fg_span_finset_subset] at key
  rcases key with ⟨s, hs, h⟩
  have := Set.subset_image hs  
  have ⟨G', hG', h'⟩ := Set.finset_subset_preimage_of_finite_image
                                        (this.symm ▸ Finset.finite_toSet s)  
  use G'
  constructor
  ·exact (Set.subset_inter_iff.mp hG').1
  · rw [this] at h'
    unfold leading_term_ideal
    rw [h', h]

lemma groebner_basis_self {G' : Finset (MvPolynomial σ k)}
  {I : Ideal (MvPolynomial σ k)} (h : is_groebner_basis G' I) :
  is_groebner_basis G' (span G') := by  
  constructor
  ·
    exact subset_span  
  ·
    rw [←SetLike.coe_set_eq]
    apply Set.eq_of_subset_of_subset    
    ·
      rw [←h.2, leading_term_ideal, leading_term_ideal]
      apply Ideal.span_mono
      apply Set.image_subset
      rw [SetLike.coe_subset_coe, span_le]
      exact h.1    
    ·
      rw [leading_term_ideal, leading_term_ideal]
      apply Ideal.span_mono
      apply Set.image_subset
      exact subset_span

theorem groebner_basis_rem_eq_zero_iff {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (h : is_groebner_basis G' I) (hG' : is_rem p G' r):
  r = 0 ↔ p ∈ I := by  
  constructor
  · intro hr
    rw [hr] at hG'
    exact (rem_mem_ideal_iff h.1 hG').mp I.zero_mem  
  · intro hp
    by_contra hr
    apply rem_term_not_mem_leading_term_ideal hG' r.multideg
    · rw [mem_support_iff, ←leading_coeff_def]
      exact r.leading_coeff_eq_zero_iff.not.mpr hr
    rw [←leading_coeff_def, ←leading_term_def, ←h.2, leading_term_ideal]
    apply Set.mem_of_subset_of_mem subset_span
    exact Set.mem_image_of_mem
            leading_term ((rem_mem_ideal_iff h.1 hG').mpr hp)

theorem groebner_basis_is_basis
  {G': Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  (h : is_groebner_basis G' I) : I = span G' := by  
  rw [←SetLike.coe_set_eq]
  apply Set.eq_of_subset_of_subset
  · intro p hp
    simp
    have hr := (exists_rem p G').choose_spec
    have := (groebner_basis_rem_eq_zero_iff h hr).mpr hp
    let q := hr.2.choose
    have hq := hr.2.choose_spec.2
    have hrem : (exists_rem p G').choose = p - q.sum (·*·) := by
      conv => enter [2] ; rw [hq]
      ring
    rw [hrem] at this
    have := eq_of_sub_eq_zero this
    rw [this]
    exact sum_mul_mem_of_subset' subset_span q  
  ·simp [span_le, h.1]

theorem groebner_basis_unique_rem
  {G': Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  (h : is_groebner_basis G' I) :
  ∃! (r : MvPolynomial σ k), is_rem p G' r := by  
  apply exists_unique_of_exists_of_unique (exists_rem p G')  
  intros r₁ r₂ hr₁ hr₂
  by_contra' hr
  have hr := sub_ne_zero_of_ne hr  
  have : (r₁-r₂).multideg ∈ (r₁-r₂).support := by
    simp [hr, ←(multideg'_eq_multideg hr), multideg']
    exact Finset.max'_mem _ _
  apply rem_sub_rem_term_not_mem_leading_term_ideal hr₁ hr₂ (r₁-r₂).multideg this
  rw [←h.2, leading_term_ideal, ←leading_coeff_def, ←leading_term_def]  
  have := Set.mem_image_of_mem leading_term (rem_sub_rem_mem_ideal h.1 hr₁ hr₂)
  exact Set.mem_of_subset_of_mem subset_span this  

-- noncomputable def groebner_rem
--   {G': Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
--   (h : is_groebner_basis G' I) :=
--   (p.groebner_basis_unique_rem h).choose

-- lemma groebner_rem_eq
--   {G': Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
--   (h : is_groebner_basis G' I) :
--   p.groebner_rem h = p.rem G'.toList := by sorry

-- theorem mem_ideal_iff_groebner_rem_eq_zero
--   {G': Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
--   (h : is_groebner_basis G' I) :
--   p ∈ I ↔ p.groebner_rem h = 0 := by sorry
-- #check 1
