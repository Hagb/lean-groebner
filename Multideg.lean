
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LibrarySearch
import Basic
import TermOrder

namespace MvPolynomial

open BigOperators
open Classical
open Finset
variable {σ : Type _}

variable [LinearOrder (TermOrder (σ →₀ ℕ))]
variable [CovariantClass (TermOrder (σ→₀ℕ)) (TermOrder (σ→₀ℕ)) (·+·) (·≤·)]
variable [ZeroLEClass (TermOrder (σ→₀ℕ))]


variable [CommSemiring R]
variable (p q: MvPolynomial σ R)
variable (p_ne_zero: p ≠ 0)
variable (q_ne_zero: q ≠ 0)
def multideg: TermOrder (σ →₀ ℕ) :=
  p.support.sup (α:=TermOrder (σ→₀ℕ)) (β:=TermOrder (σ→₀ℕ)) id
#align mv_polynomial.multideg MvPolynomial.multideg

def multideg' : TermOrder (σ →₀ ℕ) :=
  p.support.max' (α:=TermOrder (σ→₀ℕ))
    (Finset.nonempty_of_ne_empty (p.support_zero_iff.not.mp p_ne_zero))
#align mv_polynomial.multideg' MvPolynomial.multideg'

lemma multideg_def:
  multideg p = p.support.sup (α:=TermOrder (σ→₀ℕ)) (β:=TermOrder (σ→₀ℕ)) id :=
  rfl

lemma multideg'_def:
  multideg' p p_ne_zero = p.support.max' (α:=TermOrder (σ→₀ℕ))
    (Finset.nonempty_of_ne_empty (p.support_zero_iff.not.mp p_ne_zero)) :=
  rfl

@[simp]
lemma multideg'_eq_multideg {p: MvPolynomial σ R} (p_ne_zero: p ≠ 0):
  multideg' p p_ne_zero = multideg p := by
  unfold multideg multideg' Finset.max'
  -- simp only [Finset.coe_sup', Function.comp.right_id]
  -- library_search
  exact Finset.sup'_eq_sup (multideg'.proof_1 p p_ne_zero) id

@[simp]
lemma multideg_eq_zero_of_zero (hp: p = 0): multideg p = 0 := by
  unfold multideg
  rw [(support_zero_iff _).mp hp]
  exact Finset.sup_empty

@[simp]
lemma ne_zero_of_multideg_ne_zero
  {p: MvPolynomial σ R} (hmultideg: multideg p ≠ 0):
  p ≠ 0 := by
  by_contra hp
  -- simp? [hp] at hmultideg
  simp only [hp, multideg_eq_zero_of_zero, ne_eq, not_true] at hmultideg

lemma coeff_eq_zero_of_multideg_lt {p: MvPolynomial σ R} (h: multideg p < s):
  coeff s p = 0 := by
  rw [←not_mem_support_iff]
  by_contra hs
  unfold multideg at h
  -- rw [←id_eq (α:=TermOrder (σ→₀ℕ)) s] at hs
  have := Finset.le_sup (f:=@id (TermOrder (σ→₀ℕ))) hs
  exact not_le_of_lt h this

lemma coeff_eq_zero_of_multideg'_lt
    {p: MvPolynomial σ R} {p_ne_zero: p ≠ 0} (h: multideg' p p_ne_zero < s):
  coeff s p = 0 :=
    coeff_eq_zero_of_multideg_lt (multideg'_eq_multideg p_ne_zero ▸ h)

lemma le_multideg_of_coeff_ne_zero
    {p: MvPolynomial σ R} {s: TermOrder (σ→₀ℕ)} (h: coeff s p ≠ 0):
  s ≤ multideg p := by
  revert h
  rw [←not_imp_not, ←lt_iff_not_le]
  -- simp?
  simp only [ne_eq, not_not]
  exact coeff_eq_zero_of_multideg_lt


lemma le_multideg'_of_coeff_ne_zero
    {p: MvPolynomial σ R} {p_ne_zero: p ≠ 0} {s: TermOrder (σ→₀ℕ)}
    (h: coeff s p ≠ 0):
  s ≤ multideg' p p_ne_zero :=
  multideg'_eq_multideg p_ne_zero ▸ le_multideg_of_coeff_ne_zero h

  -- apply coeff_eq_zero_of_multideg_lt (p:=p)
   --coeff_eq_zero_of_multideg_lt]
noncomputable def lc : R :=
  if p_ne_zero': p ≠ 0
  then coeff (multideg' p p_ne_zero') p
  else 0
#align mv_polynomial.lc MvPolynomial.lc
noncomputable def lt : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (multideg' p p_ne_zero') (coeff (multideg' p p_ne_zero') p)
  else 0
#align mv_polynomial.lt MvPolynomial.lt

-- noncomputable def ltOfSet (S: Set (MvPolynomial σ R)): Set (MvPolynomial σ R) :=
--   { ltp | ∃ p ∈ S, ltp = lt p }

-- noncomputable def ltOfFinset (S: Finset (MvPolynomial σ R)): Finset (MvPolynomial σ R) :=
--   S.filter (∃ p ∈ S, · = lt p)

-- noncomputable def supportListOfPoly (p: MvPolynomial σ R): List (TermOrder (σ→₀ℕ)) :=
--   p.support.sort LE.le

-- noncomputable def ltOfIdeal (I : Ideal (MvPolynomial σ R)): Ideal (MvPolynomial σ R) :=
--   Ideal.span (ltOfSet I)
-- #align mv_polynomial.lt_of_ideal MvPolynomial.ltOfIdeal
lemma multideg'_in_support: multideg' p p_ne_zero ∈ p.support :=
  (show Finset (TermOrder (σ→₀ℕ)) from p.support).max'_mem _
#align mv_polynomial.multideg'_in_support MvPolynomial.multideg'_in_support

lemma lc_def_of_p_ne_zero {p: MvPolynomial σ R} (p_ne_zero: p≠0):
  lc p = coeff (multideg' p p_ne_zero) p := by
  unfold lc
  -- simp? [p_ne_zero]
  simp only [ne_eq, p_ne_zero, not_false_iff, multideg'_eq_multideg,
            dite_eq_ite, ite_true]
lemma lc_eq_zero_iff: lc p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hlc
    by_contra h
    -- simp? [h, lc] at hlc
    simp only [lc, ne_eq, h, not_false_iff, dite_true] at hlc
    exact (mem_support_iff.mp (multideg'_in_support p h)) hlc
  ·
    intro hp
    rw [hp]
    rfl
lemma lc_def': lc p = coeff (multideg p) p := by
  by_cases hp: p = 0
  ·
    rw [hp]
    -- simp? [lc_eq_zero_iff]
    simp only [multideg_eq_zero_of_zero, coeff_zero, lc_eq_zero_iff]
  ·
    unfold lc
    -- simp? [hp]
    simp only [ne_eq, hp, not_false_iff, multideg'_eq_multideg,
              dite_eq_ite, ite_true]

lemma multideg'_iff {p: MvPolynomial σ R} (p_ne_zero: p ≠ 0):
  s = multideg' p p_ne_zero ↔ (p.coeff s ≠ 0 ∧ ∀ s' > s, p.coeff s' = 0) := by
  constructor
  ·
    intros hs
    rw [hs, ←lc_def_of_p_ne_zero p_ne_zero]
    constructor
    ·exact (lc_eq_zero_iff p).not.mpr p_ne_zero
    ·
      intros s' hs'
      exact coeff_eq_zero_of_multideg'_lt hs'
  ·
    rintro ⟨hsp, hs'⟩
    rw [eq_iff_le_not_lt]
    constructor
    ·
      exact le_multideg'_of_coeff_ne_zero hsp
    ·
      by_contra hs
      specialize hs' (p.multideg' p_ne_zero) hs
      rw [←lc_def_of_p_ne_zero p_ne_zero] at hs'
      exact p_ne_zero ((lc_eq_zero_iff p).mp hs')
lemma lt_eq_zero_iff: lt p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hp
    -- simp? [lt] at hp
    simp only [lt, ne_eq, dite_not, dite_eq_left_iff, monomial_eq_zero] at hp
    by_contra hp'
    exact mem_support_iff.mp (multideg'_in_support p hp') (hp hp')
  ·
    intro hp
    rw [hp]
    rfl
lemma lt_def': lt p = monomial (multideg p) (coeff (multideg p) p) := by
  by_cases hp: p = 0
  ·
    rw [hp]
    -- simp? [lt_eq_zero_iff]
    simp only [multideg_eq_zero_of_zero, coeff_zero, map_zero,
              lt_eq_zero_iff, ne_eq, not_true]
  ·
    unfold lt
    -- simp? [hp]
    simp only [ne_eq, hp, not_false_iff, multideg'_eq_multideg,
              dite_eq_ite, ite_true]
noncomputable def lm : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (multideg' p p_ne_zero') (1 : R)
  else 0
#align mv_polynomial.lm MvPolynomial.lm

-- noncomputable def lmOfFinset (S: Finset (MvPolynomial σ R)): Finset (MvPolynomial σ R) :=
--   S.filter (∃ p ∈ S, · = lm p)
lemma lc_smul_lm_eq_lt: lc p • lm p =lt p := by
  unfold lc lm lt
  by_cases hp: p = 0
  ·
    -- simp? [hp]
    simp only [hp, ne_eq, coeff_zero, dite_eq_ite, dite_false, smul_zero]
  ·
    -- simp? [hp]
    simp only [ne_eq, hp, not_false_iff, dite_true]
    rw [smul_monomial, mul_one]
lemma lm_eq_zero_iff: lm p = 0 ↔ p = 0 := by
  unfold lm
  constructor
  ·
    intro hlm
    -- simp? at hlm
    simp only [ne_eq, dite_not, dite_eq_left_iff, monomial_eq_zero] at hlm
    by_cases if_trivial: Nontrivial R
    ·
      by_contra hp
      exact one_ne_zero (hlm hp)
    ·
      have all_mem_eq := nontrivial_iff.not.mp if_trivial
      push_neg at all_mem_eq
      specialize all_mem_eq 1 0
      rw [←mul_one p, ←C_1, ←C_0, all_mem_eq]
      simp only [map_zero, mul_zero]
  ·
    intro hp
    simp only [hp, ne_eq, not_true, dite_false]
variable {p q: MvPolynomial σ R} (p_ne_zero: p≠0) (q_ne_zero: q≠0)
lemma le_multideg' {i: TermOrder (σ→₀ℕ)} (h: i ∈ p.support):
  i ≤ p.multideg' p_ne_zero
  := Finset.le_max' (α:=TermOrder (σ→₀ℕ)) p.support i h

lemma le_multideg {i: TermOrder (σ→₀ℕ)} (h: i ∈ p.support): i ≤ p.multideg
  := by
  by_cases hp: p = 0
  ·
    rw [support_zero_iff] at hp
    -- simp? [hp] at h
    simp only [hp, Finset.not_mem_empty] at h
  ·
    exact multideg'_eq_multideg hp ▸ le_multideg' hp h
lemma multideg'_mul_le (pq_ne_zero: p * q ≠ 0):
  multideg' (p * q) pq_ne_zero ≤
      (multideg' p (ne_zero_and_ne_zero_of_mul pq_ne_zero).1) +
      (multideg' q (ne_zero_and_ne_zero_of_mul pq_ne_zero).2) := by
  have pqsup_nonempty :=
      Finset.nonempty_of_ne_empty ((support_zero_iff (p * q)).not.mp pq_ne_zero)
  unfold multideg'
  have mul_sup := support_mul p q
  have h :=
    mem_of_subset mul_sup (max'_mem (α:=TermOrder (σ→₀ℕ)) _ pqsup_nonempty)
  rw [Finset.mem_bunionᵢ] at h
  rcases h with ⟨a, ha, h⟩
  rw [Finset.mem_bunionᵢ] at h
  rcases h with ⟨b, hb, h⟩
  rw [Finset.mem_singleton] at h
  rw [h]
  apply add_le_add
  ·exact Finset.le_max' (α:=TermOrder (σ→₀ℕ)) _ _ ha
  ·exact Finset.le_max' (α:=TermOrder (σ→₀ℕ)) _ _ hb

lemma multideg_mul_le: multideg (p * q) ≤ multideg p + multideg q := by
  by_cases hpq: p * q = 0
  ·exact hpq.symm ▸ ZeroLEClass.zero_le (multideg p + multideg q)
  ·
    rw [←multideg'_eq_multideg hpq,
        ←multideg'_eq_multideg (ne_zero_and_ne_zero_of_mul hpq).1,
        ←multideg'_eq_multideg (ne_zero_and_ne_zero_of_mul hpq).2]
    exact multideg'_mul_le hpq
lemma coeff_multideg'_add_mul:
  (p * q).coeff (multideg' p p_ne_zero + multideg' q q_ne_zero) = lc p * lc q
  := by
  rw [coeff_mul]
  unfold lc
  -- simp? [p_ne_zero, q_ne_zero]
  simp only [ne_eq, p_ne_zero, not_false_iff, dite_true, q_ne_zero]
  let deg'p: σ→₀ℕ := multideg' p p_ne_zero
  let deg'q: σ→₀ℕ := multideg' q q_ne_zero
  rw [Finset.sum_eq_add_sum_diff_singleton
        (i:=(deg'p, deg'q))
        (by rw [Finsupp.mem_antidiagonal])]
  rw [(_: 
      ((deg'p + deg'q).antidiagonal \ {(deg'p, deg'q)}).sum
        (fun x => p.coeff x.1 * q.coeff x.2) = 0
      )]
  exact add_zero _
  rw [←Finset.sum_coe_sort]
  let s :=
    (deg'p + deg'q).antidiagonal \ ({(deg'p, deg'q)}: Finset ((σ→₀ℕ)×(σ→₀ℕ)))
  have:
    ∀(i: s), p.coeff (i:(σ→₀ℕ)×(σ→₀ℕ)).1 * q.coeff (i:(σ→₀ℕ)×(σ→₀ℕ)).2 = 0
  := by
    -- simp? [-not_and]
    simp only [Subtype.forall, Finsupp.mem_antidiagonal, not_true,
                Finset.mem_sdiff, Finset.mem_singleton, and_imp, Prod.forall,
                Prod.mk.injEq]
    rintro (a: TermOrder (σ→₀ℕ)) (b: TermOrder (σ→₀ℕ)) hab hab'
    by_contra'
    let ⟨ha, hb⟩ := ne_zero_and_ne_zero_of_mul this
    rw [←mem_support_iff] at ha
    rw [←mem_support_iff] at hb
    have ha' := le_multideg' p_ne_zero ha
    have hb' := le_multideg' q_ne_zero hb
    by_cases ha: a = deg'p
    ·
      rw [ha] at hab
      have hb:= add_left_cancel hab
      exact hab' ⟨ha, hb⟩
    ·
      have key :=
        calc
          deg'p + deg'q
          _ = a + b := hab.symm
          _ < multideg' p _ + b := add_lt_add_right (lt_of_le_of_ne ha' ha) b
      exact ((lt_iff_not_ge _ _).mp (lt_of_add_lt_add_left key)) hb'
  -- simp? [this]
  simp only [Finset.sum_const_zero, this]
lemma multideg'_mul [NoZeroDivisors R]:
  multideg' (p*q) (mul_ne_zero_iff.mpr ⟨p_ne_zero, q_ne_zero⟩) =
    p.multideg' p_ne_zero + q.multideg' q_ne_zero
  := by
  have pq_ne_zero := mul_ne_zero_iff.mpr ⟨p_ne_zero, q_ne_zero⟩
  rw [le_antisymm_iff]
  constructor
  ·exact multideg'_mul_le pq_ne_zero
  ·
    -- conv_rhs => rw [multideg']
    apply Finset.le_max'
    refine mem_support_iff.mpr ?_
    rw [coeff_multideg'_add_mul p_ne_zero q_ne_zero]
    -- simp? [p.lc_eq_zero_iff.not.mpr p_ne_zero, q.lc_eq_zero_iff.not.mpr q_ne_zero]
    simp only [ne_eq, mul_eq_zero, p.lc_eq_zero_iff.not.mpr p_ne_zero,
                q.lc_eq_zero_iff.not.mpr q_ne_zero, or_self, not_false_iff]

lemma multideg_add_le_right
    {p q: MvPolynomial σ R} (h: multideg p <= multideg q):
  multideg (p + q) ≤ multideg q := by
  simp only [ne_eq, ge_iff_le, le_max_iff]
  conv_lhs => unfold multideg
  -- simp?
  simp only [ne_eq, Finset.sup_le_iff, id_eq]
  intros b hb
  rw [mem_support_iff, coeff_add] at hb
  by_contra hq
  -- simp? at hq
  simp only [ne_eq, not_le] at hq
  apply hb
  rw [coeff_eq_zero_of_multideg_lt hq,
      coeff_eq_zero_of_multideg_lt (lt_of_le_of_lt h hq), add_zero]

lemma multideg_add_le_left
    {p q: MvPolynomial σ R} (h: multideg q <= multideg p):
  multideg (p + q) ≤ multideg p := add_comm p q ▸ multideg_add_le_right h

lemma multideg_add_le: multideg (p+q) ≤ max p.multideg q.multideg := by
  -- simp?
  simp only [ne_eq, ge_iff_le, le_max_iff]
  by_cases h: multideg p <= multideg q
  ·
    right
    exact multideg_add_le_right h
  ·
    left
    -- simp? at h
    simp only [ne_eq, not_le] at h
    exact multideg_add_le_left (le_of_lt h)

lemma multideg_add_eq_right
    {p q: MvPolynomial σ R} (h: multideg p < multideg q):
  multideg (p+q) = multideg q := by
  have q_ne_zero :=
    ne_zero_of_multideg_ne_zero $ ne_bot_of_gt h
  have h₁: coeff (multideg q) (p + q) ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_multideg_lt h, zero_add, ←lc_def']
    exact (lc_eq_zero_iff q).not.mpr q_ne_zero
  have pq_ne_zero : p + q ≠ 0 := ne_zero_iff.mpr ⟨q.multideg, h₁⟩
  apply Eq.symm
  rw [←multideg'_eq_multideg pq_ne_zero, multideg'_iff]
  constructor
  ·exact h₁
  ·
    intros s' hs'
    rw [coeff_add,
        coeff_eq_zero_of_multideg_lt hs',
        coeff_eq_zero_of_multideg_lt (lt_trans h hs'),
        zero_add]
    
lemma multideg_add_eq_left
    {p q: MvPolynomial σ R} (h: multideg q < multideg p):
  multideg (p+q) = multideg p :=
  add_comm p q ▸ multideg_add_eq_right h

lemma multideg_add_eq (h: multideg p ≠ multideg q):
  multideg (p+q) = max p.multideg q.multideg := by
  --  ne_iff_lt_or_gt.mp h
  sorry
  


lemma multideg_add_eq_iff (h: lt p + lt q ≠ 0):
  multideg (p+q) = max p.multideg q.multideg := by
  sorry



-- def subpoly_le: