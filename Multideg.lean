import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.CommRing
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
-- #align mv_polynomial.multideg MvPolynomial.multideg

def multideg' : TermOrder (σ →₀ ℕ) :=
p.support.max' (α:=TermOrder (σ→₀ℕ))
(Finset.nonempty_of_ne_empty (support_eq_empty.not.mpr p_ne_zero))
-- #align mv_polynomial.multideg' MvPolynomial.multideg'

def multideg'' : WithBot (TermOrder (σ→₀ℕ)) :=
  p.support.max (α:=TermOrder (σ→₀ℕ))

noncomputable def leading_coeff : R :=
  if p_ne_zero': p ≠ 0
  then coeff (multideg' p p_ne_zero') p
  else 0
#align mv_polynomial.leading_coeff MvPolynomial.leading_coeff


noncomputable def leading_term : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (multideg' p p_ne_zero') (coeff (multideg' p p_ne_zero') p)
  else 0
#align mv_polynomial.leading_term MvPolynomial.leading_term

noncomputable def lm : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (multideg' p p_ne_zero') (1 : R)
  else 0
#align mv_polynomial.lm MvPolynomial.lm

-- instance WithBot (TermOrder (σ→₀ℕ))

-- set_option trace.Meta.synthInstance true in
-- #check (inferInstance : WellFoundedRelation (WithBot (TermOrder (σ→₀ℕ))))

lemma multideg_apply :
multideg p = p.support.sup (α:=TermOrder (σ→₀ℕ)) (β:=TermOrder (σ→₀ℕ)) id
  := rfl

lemma multideg'_apply :
multideg' p p_ne_zero = p.support.max' (α:=TermOrder (σ→₀ℕ))
(Finset.nonempty_of_ne_empty (support_eq_empty.not.mpr p_ne_zero)) := rfl

lemma multideg''_apply :
  p.multideg'' = p.support.max (α:=TermOrder (σ→₀ℕ)) := rfl

lemma multideg'_eq_multideg {p: MvPolynomial σ R} (p_ne_zero: p ≠ 0):
  multideg' p p_ne_zero = multideg p := by
  unfold multideg multideg' Finset.max'
  -- library_search
  exact Finset.sup'_eq_sup (multideg'.proof_1 p p_ne_zero) id


lemma multideg''_def :
  p.multideg'' =
    if p = 0 then (⊥:  WithBot (TermOrder (σ →₀ ℕ))) else p.multideg :=
by
  by_cases hp : p = 0
  ·
    simp [multideg'', hp]
  ·
    -- simp? [multideg'', hp, ←multideg'_eq_multideg hp, Finset.max, multideg']
    simp only [multideg'', Finset.max, ← multideg'_eq_multideg hp,
              multideg', ne_eq, hp, ite_false]
    rw [Finset.max'_eq_sup', coe_sup']
    rfl


lemma multideg'_eq_multideg'' {p : MvPolynomial σ R} (p_ne_zero: p ≠ 0):
  p.multideg' p_ne_zero = p.multideg'' := by
  simp [p_ne_zero, multideg''_def, multideg'_eq_multideg]


@[simp]
lemma multideg_zero: multideg (0 : MvPolynomial σ R) = 0 := rfl

@[simp]
lemma multideg''_zero : multideg'' (0 : MvPolynomial σ R) = ⊥ := by
  unfold multideg''
  rw [support_eq_empty.mpr (rfl), max_empty]

@[simp]
lemma multideg_C: multideg (C a: MvPolynomial σ R) = 0 := by
  unfold multideg
  rw [C_apply, support_monomial]
  -- simp?
  simp only
  by_cases ha: a = 0
  · -- simp? [ha]
    simp only [ha, ite_true, sup_empty]
    rfl
  · -- simp? [ha]
    simp only [ha, ite_false, sup_singleton, id_eq]

@[simp]
lemma multideg''_C :
  multideg'' (C a : MvPolynomial σ R) = if a = 0 then ⊥ else 0 := by
  rw [multideg'', C_apply, support_monomial]
  by_cases ha : a = 0
  ·simp [ha]
  · simp [ha]
    rfl

lemma multideg_0: multideg (0: MvPolynomial σ R) = 0 := multideg_zero
lemma multideg''_0: multideg'' (0: MvPolynomial σ R) = ⊥ := multideg''_zero

@[simp]
lemma multideg_1: multideg (1: MvPolynomial σ R) = 0 := by
  rw [←C_1]
  exact multideg_C

@[simp]
lemma multideg''_1 [Nontrivial R] [Inhabited σ] : multideg'' (1 : MvPolynomial σ R) = 0 := by
  rw [multideg''_def]
  simp
  rfl

@[simp]
lemma multideg'_1 [Nontrivial R] [Inhabited σ]:
  multideg' (1 : MvPolynomial σ R) (one_ne_zero) = 0 := by
  rw [multideg'_eq_multideg]
  simp

@[simp]
lemma multideg'_1' (h1 : (1 : MvPolynomial σ R) ≠ 0):
  multideg' (1 : MvPolynomial σ R) h1 = 0 := by
  rw [multideg'_eq_multideg]
  simp

@[simp]
lemma ne_zero_of_multideg_ne_zero
  {p: MvPolynomial σ R} (h: multideg p ≠ 0):
  p ≠ 0 := by
  by_contra hp
  simp only [hp, multideg_zero, ne_eq, not_true] at h

lemma   coeff_eq_zero_of_multideg_lt {p: MvPolynomial σ R} (h: multideg p < s):
  coeff s p = 0 := by
  rw [←not_mem_support_iff]
  by_contra hs
  unfold multideg at h
  exact not_le_of_lt h (Finset.le_sup (f:=@id (TermOrder (σ→₀ℕ))) hs)

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

lemma multideg'_in_support: multideg' p p_ne_zero ∈ p.support :=
  (show Finset (TermOrder (σ→₀ℕ)) from p.support).max'_mem _
#align mv_polynomial.multideg'_in_support MvPolynomial.multideg'_in_support

lemma leading_coeff_def_of_p_ne_zero {p: MvPolynomial σ R} (p_ne_zero: p≠0):
  leading_coeff p = coeff (multideg' p p_ne_zero) p := by
  unfold leading_coeff
  -- simp? [p_ne_zero]
  simp only [ne_eq, p_ne_zero, not_false_iff, multideg'_eq_multideg,
            dite_eq_ite, ite_true]

lemma multideg_mem_support_iff_p_ne_zero :
  p.multideg ∈ p.support ↔ p ≠ 0 := by
  constructor
  ·
    intro h
    exact support_eq_empty.not.mp (Finset.ne_empty_of_mem h)
  ·
    intro h
    rw [←multideg'_eq_multideg h]
    exact multideg'_in_support p h

lemma lm_def_of_ne_zero {p : MvPolynomial σ R} (h : p ≠ 0) :
  p.lm = monomial p.multideg 1 := by simp [lm, h, multideg'_eq_multideg]

@[simp]
lemma leading_coeff_eq_zero_iff: leading_coeff p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hlc
    by_contra h
    -- simp? [h, lc] at hlc
    simp only [leading_coeff, ne_eq, h, not_false_iff, dite_true] at hlc
    exact (mem_support_iff.mp (multideg'_in_support p h)) hlc
  ·
    intro hp
    rw [hp]
    rfl

lemma leading_coeff_def: leading_coeff p = coeff (multideg p) p := by
  by_cases hp: p = 0
  ·
    rw [hp]
    -- simp? [leading_coeff_eq_zero_iff]
    simp only [multideg_zero, coeff_zero, leading_coeff_eq_zero_iff]
  ·
    unfold leading_coeff
    -- simp? [hp, multideg'_eq_multideg]
    simp only [ne_eq, hp, not_false_iff, multideg'_eq_multideg,
              dite_eq_ite, ite_true]

lemma multideg'_iff {p: MvPolynomial σ R} (p_ne_zero: p ≠ 0):
  s = multideg' p p_ne_zero ↔ (p.coeff s ≠ 0 ∧ ∀ s' > s, p.coeff s' = 0)
  := by
  constructor
  ·
    intros hs
    rw [hs, ←leading_coeff_def_of_p_ne_zero p_ne_zero]
    constructor
    ·exact (leading_coeff_eq_zero_iff p).not.mpr p_ne_zero
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
      rw [←leading_coeff_def_of_p_ne_zero p_ne_zero] at hs'
      exact p_ne_zero ((leading_coeff_eq_zero_iff p).mp hs')

@[simp]
lemma leading_term_eq_zero_iff: leading_term p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hp
    -- simp? [leading_term] at hp
    simp only [leading_term, ne_eq, dite_not, dite_eq_left_iff,
                monomial_eq_zero] at hp
    by_contra hp'
    exact mem_support_iff.mp (multideg'_in_support p hp') (hp hp')
  ·
    intro hp
    rw [hp]
    rfl

@[simp]
lemma leading_term_0 : leading_term (0 : MvPolynomial σ R) = 0 := by
  -- simp?
  simp only [ne_eq, leading_term_eq_zero_iff]


lemma leading_term_def:
  leading_term p = monomial (multideg p) p.leading_coeff := by
  by_cases hp: p = 0
  ·
    -- simp? [leading_term_eq_zero_iff, leading_coeff, hp]
    simp only [multideg_zero, leading_coeff, ne_eq, not_true, coeff_zero, hp,
                dite_eq_ite, ite_self, map_zero, leading_term_eq_zero_iff]
  ·
    -- simp? [hp, multideg'_eq_multideg, leading_term, leading_coeff]
    simp only [leading_term, ne_eq, hp, not_false_eq_true,
                multideg'_eq_multideg, dite_eq_ite, ite_true, leading_coeff]

lemma leading_term_def' :
  p.leading_term = p.leading_coeff • p.lm := by
  rw [leading_term_def, lm]
  by_cases h : p = 0
  ·simp [h]
  ·simp [h, multideg'_eq_multideg]


lemma leading_coeff_smul_lm_eq_leading_term:
  leading_coeff p • lm p =leading_term p := by
  unfold leading_coeff lm leading_term
  by_cases hp: p = 0
  ·
    -- simp? [hp]
    simp only [hp, ne_eq, coeff_zero, dite_eq_ite, dite_false, smul_zero]
  ·
    -- simp? [hp]
    simp only [ne_eq, hp, not_false_iff, dite_true]
    rw [smul_monomial, smul_eq_mul, mul_one]


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

lemma multideg_le_iff_multideg''_le {s : TermOrder (σ→₀ℕ)} :
  p.multideg'' ≤ s ↔ p.multideg ≤ s := by
  by_cases hp : p = 0
  ·simp [hp]
  ·simp [←multideg'_eq_multideg'' hp, multideg'_eq_multideg]

lemma le_multideg_of_le_multideg'' {s : TermOrder (σ→₀ℕ)}
  (h : s ≤ p.multideg'') : s ≤ p.multideg := by
  by_cases hp : p = 0
  ·simp [hp] at h
  · simp [←multideg'_eq_multideg'' hp, multideg'_eq_multideg] at h
    exact h

lemma multideg_le_multideg_of_multideg''_le_multideg''
  (h : p.multideg'' ≤ q.multideg'') : p.multideg ≤ q.multideg := by
  by_cases hp : p = 0
  ·simp [hp]
  · by_cases hq : q = 0
    ·simp [hq, multideg''_def, hp] at h
    · simp [←multideg'_eq_multideg'', hp, hq, multideg'_eq_multideg] at h
      exact h


lemma le_multideg' {i: TermOrder (σ→₀ℕ)} (h: i ∈ p.support):
  i ≤ p.multideg' p_ne_zero
  := Finset.le_max' (α:=TermOrder (σ→₀ℕ)) p.support i h

lemma le_multideg'' {i: TermOrder (σ→₀ℕ)} (h: i ∈ p.support):
  i ≤ p.multideg'' := by
  by_cases hp : p = 0
  · simp [hp] at h
  · simp [←multideg'_eq_multideg'' hp, le_multideg' hp h]

lemma le_multideg {i: TermOrder (σ→₀ℕ)} (h: i ∈ p.support): i ≤ p.multideg
  := by
  by_cases hp: p = 0
  ·
    rw [←support_eq_empty] at hp
    -- simp? [hp] at h
    simp only [hp, Finset.not_mem_empty] at h
  ·
    exact multideg'_eq_multideg hp ▸ le_multideg' hp h

theorem multideg'_mul_le (pq_ne_zero: p * q ≠ 0):
  multideg' (p * q) pq_ne_zero ≤
      (multideg' p (ne_zero_and_ne_zero_of_mul pq_ne_zero).1) +
      (multideg' q (ne_zero_and_ne_zero_of_mul pq_ne_zero).2) := by
  have pqsup_nonempty :=
    Finset.nonempty_of_ne_empty (support_eq_empty.not.mpr pq_ne_zero)
  unfold multideg'
  have mul_sup := support_mul p q
  have h :=
    mem_of_subset mul_sup (max'_mem (α:=TermOrder (σ→₀ℕ)) _ pqsup_nonempty)
  rw [Finset.mem_biUnion] at h
  rcases h with ⟨a, ha, h⟩
  rw [Finset.mem_biUnion] at h
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
  (p * q).coeff (multideg' p p_ne_zero + multideg' q q_ne_zero) =
  leading_coeff p * leading_coeff q :=
by
  rw [coeff_mul]
  unfold leading_coeff
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
  let s := (deg'p + deg'q).antidiagonal \ {(deg'p, deg'q)}
  have: ∀(i: s),
          p.coeff (i:(σ→₀ℕ)×(σ→₀ℕ)).1 * q.coeff (i:(σ→₀ℕ)×(σ→₀ℕ)).2 = 0
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
    -- simp? [leading_coeff_eq_zero_iff, p_ne_zero, q_ne_zero]
    simp only [ne_eq, mul_eq_zero, leading_coeff_eq_zero_iff, p_ne_zero,
                q_ne_zero, or_self, not_false_eq_true]

lemma multideg''_mul [NoZeroDivisors R] :
  (p*q).multideg''  = p.multideg'' + q.multideg'' := by
  by_cases hpq : p = 0 ∨ q = 0
  ·cases' hpq with h h <;> simp [h]
  ·
    push_neg at hpq
    simp_rw [←multideg'_eq_multideg'' hpq.1, ←multideg'_eq_multideg'' hpq.2,
              ←multideg'_eq_multideg'' (mul_ne_zero_iff.mpr hpq)]
    rw [←WithBot.coe_add]
    simp [multideg'_mul hpq.1 hpq.2]

@[simp]
lemma multideg_eq_zero_iff: multideg q = 0 ↔ ∃ c : R, q = C c := by
  constructor
  ·
    intros hq
    rw [multideg_apply, ] at hq
    -- rw [zero_le'''] at this
    have := (Finset.sup_eq_bot_iff (α:=TermOrder (σ→₀ℕ)) id q.support).mp hq
    by_cases hq' : q.support.Nonempty
    ·
      have : q.support = {0} :=
          eq_singleton_iff_nonempty_unique_mem.mpr ⟨hq', this⟩
      use q.coeff 0
      rw [as_sum q]
      -- simp? [this]
      simp only [this, sum_singleton, monomial_zero', coeff_C, ite_true]
    ·
      use 0
      -- simp? [hq, ←support_eq_empty, not_nonempty_iff_eq_empty.mp hq']
      simp only [map_zero, ne_eq, ←support_eq_empty,
                  not_nonempty_iff_eq_empty.mp hq']
  ·
    rintro ⟨c, hq⟩
    -- simp? [hq]
    simp only [hq, multideg_C]

@[simp]
lemma leading_coeff_mul [NoZeroDivisors R]:
  leading_coeff (p * q) = leading_coeff p * leading_coeff q := by
  by_cases hpq: p * q = 0
  ·
    cases' (mul_eq_zero.mp hpq) with h h
    <;> simp [h, (leading_coeff_eq_zero_iff _).mpr]
  ·
    let ⟨p_ne_zero, q_ne_zero⟩ := mul_ne_zero_iff.mp hpq
    rw [←coeff_multideg'_add_mul]
    unfold leading_coeff
    -- simp? [p_ne_zero, q_ne_zero, multideg'_mul]
    simp only [ne_eq, mul_eq_zero, p_ne_zero, q_ne_zero, or_self,
              not_false_iff, multideg'_mul, dite_eq_ite, ite_true]
    exact p_ne_zero
    exact q_ne_zero
@[simp]
lemma leading_coeff_C: leading_coeff (C a: MvPolynomial σ R) = a := by
  rw [leading_coeff_def, multideg_C]
  -- simp?
  simp only [coeff_C, ite_true]

@[simp]
lemma leading_coeff_0: leading_coeff (0: MvPolynomial σ R) = 0 := rfl

@[simp]
lemma leading_coeff_1: leading_coeff (1: MvPolynomial σ R) = 1 :=
(C_1 (R:=R) (σ:=σ)).symm ▸ leading_coeff_C

@[simp]
lemma leading_term_1 : leading_term (1 : MvPolynomial σ R) = 1 := by
  simp [leading_term_def]
  rfl

lemma lm_mul [NoZeroDivisors R]: lm (p * q) = lm p * lm q := by
  by_cases hpq: p * q = 0
  ·
    cases' (mul_eq_zero.mp hpq) with h h <;> simp [h, (lm_eq_zero_iff _).mpr]
  ·
    let ⟨p_ne_zero, q_ne_zero⟩ := mul_ne_zero_iff.mp hpq
    simp [lm, p_ne_zero, q_ne_zero, multideg'_mul p_ne_zero q_ne_zero]

@[simp]
lemma lm_0 : lm (0 : MvPolynomial σ R) = 0 := by simp [lm]

@[simp]
lemma lm_1 : lm (1 : MvPolynomial σ R) = 1 := by
  rw [lm]
  by_cases h : 1 = (0 : MvPolynomial σ R)
  · simp [h]
  · simp [h]
    rfl

lemma leading_term_mul [NoZeroDivisors R]:
  leading_term (p * q) = leading_term p * leading_term q := by
  repeat rw [←leading_coeff_smul_lm_eq_leading_term]
  repeat rw [lm_mul, leading_coeff_mul]
  rw [smul_mul_smul]

noncomputable def MultiplicativeWithBotTermOrderMulZeroOneClass :
  MulZeroOneClass (Multiplicative (WithBot (TermOrder (σ →₀ ℕ)))) := {
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero := ⊥,
  zero_mul := by
    intro x
    let x : WithBot (TermOrder (σ →₀ ℕ)) := x
    show ⊥ + x = ⊥
    simp [WithBot.map_bot (·+x)]
  mul_zero := by
    intro x
    let x : WithBot (TermOrder (σ →₀ ℕ)) := x
    show x + ⊥ = ⊥
    simp [WithBot.map_bot (x+·)]
}

private noncomputable instance :
  MulZeroOneClass (Multiplicative (WithBot (TermOrder (σ →₀ ℕ)))) :=
MultiplicativeWithBotTermOrderMulZeroOneClass

noncomputable def multideg''MulHomo'
  [Nontrivial R] [Inhabited σ] [NoZeroDivisors R]:
  MvPolynomial σ R →*₀ Multiplicative (WithBot (TermOrder (σ→₀ℕ))) := {
    toFun := multideg'',
    map_zero' := multideg''_zero,
    map_one' := multideg''_1,
    map_mul' := fun x y => multideg''_mul (p:=x) (q:=y)
  }
noncomputable def leading_coeffMulHomo [NoZeroDivisors R]:
  MvPolynomial σ R →*₀ R :=
{
  toFun := leading_coeff
  map_one' := C_1 (R:=R) (σ:=σ) ▸ leading_coeff_C (a:=1)
  map_mul' := by simp only [leading_coeff_mul, forall_const]
  map_zero' := by simp [leading_coeff]
}

noncomputable def lmMulHomo [NoZeroDivisors R]:
  MvPolynomial σ R →*₀ MvPolynomial σ R :=
{
  toFun := lm,
  map_one' := lm_1,
  map_zero' := lm_0,
  map_mul' := fun p q => lm_mul (p:=p) (q:=q)
}

noncomputable def leading_termMulHomo [NoZeroDivisors R] :
  MvPolynomial σ R →*₀ MvPolynomial σ R :=
{
  toFun := leading_term,
  map_zero' := leading_term_0,
  map_one' := leading_term_1,
  map_mul' := fun x y => leading_term_mul (p:=x) (q:=y)
}

lemma multideg_add_le_right
    {p q: MvPolynomial σ R} (h: multideg p <= multideg q):
  multideg (p + q) ≤ multideg q := by
  -- conv_lhs => unfold multideg
  nth_rewrite 1 [multideg]
  -- simp?
  simp only [Finset.sup_le_iff, id_eq]
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

theorem multideg_add_le: multideg (p+q) ≤ max p.multideg q.multideg := by
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

theorem multideg''_add_le : multideg'' (p+q) ≤ max p.multideg'' q.multideg''
:= by
  by_cases h : p = 0 ∨ q = 0
  ·cases' h with h h <;> simp [h]
  ·
    by_cases hpq : p + q = 0
    ·simp [hpq]
    push_neg at h
    cases' h with hp hq
    rw [←multideg'_eq_multideg'' hp, ←multideg'_eq_multideg'' hq,
        ←multideg'_eq_multideg'' hpq, multideg'_eq_multideg,
          multideg'_eq_multideg, multideg'_eq_multideg]
    have := multideg_add_le (p:=p) (q:=q)
    simp at this
    simp [this]

lemma multideg_add_eq_right
    {p q: MvPolynomial σ R} (h: multideg p < multideg q):
  multideg (p+q) = multideg q := by
  have q_ne_zero :=
    ne_zero_of_multideg_ne_zero $ ne_bot_of_gt h
  have h₁: coeff (multideg q) (p + q) ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_multideg_lt h,
        zero_add, ←leading_coeff_def]
    exact (leading_coeff_eq_zero_iff q).not.mpr q_ne_zero
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

-- TODO: mathlib
theorem monomial_add {s : σ →₀ ℕ} {a b : R} :
    monomial s (a+b) = monomial s a + monomial s b :=
AddMonoidAlgebra.single_add s a b
lemma multideg_add_lt_left_iff (h : q.multideg ≤ p.multideg)
  (h₂: p + q ≠ 0):
  multideg (p+q) < p.multideg ↔ leading_term p + leading_term q = 0 := by
  rw [leading_term_def, leading_term_def]
  constructor
  · intro hpq
    have hcoeff : (p+q).coeff p.multideg = 0 := by
      rw [coeff_eq_zero_of_multideg_lt]
      exact hpq
    have p_ne_zero : p ≠ 0 := by
      apply ne_zero_of_multideg_ne_zero
      exact (ne_of_lt (lt_of_le_of_lt (zero_le''' (p+q).multideg) hpq)).symm
    have hdeg : p.multideg = q.multideg := by
      by_contra hdeg
      rw [coeff_add] at hcoeff
      rw [coeff_eq_zero_of_multideg_lt (lt_of_le_of_ne' h hdeg)] at hcoeff
      simp [←leading_coeff_def, p_ne_zero] at hcoeff
    rw [hdeg, ←monomial_add]
    rw [monomial_eq_zero, leading_coeff_def, leading_coeff_def,
        ←hdeg, ←coeff_add]
    exact hcoeff
  · intro hpq
    apply lt_of_le_of_ne (multideg_add_le_left h)
    by_contra hpq'
    by_cases hpq'' : p.multideg = q.multideg
    · rw [←hpq'', ←hpq', ←monomial_add, monomial_eq_zero] at hpq
      rw [leading_coeff_def, leading_coeff_def, ←hpq'', ←hpq'] at hpq
      rw [←coeff_add, ←leading_coeff_def, leading_coeff_eq_zero_iff] at hpq
      exact h₂ hpq
    · change @Ne (σ →₀ ℕ) p.multideg q.multideg at hpq''
      have hp := hpq.symm ▸ coeff_zero p.multideg
      simp [hpq''.symm] at hp
      have hq := hpq.symm ▸ coeff_zero q.multideg
      simp [hpq''] at hq
      simp [hp, hq] at h₂

lemma coeff_multideg'_ne_zero : p.coeff (p.multideg' p_ne_zero) ≠ 0 :=
mem_support_iff.mp (multideg'_in_support p p_ne_zero)

variable (p q : MvPolynomial σ R) (s : σ→₀ℕ) (a : R)

@[simp]
lemma multideg_monomial : multideg (monomial s a) = if a = 0 then 0 else s :=
by
  by_cases ha : a = 0
  ·-- simp? [ha]
    simp only [ha, map_zero, multideg_zero, ite_true]
  ·-- simp? [ha, multideg, support_monomial]
    simp only [multideg, support_monomial, ha, ite_false, sup_singleton, id_eq]

@[simp]
lemma multideg''_monomial :
  multideg'' (monomial s a) =
    if a = 0 then ⊥ else (s : WithBot (σ→₀ℕ)) :=
by
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha, multideg'', support_monomial]

@[simp]
lemma leading_coeff_monomial : leading_coeff (monomial s a) = a := by
  by_cases ha : a = 0 <;> simp [leading_coeff_def, multideg_monomial, ha]


@[simp] lemma multideg_leading_term : p.leading_term.multideg = p.multideg :=
by
  rw [leading_term_def]
  -- simp?
  simp only [ne_eq, multideg_monomial, leading_coeff_eq_zero_iff,
            ite_eq_left_iff, not_forall, exists_prop, monomial_eq_zero,
            ite_eq_right_iff]
  intro hp
  -- simp? [hp]
  simp only [hp, multideg_zero]

@[simp] lemma multideg''_leading_term : p.leading_term.multideg'' = p.multideg'' :=
by
  rw [leading_term_def]
  simp [multideg''_def]
  by_cases h : p = 0 <;> simp [h]

@[simp] lemma multideg_lm : p.lm.multideg = p.multideg := by
  rw [lm]
  by_cases h : p = 0
  ·-- simp? [h]
    simp only [h, ne_eq, not_true, dite_false, multideg_zero]
  ·
    -- simp? [h]
    simp only [ne_eq, h, not_false_eq_true, dite_true, multideg_monomial]
    by_cases if_trivial: Nontrivial R
    ·-- simp? [multideg'_eq_multideg]
      simp only [one_ne_zero, multideg'_eq_multideg, ite_false]
    ·
      have all_mem_eq := nontrivial_iff.not.mp if_trivial
      push_neg at all_mem_eq
      -- simp?[all_mem_eq 1 0,p.leading_coeff_eq_zero_iff.mp (all_mem_eq _ _)]
      simp only [all_mem_eq 1 0, ite_true, multideg_zero,
                  p.leading_coeff_eq_zero_iff.mp (all_mem_eq _ _)]

@[simp] lemma leading_term_leading_term :
  p.leading_term.leading_term = p.leading_term := by
  rw [leading_term_def]
  nth_rewrite 3 [leading_term_def]
  -- simp? [monomial_eq_monomial_iff]
  simp only [multideg_leading_term, monomial_eq_monomial_iff, true_and]
  left
  rw [leading_term_def]
  -- simp?
  simp only [leading_coeff_monomial]

lemma leading_term_mul'_right [NoZeroDivisors R]:
  (p * q).leading_term = (p.leading_term * q).leading_term := by
  rw [leading_term_mul, leading_term_mul, leading_term_leading_term]

lemma leading_term_mul'_left [NoZeroDivisors R]:
  (p * q).leading_term = (p * q.leading_term).leading_term := by
  rw [leading_term_mul, leading_term_mul, leading_term_leading_term]

variable {R : Type _} [CommRing R] (p q : MvPolynomial σ R)

@[simp] lemma multideg_neg : (-p).multideg = p.multideg := by
  rw [multideg, multideg]
  simp only [support_neg]

@[simp] lemma multideg''_neg : (-p).multideg'' = p.multideg'' := by
  rw [multideg'', multideg'']
  simp only [support_neg]

@[simp] lemma leading_coeff_neg : (-p).leading_coeff = -p.leading_coeff := by
  -- simp? [leading_coeff_def]
  simp only [leading_coeff_def, multideg_neg, coeff_neg]

@[simp] lemma leading_term_neg : (-p).leading_term = -p.leading_term := by
  rw [leading_term_def, leading_term_def]
  -- simp?
  simp only [multideg_neg, leading_coeff_neg, map_neg]

lemma multideg_sub_lt_left_iff
  {p q : MvPolynomial σ R} (h : q.multideg ≤ p.multideg) (h₂ : p - q≠0) :
  multideg (p - q) < p.multideg ↔ p.leading_term = q.leading_term := by

  rw [sub_eq_add_neg] at h₂
  rw [←multideg_neg (p:=q)] at h
  rw [sub_eq_add_neg, multideg_add_lt_left_iff h h₂, leading_term_neg]
  rw [add_neg_eq_zero]

@[simp] lemma coeff_lm_of_ne_zero (h : p ≠ 0):
  coeff p.multideg p.lm = 1 := by
  -- simp? [lm, h, multideg'_eq_multideg]
  simp only [lm._eq_1, ne_eq, multideg_eq_zero_iff, not_exists, h,
              not_false_eq_true, multideg'_eq_multideg, dite_eq_ite,
              ite_true, coeff_monomial]

@[simp]
lemma sub_multideg_le [CommRing R₁] {p q: MvPolynomial σ R₁}
  (h: multideg q ≤ multideg p) :
  multideg (q - q.coeff p.multideg • p.lm) ≤ multideg p := by
  rw [smul_eq_C_mul, sub_eq_add_neg, ←neg_mul (C (coeff (multideg p) q)) p.lm]
  refine le_trans multideg_add_le ?_
  by_cases hc : q.coeff p.multideg = 0
  ·-- simp? [h, hc]
    simp only [hc, map_zero, neg_zero, zero_mul, multideg_zero,
                ge_iff_le, zero_le''', max_eq_left, h]
  ·
    -- simp? [h]
    simp only [neg_mul, multideg_neg, ge_iff_le, max_le_iff, h, true_and]
    refine le_trans multideg_mul_le ?_
    -- simp? [multideg_lm]
    simp only [multideg_C, multideg_lm, zero_add, le_refl]

@[simp]
lemma sub_multideg_lt [CommRing R₁] {p q: MvPolynomial σ R₁} (hp: p ≠ 0)
  (h: multideg q ≤ multideg p) :
  q - q.coeff p.multideg • lm p = 0 ∨
  multideg (q - q.coeff p.multideg • lm p) < multideg p := by
  by_cases h' : q - q.coeff p.multideg • lm p = 0
  ·
    left
    exact h'
  ·
    right
    apply lt_of_le_of_ne (sub_multideg_le h)
    by_contra hp'
    rw [←(leading_coeff_eq_zero_iff _).not, leading_coeff_def, hp'] at h'
    simp [hp] at h'


@[simp]
lemma sub_multideg''_lt [CommRing R₁] {p q: MvPolynomial σ R₁} (hp: p ≠ 0)
  (h: multideg q ≤ multideg p) :
  multideg'' (q - q.coeff p.multideg • lm p) < multideg'' p := by
  -- simp? [multideg''_def, hp]
  simp only [multideg''_def, ne_eq, multideg_eq_zero_iff,
              not_exists, hp, ite_false]
  by_cases h' : q - q.coeff p.multideg • lm p = 0
  ·
    -- simp? [h', WithBot.bot_lt_coe]
    simp only [h', multideg_zero, ite_true, WithBot.bot_lt_coe]
  ·
    -- simp? [hp, h']
    simp only [ne_eq, multideg_eq_zero_iff, not_exists, h',
                ite_false, WithBot.coe_lt_coe]
    exact (or_iff_right h').mp (sub_multideg_lt hp h)
