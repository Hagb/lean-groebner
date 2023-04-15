import Mathlib.Data.MvPolynomial.Basic
-- import Mathlib.Data.MvPolynomial.Division
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Basic
-- import Mathlib.Algebra.BigOperators.Ring
-- import Mathlib.Algebra.Module.Submodule.Basic
-- import Mathlib.RingTheory.Ideal.Basic
-- import Mathlib.LinearAlgebra.Finsupp
-- import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice
-- import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Basic
-- import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Data.Finsupp.Order
-- import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.List.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.RingTheory.Polynomial.Basic

import Basic
import Ideal
import TermOrder

open BigOperators
open Classical

namespace MvPolynomial

variable {σ : Type _}
variable {s : σ →₀ ℕ}
variable {k : Type _}

variable [Finite σ]


section Deg

variable [LinearOrder (TermOrder (σ →₀ ℕ))]
variable [CovariantClass (TermOrder (σ→₀ℕ)) (TermOrder (σ→₀ℕ)) (·+·) (·≤·)]
variable [ZeroLEClass (TermOrder (σ→₀ℕ))]
variable [IsWellOrder (TermOrder (σ→₀ℕ)) (@LT.lt (TermOrder (σ→₀ℕ)) _)]

variable [CommSemiring R] -- Note to myself: The CommSemiring has 1
variable (I : Ideal (MvPolynomial σ R))
variable (p q: MvPolynomial σ R)
variable (p_ne_zero: p ≠ 0)
variable (q_ne_zero: q ≠ 0)

def deg: TermOrder (σ →₀ ℕ) :=
  p.support.sup (α:=TermOrder (σ →₀ℕ)) id
#align mv_polynomial.deg MvPolynomial.deg

def deg' : TermOrder (σ →₀ ℕ) :=
  p.support.max' (α:=TermOrder (σ →₀ℕ)) (Finset.nonempty_of_ne_empty ((support_zero_iff p).not.mp p_ne_zero))
#align mv_polynomial.deg' MvPolynomial.deg'

@[simp]
def deg'_eq_deg: deg' p p_ne_zero = deg p := by
  unfold deg deg' Finset.max'
  -- simp only [Finset.coe_sup', Function.comp.right_id]
  -- library_search
  exact Finset.sup'_eq_sup (deg'.proof_1 p p_ne_zero) id

@[simp]
lemma deg_eq_zero_of_zero (hp: p = 0): deg p = 0 := by
  unfold deg
  rw [(support_zero_iff _).mp hp]
  exact Finset.sup_empty

@[simp]
lemma ne_zero_of_deg_ne_zero (hdeg: deg p ≠ 0): p ≠ 0 := by
  by_contra hp
  -- simp? [hp] at hdeg
  simp only [hp, deg_eq_zero_of_zero, ne_eq, not_true] at hdeg

noncomputable def lc : R :=
  if p_ne_zero': p ≠ 0
  then coeff (deg' p p_ne_zero') p
  else 0
#align mv_polynomial.lc MvPolynomial.lc

noncomputable def lt : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (deg' p p_ne_zero') (coeff (deg' p p_ne_zero') p)
  else 0
#align mv_polynomial.lt MvPolynomial.lt

noncomputable def ltOfSet (S: Set (MvPolynomial σ R)): Set (MvPolynomial σ R) :=
  { ltp | ∃ p ∈ S, ltp = lt p }

noncomputable def ltOfFinset (S: Finset (MvPolynomial σ R)): Finset (MvPolynomial σ R) :=
  S.filter (∃ p ∈ S, · = lt p)

noncomputable def supportListOfPoly (p: MvPolynomial σ R): List (TermOrder (σ→₀ℕ)) :=
  p.support.sort LE.le

noncomputable def ltOfIdeal : Ideal (MvPolynomial σ R) :=
  Ideal.span (ltOfSet I)
#align mv_polynomial.lt_of_ideal MvPolynomial.ltOfIdeal

lemma deg'_in_support: deg' p p_ne_zero ∈ p.support :=
  -- let supp: Finset (TermOrder (σ→₀ℕ)) := p.support
  (show Finset (TermOrder (σ→₀ℕ)) from p.support).max'_mem _
#align mv_polynomial.deg'_in_support MvPolynomial.deg'_in_support

lemma lc_zero_iff: lc p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hlc
    by_contra h
    -- simp? [h, lc] at hlc
    simp only [lc, ne_eq, h, not_false_iff, dite_true] at hlc
    exact (mem_support_iff.mp (deg'_in_support p h)) hlc
  ·
    intro hp
    rw [hp]
    rfl

lemma lt_zero_iff: lt p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hp
    -- simp? [lt] at hp
    simp only [lt, ne_eq, dite_not, dite_eq_left_iff, monomial_eq_zero] at hp
    by_contra hp'
    exact mem_support_iff.mp (deg'_in_support p hp') (hp hp')
  ·
    intro hp
    rw [hp]
    rfl

noncomputable def lm : MvPolynomial σ R :=
  if p_ne_zero': p ≠ 0
  then monomial (deg' p p_ne_zero') (1 : R)
  else 0
#align mv_polynomial.lm MvPolynomial.lm

noncomputable def lmOfFinset (S: Finset (MvPolynomial σ R)): Finset (MvPolynomial σ R) :=
  S.filter (∃ p ∈ S, · = lm p)

lemma lc_smul_lm_eq_lt: lc p • lm p =lt p := by
  unfold lc lm lt
  by_cases hp: p = 0
  ·
    -- simp? [hp]
    simp only [hp, ne_eq, not_true, coeff_zero, dite_eq_ite, ite_self, dite_false, smul_zero, map_zero]
  ·
    -- simp? [hp]
    simp only [ne_eq, hp, not_false_iff, dite_true]
    rw [smul_monomial, mul_one]

lemma lm_zero_iff: lm p = 0 ↔ p = 0 := by
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

lemma deg'_mul_le (pq_ne_zero: p * q ≠ 0):
  deg' (p * q) pq_ne_zero ≤
      (deg' p (ne_zero_and_ne_zero_of_mul pq_ne_zero).1) +
      (deg' q (ne_zero_and_ne_zero_of_mul pq_ne_zero).2) := by
  have pqsup_nonempty := (Finset.nonempty_of_ne_empty ((support_zero_iff (p * q)).not.mp pq_ne_zero))
  unfold deg'
  have mul_sup := support_mul p q
  have hdeg := (Finset.mem_of_subset mul_sup (Finset.max'_mem (α:=TermOrder (σ→₀ℕ)) _ pqsup_nonempty))
  rw [Finset.mem_bunionᵢ] at hdeg
  rcases hdeg with ⟨a, ha, hdeg⟩
  rw [Finset.mem_bunionᵢ] at hdeg
  rcases hdeg with ⟨b, hb, hdeg⟩
  rw [Finset.mem_singleton] at hdeg
  rw [hdeg]
  apply add_le_add
  ·exact Finset.le_max' (α:=TermOrder (σ→₀ℕ)) _ _ ha
  ·exact Finset.le_max' (α:=TermOrder (σ→₀ℕ)) _ _ hb

lemma deg_mul_le: deg (p * q) ≤ deg p + deg q := by
  by_cases hpq: p * q = 0
  ·exact hpq.symm ▸ ZeroLEClass.zero_le (deg p + deg q)
  ·
    rw [←deg'_eq_deg _ hpq, ←deg'_eq_deg _ (ne_zero_and_ne_zero_of_mul hpq).1,
                             ←deg'_eq_deg _ (ne_zero_and_ne_zero_of_mul hpq).2]
    exact deg'_mul_le p q hpq

lemma le_deg' (i: TermOrder (σ→₀ℕ)) (h: i ∈ p.support): i ≤ p.deg' p_ne_zero
  := Finset.le_max' (α:=TermOrder (σ→₀ℕ)) p.support i h

lemma le_deg (i: TermOrder (σ→₀ℕ)) (h: i ∈ p.support): i ≤ p.deg := by
  by_cases hp: p = 0
  ·
    rw [support_zero_iff] at hp
    -- simp? [hp] at h
    simp only [hp, Finset.not_mem_empty] at h
  ·
    exact deg'_eq_deg p hp ▸ le_deg' p hp i h

lemma coeff_deg'_add_mul:
  (p * q).coeff (deg' p p_ne_zero + deg' q q_ne_zero) = lc p * lc q := by
  rw [coeff_mul]
  unfold lc
  -- simp? [p_ne_zero, q_ne_zero]
  simp only [ne_eq, p_ne_zero, not_false_iff, dite_true, q_ne_zero]
  let deg'p: σ→₀ℕ := deg' p p_ne_zero
  let deg'q: σ→₀ℕ := deg' q q_ne_zero
  rw [Finset.sum_eq_add_sum_diff_singleton (i:=(deg'p, deg'q))]
  ·
    have key: ((deg'p + deg'q).antidiagonal \ {(deg'p, deg'q)}).sum
                (fun x => p.coeff x.1 * q.coeff x.2)
              = 0:= by
      rw [←Finset.sum_coe_sort]
      let s := (deg'p + deg'q).antidiagonal \ ({(deg'p, deg'q)}: Finset ((σ→₀ℕ) × (σ→₀ℕ)))
      have: 
          ∀(i: s),
          p.coeff (↑i: (σ→₀ℕ) × (σ→₀ℕ)).1 * q.coeff (↑i: (σ→₀ℕ) × (σ→₀ℕ)).2 = 0:= by
        -- simp? [-not_and]
        simp only [Subtype.forall, Finsupp.mem_antidiagonal, not_true, Finset.mem_sdiff, Finset.mem_singleton,
                   and_imp, Prod.forall, Prod.mk.injEq]
        rintro (a: TermOrder (σ→₀ℕ)) (b: TermOrder (σ→₀ℕ)) hab hab'
        by_contra'
        let ⟨ha, hb⟩ := ne_zero_and_ne_zero_of_mul this
        rw [←mem_support_iff] at ha
        rw [←mem_support_iff] at hb
        have ha' := le_deg' p p_ne_zero a ha
        have hb' := le_deg' q q_ne_zero b hb
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
              _ < deg' p p_ne_zero + b := add_lt_add_right (lt_of_le_of_ne ha' ha) b
          exact ((lt_iff_not_ge _ _).mp (lt_of_add_lt_add_left key)) hb'
      simp only [this, Finset.sum_const_zero]
    rw [key]
    exact add_zero _
  ·rw [Finsupp.mem_antidiagonal]

lemma deg'_mul [IsDomain R]:
  deg' (p * q) (mul_ne_zero_iff.mpr ⟨p_ne_zero, q_ne_zero⟩) = (deg' p p_ne_zero) + (deg' q q_ne_zero) := by
  -- have psup_nonempty := Finset.nonempty_of_ne_empty $ (support_zero_iff p).not.mp p_ne_zero
  -- have qsup_nonempty := Finset.nonempty_of_ne_empty $ (support_zero_iff q).not.mp q_ne_zero
  have pq_ne_zero := mul_ne_zero_iff.mpr ⟨p_ne_zero, q_ne_zero⟩
  rw [le_antisymm_iff]
  constructor
  ·exact deg'_mul_le p q pq_ne_zero
  ·
    conv_rhs => rw [deg']
    have key: coeff (deg' p p_ne_zero + deg' q q_ne_zero) (p * q) ≠ 0 := by
      rw [coeff_deg'_add_mul p q p_ne_zero q_ne_zero]
      -- simp? [p.lc_zero_iff.not.mpr p_ne_zero, q.lc_zero_iff.not.mpr q_ne_zero]
      simp only [ne_eq, mul_eq_zero, p.lc_zero_iff.not.mpr p_ne_zero, q.lc_zero_iff.not.mpr q_ne_zero,
                 or_self, not_false_iff]
    apply Finset.le_max'
    exact mem_support_iff.mpr key

end Deg

section Reg

-- variable [LinearOrder (TermOrder (σ →₀ ℕ))]
-- variable [CovariantClass (TermOrder (σ→₀ℕ)) (TermOrder (σ→₀ℕ)) (·+·) (·≤·)]
-- variable [IsWellOrder (TermOrder (σ→₀ℕ)) (@LT.lt (TermOrder (σ→₀ℕ)) _)]
variable [term_order_class: TermOrderClass (TermOrder (σ→₀ℕ))]

variable [Field k]

variable (G: Finset (MvPolynomial σ k))
variable (res: MvPolynomial σ k) (G_ne_zero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

-- #print wellFoundedLT.
-- @[default_instance]
-- private instance TermOrder.isWellFoundedRelation: WellFoundedRelation (TermOrder (σ→₀ℕ)) := term_order_class.toWellFoundedRelation

noncomputable def Reg'
(p: MvPolynomial σ k)
(G': List (MvPolynomial σ k))
(next: TermOrder (σ →₀ ℕ)): MvPolynomial σ k
  :=
    let gs := (G'.filter (lt ·∣ monomial next 1)) --.filter (·≠ 0)
    if hsl: gs = []
    then p
    else
      let g: MvPolynomial σ k := gs.head!
      have gne0: g ≠ 0 := by
        have hdvd' := List.of_mem_filter (List.head!_mem_self hsl)
        have hdvd := of_decide_eq_true hdvd'
        have ltgne0 := ne_zero_of_dvd_ne_zero
                      ((monomial_eq_zero (s:=next) (b:=(1:k))).not.mpr (one_ne_zero (α:=k)))
                      hdvd
        exact (lt_zero_iff g).not.mp ltgne0
      let mdg: σ →₀ ℕ := deg' g gne0
      let next': σ →₀ ℕ := next
      let next_poly:= (p - (monomial (next' - mdg) (coeff next' p / lc g)) * g)
      let nexts: Finset (TermOrder (σ→₀ℕ)) := next_poly.support.filter (· < next)
      if h: nexts.Nonempty
      then Reg' next_poly G' (nexts.max' h)
      else next_poly
termination_by Reg' p G' next => next
decreasing_by exact (Finset.mem_filter.mp (nexts.max'_mem h)).2

#check 1

noncomputable def Reg''
(p: MvPolynomial σ k)
(G': List (MvPolynomial σ k))
-- (next: TermOrder (σ →₀ ℕ)): MvPolynomial σ k
  :=
    if hnext: ∃ next ∈ p.support, ∃ g ∈ G', lt g∣ monomial next 1
    then
      let nextset := p.support.filter (∃ g ∈ G', lt g∣ monomial · 1)
      let next := nextset.max' (α:=TermOrder (σ →₀ℕ)) (by sorry)
      let gs := (G'.filter (lt ·∣ monomial next 1)) --.filter (·≠ 0)
      if hsl: gs = []
      then p
      else
        let g: MvPolynomial σ k := gs.head!
        have gne0: g ≠ 0 := by
          have hdvd' := List.of_mem_filter (List.head!_mem_self hsl)
          have hdvd := of_decide_eq_true hdvd'
          have ltgne0 := ne_zero_of_dvd_ne_zero
                        ((monomial_eq_zero (s:=next) (b:=(1:k))).not.mpr (one_ne_zero (α:=k)))
                        hdvd
          exact (lt_zero_iff g).not.mp ltgne0
        let mdg: σ →₀ ℕ := deg' g gne0
        let next': σ →₀ ℕ := next
        let next_poly:= (p - (monomial (next' - mdg) (coeff next' p / lc g)) * g)
        Reg'' next_poly G'
    else p
termination_by Reg'' p G' =>
  (p.support.filter (∃ g ∈ G', lt g∣ monomial · 1)).sup (α:=TermOrder (σ→₀ℕ)) id
decreasing_by
  let f (p: MvPolynomial σ k) :=
    (p.support.filter (∃ g ∈ G', lt g∣ monomial · 1)).sup (α:=TermOrder (σ→₀ℕ)) id
  have : f next_poly < f p := by
    
    sorry
  exact this




variable (p: MvPolynomial σ k)

-- #check TermOrder.isWellFoundedRelation.rel

variable (G': List (MvPolynomial σ k)) (G'_ne_zero: ∀ g ∈ G', (g: MvPolynomial σ k) ≠ 0)
variable (next: TermOrder (σ →₀ ℕ))
variable (G: Finset (MvPolynomial σ k)) (G_ne_zero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

noncomputable def Reg: MvPolynomial σ k :=
  Reg' p G.toList (if h: p = 0 then 0 else deg' p h)

lemma zero_reg'_zero: Reg' (0: MvPolynomial σ k) G' next = 0 := by
  unfold Reg'
  -- apply dite_eq_iff.mpr
  let gs := (G'.filter (lt ·∣ monomial next 1)) --.filter (·≠0)
  by_cases hg: gs = []
  ·--simp? [hg]
    simp only [hg, dite_true]
  ·-- simp? [hg]
    simp only [hg, coeff_zero, ge_iff_le, zero_div, map_zero, zero_mul, sub_self, support_zero,
               Finset.not_mem_empty, IsEmpty.forall_iff, forall_const, Finset.filter_true_of_mem,
               Finset.not_nonempty_empty, dite_false, dite_eq_ite, ite_self]

lemma zero_reg_zero: Reg (0: MvPolynomial σ k) G = 0 := by
  unfold Reg
  simp only [ne_eq, dite_true, zero_reg'_zero]


lemma eq_reg'_empty: Reg' p [] next = p := by
  unfold Reg'
  -- simp?
  simp only [List.filter_nil, ge_iff_le, Eq.ndrec, ne_eq, id_eq, dite_true]


def isReg (p: MvPolynomial σ k) (G: Finset (MvPolynomial σ k)) (r: MvPolynomial σ k)
:=  (∀ g ∈ G, ∀ rs ∈ r.support, lt g ∣ monomial rs 1) ∧
    ∃(q: MvPolynomial σ k → MvPolynomial σ k), 
      (∀ (g: MvPolynomial σ k) (_: g ∈ G) (hqg: (q g) * g ≠ 0),
         ∃ (hp: p ≠ 0), ((q g) * g).deg' hqg ≤ p.deg' hp
      )  ∧      
      p = r + ∑ g in G, (q g) * g

lemma reg_dvd : ∀ g ∈ G, ∀ rs ∈ (Reg p G).support, lt g ∣ monomial rs 1 := by
  intros g hg rs hrs
  -- unfold Reg at hrs
  sorry


theorem reg_iff (r: MvPolynomial σ k): r = Reg p G ↔ isReg p G r:= by
  constructor
  ·
    intro hr
    rw [hr]
    unfold isReg
    -- constructor
    -- ·
    --   unfold Reg
    --   intros g hg rs hrs
    --   -- unfold Reg'
    --   simp at hrs
    --   by_cases hp: p=0
    --   ·

    sorry
  sorry


theorem reg_unique: ∃! (r: MvPolynomial σ k), isReg p G r := by
  use Reg p G
  constructor
  ·
    simp only
    rw [←reg_iff]
  ·
    simp only
    intro r' hr'
    exact (reg_iff p G r').mpr hr'

end Reg

end MvPolynomial