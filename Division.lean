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
-- import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support

import Mathlib.Order.WellFounded
import Basic
import Ideal
import TermOrder

open BigOperators
open Classical
namespace MvPolynomial



variable {σ : Type _} {r : σ → σ → Prop}
variable {s : σ →₀ ℕ}
variable {k : Type _}

-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Override.20default.20ordering.20instance/near/339882298
class IsTermOrder (σ : Type _) [Finite σ]
  extends LinearOrder (TermOrder (σ →₀ ℕ)),
          IsWellOrder (TermOrder (σ→₀ℕ)) (@LT.lt (TermOrder (σ→₀ℕ)) _)
          -- TODO: IsWellOrder can be proved from Finite+LinearOrder+Additive+zero_le
          where
  Additive : ∀ v v₁ v₂ : TermOrder (σ →₀ ℕ), v₁ ≤ v₂ → v + v₁ ≤ v + v₂
  zero_le : ∀ v : TermOrder (σ →₀ ℕ), 0 ≤ v
  -- IsWellOrder: IsWellOrder (TermOrder (σ→₀ℕ)) LT.lt

variable [Finite σ]
variable [term_order_class: IsTermOrder σ]

section TermOrder

variable [CommSemiring R] -- Note to myself: The CommSemiring has 1
variable (I : Ideal (MvPolynomial σ R))
variable (p q: MvPolynomial σ R)
variable (p_nonzero: p ≠ 0)
variable (q_nonzero: q ≠ 0)

def multideg : TermOrder (σ →₀ ℕ) :=
  p.support.max' (α:=TermOrder (σ →₀ℕ)) (Finset.nonempty_of_ne_empty ((support_zero_iff p).not.mp p_nonzero))
#align mv_polynomial.multideg MvPolynomial.multideg

-- def multideg' : σ →₀ ℕ := multideg p p_nonzero

noncomputable def lc : R :=
  if p_nonzero': p ≠ 0
  then coeff (multideg p p_nonzero') p
  else 0
#align mv_polynomial.lc MvPolynomial.lc

noncomputable def lt : MvPolynomial σ R :=
  if p_nonzero': p ≠ 0
  then monomial (multideg p p_nonzero') (coeff (multideg p p_nonzero') p)
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

lemma multideg_in_support: multideg p p_nonzero ∈ p.support :=
  let supp: Finset (TermOrder (σ→₀ℕ)) := p.support
  supp.max'_mem _
#align mv_polynomial.multideg_in_support MvPolynomial.multideg_in_support

lemma lc_zero_iff: lc p = 0 ↔ p = 0 := by
  constructor
  ·
    intro hlc
    by_contra h
    -- simp? [h, lc] at hlc
    simp only [lc, ne_eq, h, not_false_iff, dite_true] at hlc
    exact (mem_support_iff.mp (multideg_in_support p h)) hlc
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
    exact mem_support_iff.mp (multideg_in_support p hp') (hp hp')
  ·
    intro hp
    rw [hp]
    rfl

noncomputable def lm : MvPolynomial σ R :=
  if p_nonzero': p ≠ 0
  then monomial (multideg p p_nonzero') (1 : R)
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

lemma mul_multideg [IsDomain R]:
  multideg (p * q) (mul_ne_zero_iff.mpr ⟨p_nonzero, q_nonzero⟩) = (multideg p p_nonzero) + (multideg q q_nonzero) := by
  unfold multideg
  rw [le_antisymm_iff]
  constructor
  ·
    -- simp?
    sorry
  ·
    sorry

end TermOrder

section Reg

variable [Field k]

variable (G: Finset (MvPolynomial σ k))
variable (res: MvPolynomial σ k) (G_nonzero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

-- #print wellFoundedLT.
@[default_instance]
private instance: WellFoundedRelation (TermOrder (σ→₀ℕ)) := term_order_class.toWellFoundedRelation

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
      let mdg: σ →₀ ℕ := multideg g gne0
      let next': σ →₀ ℕ := next
      let next_poly:= (p - (monomial (next' - mdg) (coeff next' p / lc g)) * g)
      let nexts: Finset (TermOrder (σ→₀ℕ)) := next_poly.support.filter (· < next)
      if h: nexts.Nonempty
      then Reg' next_poly G' (nexts.max' h)
      else next_poly
termination_by Reg' p G' next => next
decreasing_by exact (Finset.mem_filter.mp (nexts.max'_mem h)).2


variable (p: MvPolynomial σ k)
variable (G': List (MvPolynomial σ k)) (G'_nonzero: ∀ g ∈ G', (g: MvPolynomial σ k) ≠ 0)
variable (next: TermOrder (σ →₀ ℕ))
variable (G: Finset (MvPolynomial σ k)) (G_nonzero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

noncomputable def Reg: MvPolynomial σ k :=
  Reg' p G.toList (if h: p = 0 then 0 else multideg p h)

lemma zero_reg'_zero: Reg' (0: MvPolynomial σ k) G' next = 0 := by
  unfold Reg'
  -- apply dite_eq_iff.mpr
  let gs := (G'.filter (lt ·∣ monomial next 1)) --.filter (·≠0)
  by_cases hg: gs = []
  ·--simp? [hg]
    simp only [hg, dite_true]
  ·--simp? [hg]
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
         ∃ (hp: p ≠ 0), ((q g) * g).multideg hqg ≤ p.multideg hp
      )  ∧      
      p = r + ∑ g in G, (q g) * g


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