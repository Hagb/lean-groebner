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
-- import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.WellFounded
import LeanTryingMultivariable
import TermOrder

open BigOperators
open Classical
namespace MvPolynomial

variable {k : Type _} [Field k]

variable {σ : Type _} {r : σ → σ → Prop}

variable {s : σ →₀ ℕ}

variable (p : MvPolynomial σ k)

variable (p_nonzero : p ≠ 0)

variable (I : Ideal (MvPolynomial σ k))

class IsTermOrder (σ : Type _) [Finite σ]
  extends LinearOrder (TermOrder (σ →₀ ℕ)),
          IsWellOrder (TermOrder (σ→₀ℕ)) (@LT.lt (TermOrder (σ→₀ℕ)) _)
          where
  Additive : ∀ v v₁ v₂ : TermOrder (σ →₀ ℕ), v₁ ≤ v₂ → v + v₁ ≤ v + v₂
  zero_le : ∀ v : TermOrder (σ →₀ ℕ), 0 ≤ v
  -- IsWellOrder: IsWellOrder (TermOrder (σ→₀ℕ)) LT.lt

variable [Finite σ]
-- variable [LinearOrder (TermOrder (σ →₀ ℕ))]
-- variable [IsWellOrder (TermOrder (σ→₀ℕ)) (@LT.lt (TermOrder (σ→₀ℕ)) _)]
variable [term_order_class: IsTermOrder σ]

-- variable [DecidableRel (@LT.lt (TermOrder (σ →₀ ℕ)) Preorder.toLT)]
-- #check decidableLT_of_decidableLE
-- instance wellFoundedLT: WellFoundedLT (TermOrder (σ →₀ ℕ)) := by
--   constructor
--   constructor
--   intros a
--   constructor
--   sorry
  -- sorry

-- #check term_order_class.IsWellOrder.WellFoundedRelation

def multideg : TermOrder (σ →₀ ℕ) :=
  let supp : Finset (TermOrder (σ →₀ℕ)) := p.support
  supp.max' (Finset.nonempty_of_ne_empty ((support_zero_iff p).not.mp p_nonzero))
#align mv_polynomial.multideg MvPolynomial.multideg

noncomputable def lc : k :=
  if p_nonzero': p ≠ 0
  then coeff (multideg p p_nonzero') p
  else 0
#align mv_polynomial.lc MvPolynomial.lc

noncomputable def lm : MvPolynomial σ k :=
  if p_nonzero': p ≠ 0
  then monomial (multideg p p_nonzero') (1 : k)
  else 0
#align mv_polynomial.lm MvPolynomial.lm

noncomputable def lt : MvPolynomial σ k :=
  if p_nonzero': p ≠ 0
  then monomial (multideg p p_nonzero') (coeff (multideg p p_nonzero') p)
  else 0
#align mv_polynomial.lt MvPolynomial.lt

noncomputable def ltOfSet (S: Set (MvPolynomial σ k)): Set (MvPolynomial σ k) :=
  { ltp | ∃ p ∈ S, ltp = lt p }

noncomputable def ltOfFinset (S: Finset (MvPolynomial σ k)): Finset (MvPolynomial σ k) :=
  S.filter (∃ p ∈ S, · = lt p)

noncomputable def lmOfFinset (S: Finset (MvPolynomial σ k)): Finset (MvPolynomial σ k) :=
  S.filter (∃ p ∈ S, · = lm p)

noncomputable def supportListOfPoly (p: MvPolynomial σ k): List (TermOrder (σ→₀ℕ)) :=
  p.support.sort LE.le

noncomputable def ltOfIdeal : Ideal (MvPolynomial σ k) :=
  Ideal.span (ltOfSet I)
#align mv_polynomial.lt_of_ideal MvPolynomial.ltOfIdeal

theorem multideg_in_support : multideg p p_nonzero ∈ p.support :=
  let supp: Finset (TermOrder (σ→₀ℕ)) := p.support
  supp.max'_mem _
#align mv_polynomial.multideg_in_support MvPolynomial.multideg_in_support

variable (G: Finset (MvPolynomial σ k))
variable (res: MvPolynomial σ k) (G_nonzero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

-- #print wellFoundedLT.
@[default_instance]
private instance: WellFoundedRelation (TermOrder (σ→₀ℕ)) := term_order_class.toWellFoundedRelation

-- noncomputable def Reg'
--   (p: MvPolynomial σ k)
--   (G: List (MvPolynomial σ k))
--   (G_nonzero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)
--   (last: TermOrder (σ →₀ ℕ)):
--   MvPolynomial σ k
--   :=
--     let support_finset: Finset (TermOrder (σ→₀ℕ)) := p.support
--     let support_list: List (σ→₀ℕ) := ((support_finset.filter (· < last)).sort LE.le).reverse
--     let ss := (support_list.product G).filter fun ⟨ps, g⟩ =>
--                 lt g∣ monomial ps 1
--     if hsl: ss = []
--     then p
--     else
--       let pair := ss.head!
--       have hg : pair.1 ∈ support_list ∧ pair.2 ∈ G := by
--         apply (List.pair_mem_product.mp _)
--         rw [←Prod.fst_eq_iff.mp (by rfl: pair.1=pair.1)]
--         apply List.mem_of_mem_filter
--         exact List.head!_mem_self hsl
--       let tmp: σ →₀ ℕ := multideg pair.2 (G_nonzero pair.2 hg.2)
--       let next_poly:= (p - (monomial (pair.1 - tmp) (coeff pair.1 p / lc pair.2)) * pair.2)
--       Reg' next_poly
--            G
--            G_nonzero
--            pair.1
-- termination_by Reg' _ _ _ last => last
-- decreasing_by 
--   exact (Finset.mem_filter.mp (((support_finset.filter _).mem_sort _).mp (List.mem_reverse'.mp hg.1))).2



noncomputable def Reg'
(p: MvPolynomial σ k)
(G': List (MvPolynomial σ k)) (G'_nonzero: ∀ g ∈ G', (g: MvPolynomial σ k) ≠ 0)
(next: TermOrder (σ →₀ ℕ)): MvPolynomial σ k
  :=
    let gs := G'.filter (lt ·∣ monomial next 1)
    if hsl: gs = []
    then p
    else
      let g := gs.head!
      have gne0 : g ∈ G' := List.mem_of_mem_filter (List.head!_mem_self hsl)
      let mdg: σ →₀ ℕ := multideg g (G'_nonzero g gne0)
      let next': σ →₀ ℕ := next
      let next_poly:= (p - (monomial (next' - mdg) (coeff next' p / lc g)) * g)
      let nexts: Finset (TermOrder (σ→₀ℕ)) := next_poly.support.filter (· < next)
      if h: nexts.Nonempty
      then Reg' next_poly G' G'_nonzero (nexts.max' h)
      else next_poly
termination_by Reg' p G' G'_nonzero next => next
decreasing_by exact (Finset.mem_filter.mp (nexts.max'_mem h)).2
  -- exact test

variable (p: MvPolynomial σ k)
variable (G': List (MvPolynomial σ k)) (G'_nonzero: ∀ g ∈ G', (g: MvPolynomial σ k) ≠ 0)
variable (next: TermOrder (σ →₀ ℕ))
variable (G: Finset (MvPolynomial σ k)) (G_nonzero: ∀ g ∈ G, (g: MvPolynomial σ k) ≠ 0)

noncomputable def Reg: MvPolynomial σ k :=
  let G': List (MvPolynomial σ k) := (G.filter (· ≠ 0)).toList
  have G'_nonzero: ∀ g ∈ G', g ≠ 0 := by
    intros g hg
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hg)).2
  Reg' p G' G'_nonzero (if h: p = 0 then 0 else multideg p h)

lemma zero_reg'_zero: Reg' (0: MvPolynomial σ k) G' G'_nonzero next = 0 := by
  unfold Reg'
  -- apply dite_eq_iff.mpr
  let gs := List.filter (fun x => decide (lt x ∣ monomial next 1)) G'
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
-- lemma Finset.empty_forall_true {α: Type _} (prop: Prop): ∀ p ∈ (Finset.empty: Finset α), prop := by
--   intros p hp
--   exfalso
--   exact (Finset.not_mem_empty p) hp

-- lemma List.empty_forall_true {α: Type _} (prop: Prop): ∀ p ∈ ([]: List α), prop := by
--   intros p hp
--   apply List.forall_mem_nil _ _ hp

lemma eq_reg'_empty: Reg' p [] (List.forall_mem_nil _) next = p := by
  unfold Reg'
  -- simp?
  simp only [List.filter_nil, ge_iff_le, Eq.ndrec, ne_eq, id_eq, dite_true]


def isReg (p: MvPolynomial σ k) (G: Finset (MvPolynomial σ k)) (r: MvPolynomial σ k)
:= ∃(q: MvPolynomial σ k → MvPolynomial σ k), 
      (∀ (g: MvPolynomial σ k) (_: g ∈ G) (hqg: (q g) * g ≠ 0),
         ∃ (hp: p ≠ 0), ((q g) * g).multideg hqg ≤ p.multideg hp
      ) ∧
      (∀ g ∈ G, ∀ rs ∈ r.support, ¬ (monomial rs 1) ∣ lm g) ∧
      p = r + ∑ g in G, (q g) * g


theorem reg_iff (r: MvPolynomial σ k): isReg p G r ↔ r = Reg p G := by
  constructor
  ·
    intros ⟨hr, q⟩
  sorry

end MvPolynomial