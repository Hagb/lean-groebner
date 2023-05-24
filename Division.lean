
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Division
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
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.ProdSigma
import Mathlib.RingTheory.Polynomial.Basic

import Basic
-- import Ideal
import TermOrder
import Multideg

open BigOperators
open Classical

lemma List.filter_eq_nil' {α : Type _} {p : α→Prop} {l : List α} :
  l.filter (fun x => decide (p x)) = [] ↔ ∀ a ∈ l , ¬p a := by
  conv =>
    enter [2, a, ha]
    rw [Iff.intro (decide_eq_true (p:=p a)) of_decide_eq_true]
  exact List.filter_eq_nil

lemma List.filter_ne_nil' {α : Type _} {p : α→Prop} {l : List α} :
  l.filter (fun x => decide (p x)) ≠ [] ↔ ∃ a ∈ l , p a := by
  have := (List.filter_eq_nil' (α:=α) (p:=p) (l:=l)).not
  push_neg at this
  exact this

lemma List.of_mem_filter' {α : Type _} {p : α→Prop} {a : α} {l : List α} :
  a ∈ l.filter (fun x => decide (p x)) → p a := by
  rw [Iff.intro (decide_eq_true (p:=p a)) of_decide_eq_true]
  exact of_mem_filter

namespace MvPolynomial
section MvDiv
variable {σ : Type _} {s : σ →₀ ℕ} {k : Type _} [Field k]
variable [term_order_class: TermOrderClass (TermOrder (σ→₀ℕ))]
variable (p: MvPolynomial σ k) (G: List (MvPolynomial σ k))

noncomputable def step:
(G.toFinset →₀ MvPolynomial σ k) × MvPolynomial σ k :=
  if p = 0 then ⟨0, 0⟩ else
  if hgs: ∃ g ∈ G, leading_term g∣ leading_term p
  then
    let gs := G.filter (leading_term ·∣ leading_term p)
    let g := gs.head!
    have gnonempty: gs ≠ [] := List.filter_ne_nil'.mpr hgs
    have hG: g ∈ G := List.mem_of_mem_filter (gs.head!_mem_self gnonempty)
    have hg: leading_term g ∣ leading_term p :=
      List.of_mem_filter' (a:=g) (gs.head!_mem_self gnonempty) -- a is needed
    ⟨Finsupp.single ⟨g, List.mem_toFinset.mpr hG⟩ hg.choose, p - g * hg.choose⟩
  else ⟨0, p⟩


def step_apply := by
  have key: p.step = p.step := rfl
  conv at key => rhs; unfold step
  exact key

@[simp]
lemma step_multideg_le:
  (p.step G).2.multideg ≤ p.multideg := by  
  unfold step
  by_cases hp : p = 0
  · -- simp? [hp]
    simp only [hp, zero_sub, ite_true, multideg_zero, le_refl]
  ·
    by_cases hgs: ∃ g ∈ G, leading_term g∣ leading_term p    
    ·-- simp? [hp, hgs]
      simp only [hp, ne_eq, hgs, dite_true, ite_false]
      rw [sub_eq_add_neg, neg_eq_neg_one_mul]
      apply multideg_add_le_left
      rw [←multideg_leading_term, leading_term_mul, leading_term_mul'_right]
      generalize_proofs _ h
      rw [←Exists.choose_spec h]
      -- simp?
      simp only [leading_term_neg, leading_term_1, leading_term_leading_term,
                neg_mul, one_mul, multideg_neg, multideg_leading_term, le_refl]
      -- simp only [lt_neg, leading_term_1, leading_term_leading_term, one_mul, multideg_leading_term, ne_eq, le_refl]    
    ·-- simp? [hgs, hp]
      simp only [hp, ne_eq, hgs, dite_false, ite_false, le_refl]
@[simp]
lemma step_sub_multideg''_lt
  {p: MvPolynomial σ k} (G: List (MvPolynomial σ k)) (hp: p ≠ 0):
  multideg'' ((p.step G).2 - coeff p.multideg (p.step G).2•lm p) < multideg'' p
:= sub_multideg''_lt hp (step_multideg_le p G)


@[simp]
lemma step_zero: (0: MvPolynomial σ k).step G = ⟨0, 0⟩ := by
  rw [step_apply]
  simp only [zero_sub, ite_true]

-- @[simp]
lemma ne_zero_of_step_quo_ne_zero (hp : (p.step G).2 ≠ 0) : p ≠ 0 := by
  by_contra h
  simp [h] at hp

-- lemma step_quo_dvd
--   (h : p≠0) (hg : ∃ g ∈ G, leading_term g∣ leading_term p):
--   (G.filter (leading_term ·∣ leading_term p)).head!.leading_term ∣
--   p.leading_term := sorry


-- lemma step_quo_ne_zero''
--   (h : p≠0) (hg : ∃ g ∈ G, leading_term g∣ leading_term p) :
--   (G.filter (leading_term ·∣ leading_term p)).head! ≠ 0 := by
--   let gs := G.filter (leading_term ·∣ leading_term p)
--   have : gs ≠ [] := List.filter_ne_nil'.mpr hg
--   by_contra h'
--   sorry

-- lemma step_quo_dvd_choose
--   (h : p≠0) (hg : ∃ g ∈ G, leading_term g∣ leading_term p):
--   (step_quo_dvd p G h hg).choose ≠ 0 := sorry
@[simp]
lemma step_sub_multideg_le
  {p: MvPolynomial σ k} (G: List (MvPolynomial σ k)):
  multideg ((p.step G).2- coeff p.multideg (p.step G).2 • lm p) ≤ multideg p
:= sub_multideg_le (step_multideg_le p G)

noncomputable def mv_div
(p: MvPolynomial σ k)
(G: List (MvPolynomial σ k))
: (G.toFinset →₀ MvPolynomial σ k) × MvPolynomial σ k
  :=
    if hp: p = 0 then ⟨0, p⟩ else
    let xs_r := step p G
    let xs'_r' := mv_div (xs_r.2 - coeff p.multideg xs_r.2 • lm p) G
    ⟨xs_r.1 + xs'_r'.1, xs'_r'.2 + coeff p.multideg xs_r.2 • lm p⟩
termination_by _ => multideg'' p
decreasing_by exact step_sub_multideg''_lt G hp

@[reducible]
noncomputable def quo: G.toFinset →₀ MvPolynomial σ k :=
  (mv_div p G).1

@[reducible]
noncomputable def rem: MvPolynomial σ k :=
  (mv_div p G).2


def mv_div_apply := by
  have key: p.mv_div G = p.mv_div G := rfl
  nth_rewrite 2 [mv_div] at key
  exact key

lemma quo_apply: quo p G = (mv_div p G).1 := rfl

lemma rem_apply: rem p G = (mv_div p G).2 := rfl


@[simp]
lemma step_empty: step p [] = ⟨0, p⟩ := by
  rw [step_apply]
  -- simp?
  simp only [ne_eq, List.find?, List.not_mem_nil, false_and, exists_false,
            List.filter_nil, dite_false,
  ite_eq_right_iff, Prod.mk.injEq, true_and]
  intro hp
  exact hp.symm

@[simp]
lemma mv_div_empty (p: MvPolynomial σ k): p.mv_div [] = ⟨0, p⟩ := by
  rw [mv_div_apply]
  -- simp?
  simp only [ne_eq, step_empty, zero_add, dite_eq_ite,
            ite_eq_left_iff, Prod.mk.injEq]
  intro hp
  rw [mv_div_empty (p - coeff (multideg p) p • lm p)]
  -- simp?
  simp only [ne_eq, sub_add_cancel, and_self]
termination_by mv_div_empty p => multideg'' p
decreasing_by
  --  ↓↓↓ Workaround to make lean remember the instance ↓↓↓
  let term_order_class := term_order_class -- Why should I do that??????
  exact sub_multideg''_lt hp le_rfl

@[simp]
lemma rem_empty (p: MvPolynomial σ k): rem p [] = p := by
  -- simp? [rem_apply]
  simp only [rem_apply, mv_div_empty]
  
@[simp]
lemma quo_empty (p: MvPolynomial σ k): quo p [] = 0 := by
  simp only [quo_apply, mv_div_empty]

@[simp]
lemma mv_div_zero: (0: MvPolynomial σ k).mv_div G = ⟨0, 0⟩ := by
  rw [mv_div_apply]
  simp only [step_zero, multideg_zero, coeff_zero, zero_smul, sub_self,
            zero_add, add_zero, Prod.mk.eta, dite_eq_ite, ite_true]

@[simp]
lemma quo_zero: quo (0: MvPolynomial σ k) G = 0 := by
  simp only [quo_apply, mv_div_zero]

@[simp]
lemma rem_zero: rem (0: MvPolynomial σ k) G = 0 := by
  simp only [rem_apply, mv_div_zero]

lemma step_quo_sum_add_rem: (p.step G).1.sum (·*·) + (p.step G).2 = p := by  
  unfold step
  by_cases hp: p = 0
  · --simp? [hp]
    simp only [hp, zero_sub, ite_true, add_zero]
    rw [Finsupp.sum_zero_index]
    -- simp only [hp, zero_sub, ite_true, Finsupp.sum_zero_index, add_zero]
  ·    
    by_cases hg: ∃ g, g ∈ G ∧ leading_term g ∣ leading_term p
    ·
      -- simp? [hp, hg]
      simp only [hp, ne_eq, hg, dite_true, ite_false, mul_zero,
                Finsupp.sum_single_index, add_sub_cancel'_right]
    ·    
      --simp? [hp, hg]
      simp only [hp, ne_eq, hg, dite_false, ite_false, zero_add]
      rw [Finsupp.sum_zero_index, zero_add]

@[simp]
lemma step_quo_sum_eq_sub_rem: (p.step G).1.sum (·*·) = p - (p.step G).2 := by
  rw [sub_eq_of_eq_add]
  exact (step_quo_sum_add_rem p G).symm

@[simp]
lemma quo_sum_eq_sub_rem (p: MvPolynomial σ k) (G: List (MvPolynomial σ k)):
  (p.quo G).sum (·*·) = p - p.rem G := by  
  rw [quo_apply, rem_apply, mv_div_apply]
  by_cases hp: p = 0
  ·-- simp? [hp]
    simp only [hp, multideg_zero, dite_eq_ite, ite_true,
                Finsupp.sum_zero_index, sub_self]
  ·-- simp? [hp]    
    simp only [hp, ne_eq, dite_eq_ite, ite_false]
    rw [Finsupp.sum_add_index]
    ·
      -- rw [←quo_apply]
      rw [quo_sum_eq_sub_rem
            ((step p G).snd - coeff (multideg p) (step p G).snd • lm p)
            G,
          step_quo_sum_eq_sub_rem]
      ring
    ·-- simp?
      simp only [ne_eq, Finset.mem_union, Finsupp.mem_support_iff, mul_zero,
                implies_true, Subtype.forall, forall_const]
    · intros a _ b₁ b₂
      exact mul_add (↑a: MvPolynomial σ k) b₁ b₂
termination_by _ => multideg'' p
decreasing_by exact step_sub_multideg''_lt G hp
  
theorem quo_quo_sum_add_rem: (p.quo G).sum (·*·) + p.rem G = p := by
  -- simp?
  simp only [quo_sum_eq_sub_rem, sub_add_cancel]

@[simp]
lemma step_multideg_quo_mul_le (hq: q ∈ G) :
   (q * ((p.step G).1 ⟨q, List.mem_toFinset.mpr hq⟩)).multideg ≤ p.multideg :=
by  
  rw [step_apply]
  by_cases hp: p = 0
  ·-- simp? [hp]
    simp only [hp, zero_sub, ite_true, Finsupp.coe_zero, Pi.zero_apply,
                mul_zero, multideg_zero, le_refl]
  ·    
    -- simp? [hp]
    simp only [hp, ne_eq, ite_false, mul_eq_zero]
    by_cases hg: ∃ g, g ∈ G ∧ leading_term g ∣ leading_term p
    ·-- simp? [hg, Finsupp.single_apply]
      simp only [hg, dite_true, ne_eq, Subtype.mk.injEq, Finsupp.single_apply,
                mul_ite, mul_zero, ite_eq_right_iff, mul_eq_zero]

      let g := List.head!
                (G.filter (fun x => decide (leading_term x ∣ leading_term p)))      
      by_cases hg : g = q
      ·
        -- simp? [hg]
        simp only [hg, ite_true, mul_eq_zero, ne_eq, ge_iff_le]
        generalize_proofs _ h
        rw [←multideg_leading_term, leading_term_mul'_right,
            multideg_leading_term, ←h.choose_spec, multideg_leading_term]      
      ·--simp? [hg]
        simp only [hg, ite_false, multideg_zero, zero_le''']    
    ·
      -- simp? [hg]
      simp only [hg, dite_false, Finsupp.coe_zero, Pi.zero_apply, mul_zero,
                multideg_zero, ne_eq, zero_le''']

theorem multideg_quo_mul_le (p : MvPolynomial σ k) (G : List (MvPolynomial σ k))
  (q: MvPolynomial σ k) (hq: q ∈ G):
  (q * (p.quo G ⟨q, List.mem_toFinset.mpr hq⟩)).multideg ≤ p.multideg :=
by  
  rw [quo_apply]
  unfold mv_div
  by_cases hp: p = 0
  ·
    -- simp? [hp]
    simp only [hp, multideg_zero, dite_eq_ite, ite_true,
              Finsupp.coe_zero, Pi.zero_apply, mul_zero, le_refl]  
  ·
    -- simp? [hp]
    simp only [hp, ne_eq, dite_eq_ite, ite_false, Finsupp.coe_add,
              Pi.add_apply, mul_eq_zero]
    rw [mul_add]    
    apply le_trans multideg_add_le
    -- simp? [step_multideg_quo_mul_le p G hq]
    simp only [mul_eq_zero, ne_eq, ge_iff_le, max_le_iff,
              step_multideg_quo_mul_le p G hq, true_and]
      -- Why step_multideg_quo_mul_le not work?
    rw [←quo_apply]    
    apply le_trans (multideg_quo_mul_le
                    ((p.step G).2 - (p.step G).2.coeff (multideg p) • lm p)
                    G q hq)
    exact step_sub_multideg_le G
termination_by _ => multideg'' p
decreasing_by exact step_sub_multideg''_lt G hp

lemma step_eq_iff (hp : p ≠ 0):
  (p.step G).2 = p ↔
  ∀ g ∈ G, g ≠ 0 → ¬ LE.le (α:=σ→₀ℕ) g.multideg p.multideg := by  
  constructor
  ·    
    intros h g hg hg'
    -- simp? [step_apply, hp] at h
    simp only [step_apply, ne_eq, multideg_eq_zero_iff,
              not_exists, hp, ite_false] at h
    by_cases hg's : ∃ g, g ∈ G ∧ leading_term g ∣ leading_term p
    ·      
      simp [hg's] at h
      -- simp [step_quo_ne_zero'' p G hp hg's] at h
      -- simp [step_quo_dvd_choose p G hp hg's] at h
      -- simp only [hg's, dite_true, sub_eq_self, mul_eq_zero,
      --           ne_eq, multideg_eq_zero_iff, not_exists] at h
      
      let g's := G.filter (leading_term ·∣ leading_term p)
      have gnonempty: g's ≠ [] :=  List.filter_ne_nil'.mpr (hg's)
      have := List.of_mem_filter (List.head!_mem_self gnonempty)
      have key := of_decide_eq_true this      
      cases' h with h h
      · exfalso
        rw [h] at key
        simp [hp, monomial_dvd_monomial, leading_term_def] at key
      · exfalso
        have key := h ▸ key.choose_spec
        simp [hp] at key
    ·      
      push_neg at hg's
      specialize hg's g hg
      simp [leading_term_def, hg', hp, monomial_dvd_monomial] at hg's
      rw [imp_iff_not_or] at hg's
      cases' hg's with hg's hg's
      ·exact hg's
      · exfalso
        rw [dvd_iff_exists_eq_mul_left, not_exists] at hg's
        apply hg's (p.leading_coeff / g.leading_coeff)
        rw [div_mul_cancel _ (g.leading_coeff_eq_zero_iff.not.mpr hg')]
  ·    
    intros hg
    simp [step_apply, hp]
    by_cases hg's : ∃ g, g ∈ G ∧ leading_term g ∣ leading_term p
    · exfalso
      rcases hg's with ⟨g',hg',hg'p⟩
      simp [monomial_dvd_monomial, leading_term_def, hp] at hg'p
      simp [(not_imp_not.mp (hg g' hg')) hg'p.1, hp] at hg'p
    ·
      simp [hg's, hg]

lemma step_multideg_eq_iff_eq (h : (p.step G).2 ≠ 0):
  (p.step G).2.multideg = p.multideg ↔ (p.step G).2 = p := by  
  have hp := ne_zero_of_step_quo_ne_zero p G h
  simp [step, hp, h]
  by_cases hg : ∃ g, g ∈ G ∧ leading_term g ∣ leading_term p
  ·    
    simp [hg, hp, step_apply] at h
    simp [hg]
    generalize_proofs _ hdvd
    have hp' : p.leading_term ≠ 0 := p.leading_term_eq_zero_iff.not.mpr hp
    rw [hdvd.choose_spec] at hp'
    simp at hp'
    simp [hp']    
    let g := List.head! (G.filter (leading_term · ∣ leading_term p))
    have : p.leading_term = leading_term (g * hdvd.choose) := by
      rw [leading_term_mul'_right, ←hdvd.choose_spec]
      rw [leading_term_leading_term]
    refine ne_of_lt ((multideg_sub_lt_left_iff ?_ h).mpr this)    
    apply le_of_eq
    nth_rewrite 1 [leading_term_def] at this -- Why rw not work?
    nth_rewrite 1 [leading_term_def] at this
    rw [monomial_eq_monomial_iff] at this
    simp [hp] at this
    exact this.1.symm
  ·
    simp [hg]

lemma step_multideg''_eq_iff :
  (p.step G).2.multideg'' = p.multideg'' ↔ (p.step G).2 = p := by
  by_cases hstep : (p.step G).2 = 0
  ·
    by_cases hp : p = 0
    · simp [multideg''_def, hp, hstep]
    · simp [multideg''_def, hp, hstep]
      rw [(⟨symm, symm⟩ : Iff (p=0) (0=p))] at hp
      exact hp
  ·
    simp [multideg''_def, hstep, ne_zero_of_step_quo_ne_zero p G hstep]
    exact step_multideg_eq_iff_eq p G hstep

lemma step_multideg_eq_iff (h : (p.step G).2 ≠ 0):
  (p.step G).2.multideg = p.multideg ↔
  ∀ g ∈ G, g ≠ 0 → ¬ LE.le (α:=σ→₀ℕ) g.multideg p.multideg :=
Trans.trans
  (step_multideg_eq_iff_eq p G h)
  (step_eq_iff p G (ne_zero_of_step_quo_ne_zero p G h))

theorem rem_support (p : MvPolynomial σ k) (G : List (MvPolynomial σ k))
  {g : MvPolynomial σ k} (h : g ∈ G) (h' : g ≠ 0):
  ∀ s ∈ (p.rem G).support, ¬ LE.le (α:=σ→₀ℕ) g.multideg s := by  
  intros s hs
  -- rw [rem_apply, mv_div_apply] at hs'
  by_cases hp : p = 0
  ·
    -- why simp [hp] at hs not work??
    rw [hp, rem_zero, support_zero] at hs
    exfalso
    exact Finset.not_mem_empty s hs  
  ·
    -- workaround
    rw [rem_apply, mv_div_apply] at hs    
    -- simp? only [hp] at hs
    -- simp? only [←rem_apply] at hs
    -- simp? at hs
    -- simp? [hp, ←rem_apply, -coeff_smul] at hs
    simp only [ne_eq, multideg_eq_zero_iff, not_exists, hp, rem_apply,
              dite_eq_ite, ite_false, mem_support_iff, coeff_add] at hs
    -- simp? only [coeff_smul] at hs
    set_option synthInstance.etaExperiment true in rw [coeff_smul] at hs
    -- simp? at hs
    rw [smul_eq_mul] at hs    
    have hnext := rem_support
      ((step p G).snd - (p.step G).2.coeff p.multideg • p.lm)
      G h h' s
    -- simp? at hnext
    simp only [ne_eq, mem_support_iff, not_imp_not] at hnext    
    by_contra tmp
    simp only [ne_eq, hp, hnext tmp , zero_add, mul_eq_zero] at hs
    push_neg at hs
    cases' hs with hs₁ hs₂    
    -- simp? [hp, lm, multideg'_eq_multideg hp] at hs₂
    simp only [lm, ne_eq, hp, not_false_eq_true, multideg'_eq_multideg hp,
                dite_eq_ite, ite_true, coeff_monomial, ite_eq_right_iff,
                one_ne_zero, not_forall, exists_prop, and_true] at hs₂
    have : (step p G).snd ≠ 0 := by
      by_contra h
      simp [h] at hs₁
    apply not_not.mpr tmp
    refine hs₂ ▸ (step_multideg_eq_iff p G this).mp ?_ g h h'
    exact eq_of_le_of_not_lt
          (step_multideg_le p G)
          (not_lt_of_le (le_multideg_of_coeff_ne_zero hs₁))
termination_by _ => multideg'' p
decreasing_by exact step_sub_multideg''_lt G hp


variable (G': Finset (MvPolynomial σ k))

def is_rem
  (r: MvPolynomial σ k)
:= (∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬LE.le (α:=σ→₀ℕ) g.multideg s) ∧
    ∃(q : G' →₀ MvPolynomial σ k), 
      (∀(g: MvPolynomial σ k) (hg : g ∈ G'),
        (g * q ⟨g, hg⟩).multideg ≤ p.multideg )∧
      p = q.sum (·*·) + r

theorem rem_is_rem : is_rem p G.toFinset (p.rem G) := by  
  constructor
  ·
    intro g hg
    exact rem_support p G (List.mem_toFinset.mp hg)
  ·
    use p.quo G
    constructor
    ·
      intros g hg
      exact multideg_quo_mul_le p G g (List.mem_toFinset.mp hg)
    ·
      exact (quo_quo_sum_add_rem p G).symm

lemma rem_is_rem' : is_rem p G' (p.rem G'.toList) := by
  have := rem_is_rem p G'.toList
  simp at this
  exact this

theorem exists_rem : ∃ r : MvPolynomial σ k, is_rem p G' r := by  
  use p.rem G'.toList
  simp only [rem_is_rem']

-- lemma step_rem (p: MvPolynomial σ k) (G: List (MvPolynomial σ k)):
--   ((p.rem G).step G).2 = p.rem G := by
--   rw [rem_apply, step_apply]
--   by_cases h: (p.mv_div G).snd = 0
--   ·
--     -- simp? [h]
--     simp only [h, zero_sub, ite_true]
--   ·
--     -- simp? [h]
--     simp only [h, ne_eq, ite_false]
--     by_cases h₂ : ∃ g, g ∈ G ∧ leading_term g ∣ leading_term (mv_div p G).snd
--     ·
--       -- simp? [h, h₂]
--       simp only [h₂, dite_true, sub_eq_self, mul_eq_zero, ne_eq]
--       generalize_proofs h h'
--       by_cases hh' : h'.choose = 0
--       ·
--         right
--         exact hh'
--       left
--       have test := h₂.choose_spec
--       have test1 := h'.choose_spec
--       -- conv => enter [1,1,1,1,x]; rw [test1]

--       sorry
--     ·
--       -- simp? [h, h₂]
--       simp only [h₂, dite_false]


-- #check le_trans
-- #check mul_add
-- #check coeff_ne_zero
-- #check rem_support
-- lemma testttt (h : p=0 ∧ q=0): False := by
--   Decidable.byContradiction
--   cases' h with h1 h2
--   ring
-- #check not_not
-- #check div_diviso

-- example [CommRing L] [CommRing (MvPolynomial σ L)] (p a b c: (MvPolynomial σ L)): p - a + (a - c - b) - (p - (b + c)) = 0 := by
--   ring

-- example [CommRing J] (p a b c: J): p - a + (a - c - b) - (p - (b + c)) = 0 := by
--   ring
-- set_option maxHeartbeats
-- lemma reg_dvd : ∀ g ∈ G, ∀ rs ∈ (reg p G).support, lt g ∣ monomial rs 1 := by
--   intros g hg rs hrs
--   -- unfold Reg at hrs
--   sorry
-- instance : NonAssocSemiring k := CommRing.toCommSemiring.toSemiring.toNonAssocSemiring
-- theorem reg_iff (r: MvPolynomial σ k): r = reg p G ↔ isReg p G r:= by
--   constructor
--   ·
--     intro hr
--     rw [hr]
--     unfold isReg
--     -- constructor
--     -- ·
--     --   unfold Reg
--     --   intros g hg rs hrs
--     --   -- unfold Reg'
--     --   simp at hrs
--     --   by_cases hp: p=0
--     --   ·

--     sorry
--   sorry


-- theorem reg_unique: ∃! (r: MvPolynomial σ k), isReg p G r := by
--   use reg p G
--   constructor
--   ·
--     simp only
--     rw [←reg_iff]
--   ·
--     simp only
--     intro r' hr'
--     exact (reg_iff p G r').mpr hr'

end MvDiv

end MvPolynomial