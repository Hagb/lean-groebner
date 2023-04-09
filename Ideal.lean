import Mathlib.Data.MvPolynomial.Basic
-- import Mathlib.Data.MvPolynomial.Division
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
-- import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Basic
-- import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Data.Finsupp.Order
-- import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch
-- import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.ProdSigma
import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Order.WellFounded
import TermOrder

-- import data.mv_polynomial.comm_ring
-- import data.mv_polynomial.comm_ring
-- import data.set.image
-- import data.set.image
-- import ring_theory.
-- import ring_theory.
-- import ring_theory.mv_polynomial.basic
-- import ring_theory.mv_polynomial.basic
-- import ring_theory.nullstellensatz
-- import ring_theory.nullstellensatz
-- import order.min_max
-- import order.min_max
open BigOperators

open Classical

namespace Ideal

theorem mem_span_iff {X : Type _} [_inst_1 : CommSemiring X] (A : Set X) (p : X) :
    p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : X → X), p = ∑ m in s, f m * m :=
  by
  let key := Finsupp.mem_span_iff_total X A p
  simp only [submodule_span_eq] at key
  simp only [key]
  constructor
  · simp only [forall_exists_index]
    intro f hp
    use f.support
    rw [← hp]
    use fun x => if h : x ∈ A then f ⟨x, h⟩ else 0
    unfold Finsupp.total
    simp only [Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul, Subtype.coe_prop,
  Subtype.coe_eta, dite_eq_ite, ite_true]
    unfold Finsupp.sum
    rfl
  · simp only [forall_exists_index]
    intro sset f hp
    rw [hp]
    let f' : A → X := fun x => if x ∈ sset then f x else 0
    let sset' := Finset.filter (f' · ≠ 0) sset
    have hf' : ∀ x : A, f' x ≠ 0 → x ∈ sset' :=
      by
      intro x hx
      -- simp?
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, Subtype.forall, Finset.mem_filter, and_self_left]
      -- simp? at hx
      simp only [Ne.def, ite_eq_right_iff, not_forall, exists_prop] at hx
      exact hx
    use Finsupp.onFinset sset' f' hf'
    rw [Finsupp.total_onFinset X _ _]
    rw [(_ : (∑ m : ↥A in sset, f m * m) = ∑ m in sset', f' m * m)]
    rfl
    let diff := sset \ sset'
    have split_sset : sset = diff ∪ sset' :=
      by
      -- simp?
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, Subtype.forall, Finset.sdiff_union_self_eq_union,
  Finset.left_eq_union_iff_subset, Finset.filter_subset]
    rw [split_sset, Finset.sum_union Finset.sdiff_disjoint]
    have sum_diff_eq_zero : (∑ x : ↥A in diff, f ↑x * ↑x) = 0 :=
      by
      rw [Finset.sum_eq_zero]
      intro x hx
      -- squeeze_dsimp [diff, sset'] at hx,
      -- dsimp only [diff, sset'] at hx
      -- squeeze_simp at hx,
      -- simp? at hx
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, Subtype.forall, Finset.mem_sdiff,
  Finset.mem_filter, and_self_left, not_and, not_not] at hx
      simp only [hx.2 hx.1, MulZeroClass.zero_mul]
    rw [sum_diff_eq_zero, zero_add, Finset.sum_congr]
    · rfl
    intro x hx
    have hx' : x ∈ sset := by
      exact Finset.mem_of_mem_filter x hx
    simp only [hx', if_true]
#align ideal.mem_span_iff Ideal.mem_span_iff

theorem mem_span_iff' {X : Type _} [_inst_1 : CommSemiring X] (A : Set X) (p : X) :
    p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : A → X), p = ∑ m in s, f m * m :=
  by
  rw [mem_span_iff]
  constructor
  · rintro ⟨s, f, hp⟩
    rw [hp]
    use s
    use f ∘ ((↑): A→X)
    rfl
  · rintro ⟨s, f, hp⟩
    rw [hp]
    use s
    use fun x => if h : x ∈ A then f ⟨x, h⟩ else 0
    simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, if_true]
#align ideal.mem_span_iff' Ideal.mem_span_iff'

end Ideal

open Ideal

-- open set
namespace MvPolynomial

variable {k : Type _} [Field k]

variable {σ : Type _} {r : σ → σ → Prop}

variable {s : σ →₀ ℕ}

variable (p : MvPolynomial σ k)

variable (p_nonzero : p ≠ 0)

variable (I : Ideal (MvPolynomial σ k))

def IsMonomial : Prop :=
  ∃ (s : σ →₀ ℕ)(c : k), p = monomial s c
#align mv_polynomial.is_monomial MvPolynomial.IsMonomial

def fullMonomialSet : Set (MvPolynomial σ k) :=
  { mono | IsMonomial mono }
#align mv_polynomial.full_monomial_set MvPolynomial.fullMonomialSet

def IsMonomialSet (theset : Set (MvPolynomial σ k)) : Prop :=
  theset ⊆ fullMonomialSet
#align mv_polynomial.is_monomial_set MvPolynomial.IsMonomialSet

variable (A : Set (MvPolynomial σ k)) (A_is_monomial_set : IsMonomialSet A)

theorem monomial_set_iff {A : Set (MvPolynomial σ k)} : IsMonomialSet A ↔ ∀ p ∈ A, IsMonomial p :=
  by
  unfold IsMonomialSet fullMonomialSet
  rfl
#align mv_polynomial.monomial_set_iff MvPolynomial.monomial_set_iff

variable (mono : MvPolynomial σ k) (mono_is_mono : IsMonomial mono)

-- include A A_is_monomial_set

-- include mono mono_is_mono

-- TODO: when k is commring
theorem mono_in_mono_ideal_iff (hA : A.Nonempty) : mono ∈ Ideal.span A ↔ ∃ p₁ ∈ A, p₁ ∣ mono :=
  by
  constructor
  · intro hmA
    by_cases mono_zero : mono = 0
    · cases' hA with a ha
      exact ⟨a, ha, mono_zero.symm ▸ dvd_zero a⟩
    rcases mono_is_mono with ⟨mono_k, mono_c, mono_is_mono⟩
    rw [mem_span_iff A mono] at hmA
    rcases hmA with ⟨s, f, hmono⟩
    have key :=
      coeff_sum (s.image ((↑): ↥A →MvPolynomial σ k)) (fun m : MvPolynomial σ k => f m * m)
        mono_k
    -- squeeze_simp at key,
    simp only [Finset.sum_image, SetCoe.forall, Subtype.coe_mk, Subtype.mk_eq_mk, imp_self,
      imp_true_iff] at key
    rw [← hmono, mono_is_mono] at key
    simp only [coeff_monomial, eq_self_iff_true, if_true] at key
    have mono_c_nz : mono_c ≠ 0 := by
      by_contra h
      rw [mono_is_mono, h, monomial_zero] at mono_zero
      exact mono_zero rfl
    have key' : ∃ x : ↥A, coeff mono_k (f x * (x: MvPolynomial σ k)) ≠ 0 := by
      by_contra h
      push_neg at h
      simp only [h, Finset.sum_const_zero] at key
      exact mono_c_nz key
    simp only [Ne.def, SetCoe.exists, Subtype.coe_mk, exists_prop] at key'
    rcases key' with ⟨p, hpA, hpc⟩
    use p, hpA
    have p_is_mono := (monomial_set_iff.mp A_is_monomial_set) p hpA
    rcases p_is_mono with ⟨p_k, p_c, hp⟩
    rw [hp, coeff_mul_monomial'] at hpc
    simp only [add_zero, ite_eq_right_iff, mul_eq_zero, not_forall, exists_prop] at hpc
    use monomial (mono_k - p_k) (mono_c / p_c)
    rw [hp, mono_is_mono, monomial_mul]
    apply (monomial_eq_monomial_iff mono_k (p_k + (mono_k - p_k)) mono_c (p_c * (mono_c / p_c))).mpr
    left
    constructor
    ·-- squeeze_simp [hpc]
      simp only [hpc, add_tsub_cancel_of_le]
    push_neg  at hpc
    rw [(by ring : p_c * (mono_c / p_c) = mono_c * (p_c / p_c))]
    rw [(div_self hpc.2.2 : p_c / p_c = 1)]
    ring
  · rintro ⟨p₁, hp₁, hp₁p⟩
    -- unfold has_dvd.dvd at hp₁p,
    cases' hp₁p with c hp₁p
    rw [mul_comm] at hp₁p
    rw [hp₁p]
    exact mul_mem_left (span A) _ (subset_span hp₁)
#align mv_polynomial.mono_in_mono_ideal_iff MvPolynomial.mono_in_mono_ideal_iff

-- omit mono mono_is_mono

-- TODO: when k is commring
/-
invalid declaration, identifier expected
-/
theorem mem_mono_ideal_iff_term_mem :
    p ∈ span A ↔ ∀ v ∈ p.support, monomial v (coeff v p) ∈ span A :=
  by
  constructor
  · intro hp v hv
    rw [mem_span_iff] at hp
    rcases hp with ⟨s, f, hp⟩
    let key :=
      coeff_sum (s.image ((↑): A → MvPolynomial σ k)) (fun m : MvPolynomial σ k => f m * m) v
    -- squeeze_simp at key,
    simp only [Finset.sum_image, SetCoe.forall, Subtype.coe_mk, Subtype.mk_eq_mk, imp_self,
      imp_true_iff] at key
    rw [← hp] at key
    have key' : ∃ x : ↥A, coeff v (f x * (x: MvPolynomial σ k)) ≠ 0 :=
      by
      rcases Finset.exists_ne_zero_of_sum_ne_zero
          (key ▸ mem_support_iff.mp hv : (∑ x : ↥A in s, coeff v (f ↑x * ↑x)) ≠ 0) with
        ⟨x, _, h⟩
      use x
      exact h
    simp only [Ne.def, SetCoe.exists, Subtype.coe_mk, exists_prop] at key'
    rcases key' with ⟨m, hmA, hmc⟩
    have m_is_mono := (monomial_set_iff.mp A_is_monomial_set) m hmA
    rcases m_is_mono with ⟨mk, mc, hm⟩
    nth_rw 2 [hm] at hmc
    -- squeeze_simp [coeff_mul_monomial'] at hmc,
    simp only [coeff_mul_monomial', ite_eq_right_iff, mul_eq_zero, not_forall, exists_prop] at hmc
    push_neg  at hmc
    have key' : (monomial (v - mk)) (coeff v p / mc) * (monomial mk) mc ∈ span A :=
      by
      rw [hm] at hmA
      apply Submodule.smul_mem (span A)
      apply subset_span hmA
    rw [monomial_mul] at key'
    -- squeeze_simp [hmc.1, add_comm] at key',
    simp only [hmc, add_comm, add_tsub_cancel_of_le, div_mul_cancel, Ne.def, not_false_iff] at key'
    exact key'
  · intro hv
    rw [← support_sum_monomial_coeff p]
    apply Ideal.sum_mem (span A)
    exact hv
#align mv_polynomial.mem_mono_ideal_iff_term_mem MvPolynomial.mem_mono_ideal_iff_term_mem

-- omit A A_is_monomial_set

-- theorem support_zero_iff : p = 0 ↔ p.support = ∅ :=
--   by
--   constructor
--   · intro hp
--     rw [hp]
--     exact support_zero
--   · intro hps
--     rw [as_sum p, hps]
--     exact rfl
-- #align mv_polynomial.support_zero_iff MvPolynomial.support_zero_iff

end MvPolynomial
