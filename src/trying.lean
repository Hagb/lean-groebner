import data.mv_polynomial.basic
-- import data.mv_polynomial.comm_ring
-- import data.set.image
-- import ring_theory.
-- import ring_theory.mv_polynomial.basic
-- import ring_theory.nullstellensatz
-- import order.min_max
import algebra.big_operators.basic
import algebra.big_operators.ring
import algebra.module.submodule.basic
import ring_theory.ideal.basic
import linear_algebra.finsupp
import linear_algebra.span
import data.finset.basic
import data.finset.sum

open_locale big_operators
open_locale classical

namespace ideal
lemma mem_span_iff {X: Type _} [_inst_1 : comm_semiring X] (A: set X) (p: X): p ∈ ideal.span A ↔
       ∃ (s : finset A) (f : X → X), p = (∑ m in s, (f m) * m) :=
begin
  let key := finsupp.mem_span_iff_total X A p,
  simp only [submodule_span_eq] at key,
  simp only [key],
  split,
  {
    simp only [forall_exists_index],
    intros f hp,
    use f.support,
    rw ← hp,
    use λ x, if h : x ∈ A then (f ⟨x, h⟩) else 0,
    simpa only [subtype.coe_prop, subtype.coe_eta],
  },
  {
    simp only [forall_exists_index],
    intros sset f hp,
    rw hp,
    let f' : A → X := λ x, if x ∈ sset then f x else 0,
    let sset' := {x ∈ sset | f' x ≠ 0},
    have hf': ∀ (x: A), f' x ≠ 0 → x ∈ sset', {
      intros x hx,
      dsimp only [sset'],
      simp only [ne.def, ite_eq_right_iff, not_forall, exists_prop, finset.sep_def, finset.mem_filter, and_self_left],
      dsimp only [f'] at hx,
      -- squeeze_simp at hx,
      simp only [ne.def, ite_eq_right_iff, not_forall, exists_prop] at hx,
      exact hx,
    },
    use finsupp.on_finset sset' f' hf',
    rw finsupp.total_on_finset X (@coe A X _) _,
    rw (_: ∑ (m : ↥A) in sset, f m * m = ∑ m in sset', f' m * m),
    refl,

    let diff := sset \ sset',
    have split_sset: sset = diff ∪ sset', {
      dsimp only [sset', diff],
      simp only [finset.sep_def, finset.sdiff_union_self_eq_union, finset.left_eq_union_iff_subset, finset.filter_subset],
    },
    rw [split_sset, finset.sum_union finset.sdiff_disjoint],
    have sum_diff_eq_zero: ∑ (x : ↥A) in diff, f ↑x * ↑x = 0, {
      rw finset.sum_eq_zero,
      intros x hx,
      -- squeeze_dsimp [diff, sset'] at hx,
      dsimp only [diff, sset'] at hx,
      -- squeeze_simp at hx,
      simp only [ne.def, ite_eq_right_iff, not_forall, exists_prop, finset.sep_def, finset.mem_sdiff, finset.mem_filter, and_self_left,
  not_and, not_not] at hx,
      simp only [hx.2 hx.1, zero_mul],
    },
    rw [sum_diff_eq_zero, zero_add, finset.sum_congr], { refl, },
    intros x hx,
    have hx': x ∈ sset,
    {
      dsimp only [sset'] at hx,
      apply finset.filter_subset,
      exact hx,
    },
    dsimp only [f'],
    simp only [hx', if_true],
  },
end

lemma mem_span_iff' {X: Type _} [_inst_1 : comm_semiring X] (A: set X) (p: X): p ∈ ideal.span A ↔
       ∃ (s : finset A) (f : A → X), p = (∑ m in s, (f m) * m) :=
begin
  rw mem_span_iff,
  split,
  {
    rintros ⟨s, f, hp⟩,
    rw hp,
    use s,
    use f ∘ coe,
  },
  {
    rintros ⟨s, f, hp⟩,
    rw hp,
    use s,
    use λ x, if h: x ∈ A then f ⟨x, h⟩ else 0,
    simp only [subtype.coe_prop, subtype.coe_eta, dite_eq_ite, if_true],
  },
end
end ideal

open ideal
-- open set
namespace mv_polynomial

variables {k : Type*} [field k]

variables {σ : Type*} {r: σ → σ → Prop}
variables {s: (σ →₀ ℕ)}

variables (p: mv_polynomial σ k)

variables (p_nonzero: p ≠ 0)
variables (I: ideal (mv_polynomial σ k))

def is_monomial: Prop := ∃ (s: σ→₀ℕ) (c: k), p = monomial s c

def full_monomial_set : set (mv_polynomial σ k) :=
{mono | is_monomial mono}

def is_monomial_set (theset: set (mv_polynomial σ k)): Prop :=
theset ⊆ full_monomial_set

variables (A: set (mv_polynomial σ k)) (A_is_monomial_set: is_monomial_set A)

lemma is_monomial_set_iff {A: set (mv_polynomial σ k)}: is_monomial_set A ↔ ∀ p ∈ A, is_monomial p :=
begin
unfold is_monomial_set has_subset.subset has_le.le,
unfold full_monomial_set,
simp,
end


variables (mono: mv_polynomial σ k) (mono_is_mono: is_monomial mono)



include A A_is_monomial_set
include mono mono_is_mono
-- TODO: when k is commring
lemma mono_in_mono_ideal_iff (hA: A.nonempty): mono ∈ ideal.span A ↔ ∃ (p₁ ∈ A), p₁ ∣ mono :=
begin
  split,
  {
    intro hmA,
    by_cases mono_zero: mono = 0,
    {
      cases hA with a ha,
      exact ⟨a, ha, mono_zero.symm ▸ dvd_zero a⟩,
    },
    rcases mono_is_mono with ⟨mono_k,mono_c,mono_is_mono⟩,
    rw (mem_span_iff A mono) at hmA,
    rcases hmA with ⟨s,f,hmono⟩,
    have key := coeff_sum (s.image (@coe (↥A) (mv_polynomial σ k) _)) (λ (m: (mv_polynomial σ k)), f m * m) mono_k,
    -- squeeze_simp at key,
    simp only [finset.sum_image, set_coe.forall, subtype.coe_mk, subtype.mk_eq_mk, imp_self, implies_true_iff] at key,
    rw [← hmono, mono_is_mono] at key,
    simp only [coeff_monomial, eq_self_iff_true, if_true] at key,
    
    have mono_c_nz: mono_c ≠ 0,
    {
      by_contradiction,
      rw [mono_is_mono, h, monomial_zero] at mono_zero,
      exact mono_zero rfl,
    },

    have key': ∃ (x: ↥A), coeff mono_k (f ↑x * ↑x) ≠ 0,
    {
      by_contradiction,
      push_neg at h,
      simp only [h, finset.sum_const_zero] at key,
      exact mono_c_nz key,
    },
    simp only [ne.def, set_coe.exists, subtype.coe_mk, exists_prop] at key',
    rcases key' with ⟨p, hpA, hpc⟩,
    use [p, hpA],
    have p_is_mono := (is_monomial_set_iff.mp A_is_monomial_set) p hpA,
    simp only [is_monomial] at p_is_mono,
    rcases p_is_mono with ⟨p_k,p_c,hp⟩,
    rw [hp, coeff_mul_monomial'] at hpc,
    simp only [add_zero, ite_eq_right_iff, mul_eq_zero, not_forall, exists_prop] at hpc,
    use monomial (mono_k - p_k) (mono_c / p_c),
    rw [hp,mono_is_mono,monomial_mul],
    apply (monomial_eq_monomial_iff mono_k (p_k + (mono_k - p_k)) mono_c (p_c * (mono_c / p_c))).mpr,
    left,
    split, {
      -- squeeze_simp [hpc]
      simp only [hpc, add_tsub_cancel_of_le],
    },
    push_neg at hpc,
    rw (by ring: p_c * (mono_c / p_c) = mono_c * (p_c / p_c)),
    rw (div_self hpc.2.2: p_c/p_c=1),
    ring,
  },
  {
    rintros ⟨p₁, hp₁, hp₁p⟩,
    -- unfold has_dvd.dvd at hp₁p,
    cases hp₁p with c hp₁p,
    rw mul_comm at hp₁p,
    rw hp₁p,
    exact mul_mem_left (span A) _ (subset_span hp₁),
  },
end
omit mono mono_is_mono

-- TODO: when k is commring
/-
invalid declaration, identifier expected
-/

lemma mem_mono_ideal_iff_term_mem: p ∈ span A ↔ ∀ v ∈ p.support, monomial v (coeff v p) ∈ span A :=
begin
  split,
  {
    intros hp v hv,
    rw mem_span_iff at hp,
    rcases hp with ⟨s, f, hp⟩,
    let key := coeff_sum (s.image (@coe (↥A) (mv_polynomial σ k) _)) (λ (m: (mv_polynomial σ k)), f m * m) v,
    -- squeeze_simp at key,
    simp only [finset.sum_image, set_coe.forall, subtype.coe_mk, subtype.mk_eq_mk, imp_self, implies_true_iff] at key,
    rw ←hp at key,

    have key': ∃ (x: ↥A), coeff v (f ↑x * ↑x) ≠ 0,
    {
      rcases finset.exists_ne_zero_of_sum_ne_zero
              (key ▸ mem_support_iff.mp hv: ∑ (x : ↥A) in s, coeff v (f ↑x * ↑x) ≠ 0)
            with ⟨x, hx, h⟩,
      use x,
    },
    simp only [ne.def, set_coe.exists, subtype.coe_mk, exists_prop] at key',
    rcases key' with ⟨m, hmA, hmc⟩,
    have m_is_mono := (is_monomial_set_iff.mp A_is_monomial_set) m hmA,
    rcases m_is_mono with ⟨mk,mc,hm⟩,
    nth_rewrite 1 hm at hmc,
    -- squeeze_simp [coeff_mul_monomial'] at hmc,
    simp only [coeff_mul_monomial', ite_eq_right_iff, mul_eq_zero, not_forall, exists_prop] at hmc,
    push_neg at hmc,
    have key': ((monomial (v-mk)) ((coeff v p)/mc)) * (monomial mk) mc ∈ span A, {
      rw hm at hmA,
      apply submodule.smul_mem (span A),
      apply subset_span hmA,
    },
    rw monomial_mul at key',
    -- squeeze_simp [hmc.1, add_comm] at key',
    simp only [hmc, add_comm, add_tsub_cancel_of_le, div_mul_cancel, ne.def, not_false_iff] at key',
    exact key',
  },
  {
    intros hv,
    rw ← support_sum_monomial_coeff p,
    apply ideal.sum_mem (span A),
    exact hv,
  },
end
omit  A A_is_monomial_set

lemma support_zero_iff: p=0 ↔ p.support = ∅ := begin
  split,
  {
    intros hp,
    rw hp,
    exact support_zero,
  },
  {
    intros hps,
    rw [as_sum p, hps],
    exact rfl,
  },
end

variables [finite σ]
variables [has_add (σ →₀ ℕ)] [has_zero (σ →₀ ℕ)] 
class term_order (σ : Type _) [finite σ] extends linear_order (σ →₀ ℕ) :=
  (additive : ∀ v v₁ v₂ : (σ →₀ ℕ), v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le : ∀ v : (σ →₀ ℕ), 0 ≤ v)

variables [linear_order (σ→₀ℕ)]

def multideg: σ→₀ℕ :=
p.support.max' (finset.nonempty_of_ne_empty ((support_zero_iff p).not.mp p_nonzero))

def lc: k := coeff (multideg p p_nonzero) p

noncomputable def lm: mv_polynomial σ k := monomial (multideg p p_nonzero) (1: k)

noncomputable def lt: mv_polynomial σ k := monomial (multideg p p_nonzero) (lc p p_nonzero)

noncomputable def lt_of_ideal: ideal (mv_polynomial σ k) :=
ideal.span {ltp | ∃ (p ∈ I) (p_non0: p ≠ 0), ltp = lm p p_non0}

lemma multideg_in_support: multideg p p_nonzero ∈ p.support :=
(support p).max'_mem (multideg._proof_1 p p_nonzero)

end mv_polynomial