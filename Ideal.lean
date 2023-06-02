import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Substs
import Mathlib.RingTheory.Polynomial.Basic
import Division

open BigOperators

open Classical
open Tactic

namespace Ideal

variable {R : Type _} [Semiring R]

-- mem_span_iff, mem_span_iff', mem_span_iff'' have much shorter proofs in
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/submodule.2Espan.20as_sum

theorem mem_span_iff (A : Set R) (p : R) :
    p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : R → R), p = ∑ m in s, f m * m := by
  let key := Finsupp.mem_span_iff_total R A p
  simp only [submodule_span_eq] at key
  simp only [key]
  constructor
  · simp only [forall_exists_index]
    intro f hp
    use f.support
    rw [← hp]
    use fun x => if h : x ∈ A then f ⟨x, h⟩ else 0
    unfold Finsupp.total
    simp only [Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul,
                Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true]
    unfold Finsupp.sum
    rfl
  · simp only [forall_exists_index]
    intro sset f hp
    rw [hp]
    let f' : A → R := fun x => if x ∈ sset then f x else 0
    let sset' := Finset.filter (f' · ≠ 0) sset
    have hf' : ∀ x : A, f' x ≠ 0 → x ∈ sset' :=
      by
      intro x hx
      -- simp?
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, Subtype.forall,
                 Finset.mem_filter, and_self_left]
      -- simp? at hx
      simp only [Ne.def, ite_eq_right_iff, not_forall, exists_prop] at hx
      exact hx
    use Finsupp.onFinset sset' f' hf'
    rw [Finsupp.total_onFinset R _ _]
    rw [(_ : (∑ m : ↥A in sset, f m * m) = ∑ m in sset', f' m * m)]
    rfl
    let diff := sset \ sset'
    have split_sset : sset = diff ∪ sset' :=
      by
      -- simp?
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, Subtype.forall,
                  Finset.sdiff_union_self_eq_union,
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

theorem mem_span_iff' (A : Set R) (p : R) :
    p ∈ Ideal.span A ↔ ∃ (s : Finset A)(f : A → R), p = ∑ m in s, f m * m :=
  by
  rw [mem_span_iff]
  constructor
  · rintro ⟨s, f, hp⟩
    rw [hp]
    use s
    use f ∘ ((↑): A→R)
    rfl
  · rintro ⟨s, f, hp⟩
    rw [hp]
    use s
    use fun x => if h : x ∈ A then f ⟨x, h⟩ else 0
    simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, if_true]
#align ideal.mem_span_iff' Ideal.mem_span_iff'

theorem mem_span_iff'' (A : Set R) (p : R) :
  p ∈ Ideal.span A ↔ ∃ (s : Finset R) (f : R → R), s.toSet ⊆ A ∧ p = ∑ m in s, f m * m := by
  rw [mem_span_iff]
  constructor
  ·
    rintro ⟨s, f, h⟩
    use s.image (fun (x : A) => (↑x : R))
    use f
    simp [h]
  ·
    rintro ⟨s, f, hs, h⟩
    by_cases hA : A = ∅
    ·
      simp [hA, Set.subset_empty_iff] at hs
      simp [hs] at h
      use ∅
      use f
      simp [h]
    cases' Set.nonempty_iff_ne_empty.mpr hA with a ha
    have : ∀ (x : R), x ∈ s → x ∈ A := by
      intro x hx
      apply Set.mem_of_subset_of_mem hs
      simp [hx]
    use s.image (fun (x : R) => if hx : x ∈ s then ⟨x, this x hx⟩ else ⟨a, ha⟩)
    use f
    rw [h]
    rw [Finset.sum_image']
    intro c hc
    simp [hc]
    have :
      s.filter (fun (x : R) =>
          ((if hx : x ∈ s then ⟨x, this x hx⟩ else ⟨a, ha⟩) = (⟨c, this c hc⟩ : A)))
      = {c} := by
      ext c'
      simp
      constructor
      · rintro ⟨hc', h⟩
        simp [hc'] at h
        exact h
      · intro hc'
        rw [hc']
        simp [hc]
    rw [this]
    simp

theorem fg_span_iff_fg_span_finset_subset (s : Set R) :
  (span s).FG ↔ ∃ (s' : Finset R), s'.toSet ⊆ s ∧ span s = span s' := by
  constructor
  ·
    intro hfg
    let ⟨s₁, hs₁⟩ := hfg
    have := subset_span (α:=R) (s:=s₁)
    rw [hs₁] at this
    let s' := s₁.biUnion
      (fun x =>
        if h : x ∈ s₁
          then ((mem_span_iff s x).mp (Set.mem_of_subset_of_mem this h)).choose.image (fun (x : s) => (↑x : R))
          else ∅)
    use s'
    constructor
    ·
      simp
      intro i hi
      simp [hi]
    ·
      rw [←SetLike.coe_set_eq]
      apply Set.eq_of_subset_of_subset
      ·
        intro a ha
        rw [←hs₁] at ha
        simp [mem_span_iff''] at ha
        rcases ha with ⟨s'', hs'', f , ha⟩
        rw [ha]
        apply Ideal.sum_mem
        intro b hb
        apply mul_mem_left
        have hb := Set.mem_of_subset_of_mem hs'' (Finset.mem_coe.mpr hb)
        change b ∈ s₁ at hb
        have key :
          b ∈ span (
            (fun x => if h : x ∈ s₁
            then ((mem_span_iff s x).mp (Set.mem_of_subset_of_mem this h)).choose.image (fun (x : s) => (↑x : R))
            else (∅ : Finset R)) b)
          := by
          -- simp only [hb, dite_true]
          simp [hb]
          generalize_proofs h₁
          have := h₁.choose_spec
          rcases this with ⟨f',hb'⟩
          nth_rewrite 1 [hb']
          apply sum_mem
          intro c hc
          apply mul_mem_left
          apply Set.mem_of_subset_of_mem subset_span
          simp [hc]
        refine Set.mem_of_subset_of_mem ?_ key
        apply span_mono
        rw [Finset.coe_subset]
        apply Finset.subset_biUnion_of_mem (x:=b) _
        exact hb
      ·
        apply span_mono
        simp
        intro i hi
        simp [hi]
  ·
    rintro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

@[simp]
lemma span_singleton_zero:
  span ({0} : Set R) = ⊥ := by simp only [span_singleton_eq_bot]

@[simp]
lemma span_sdiff_singleton_zero_eq (s : Set R):
  span (s \ {0}) = span s := by
  by_cases h : 0 ∈ s
  · nth_rewrite 2 [(by simp [h] : s = s \ {0} ∪ {0})]
    rw [span_union]
    simp
  ·simp [h]


theorem sum_mul_left_mem_of_subset {G' : Finset R}
  {I : Ideal R}
  (hG' : G'.toSet ⊆ I)
  (f : R → R):
  G'.sum (fun x => (f x) * x) ∈ I := by
  apply Ideal.sum_mem
  intro c hc
  simp [hc]
  apply Ideal.mul_mem_left
  apply Set.mem_of_subset_of_mem hG'
  simp [hc]

theorem sum_mul_right_mem_of_subset {R : Type _} [CommSemiring R] {G' : Finset R}
  {I : Ideal R}
  (hG' : G'.toSet ⊆ I)
  (f : R → R):
  G'.sum (fun x => x * (f x)) ∈ I := by
  conv => enter [1,2,x]; rw [mul_comm]
  exact sum_mul_left_mem_of_subset hG' f

theorem sum_mul_mem_of_subset' {R : Type _} [CommSemiring R] {G' : Set R}
  {I : Ideal R}
  (hG' : G' ⊆ I)
  (q : G' →₀ R):
  q.sum (·*·) ∈ I := by
  apply Ideal.sum_mem
  intro c hc
  simp [hc]
  apply Ideal.mul_mem_right
  apply Set.mem_of_subset_of_mem hG'
  simp [hc]

end Ideal

open Ideal

namespace MvPolynomial

set_option synthInstance.maxHeartbeats 40000

-- These section is abandoned,
-- becasuse the equivalent things have committed to Mathlib
section Abandoned

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

theorem monomial_set_iff {A : Set (MvPolynomial σ k)} : IsMonomialSet A ↔ ∀ p ∈ A, IsMonomial p
:= by
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

end Abandoned
section Ideal

variable {σ : Type _} {k : Type _} [Field k]
variable [term_order_class: TermOrderClass (TermOrder (σ→₀ℕ))]

variable (p : MvPolynomial σ k)
variable (G': Finset (MvPolynomial σ k)) (G'': Set (MvPolynomial σ k))
variable (I I₁ I₂ : Ideal (MvPolynomial σ k))

variable {R : Type _} [CommSemiring R]

@[reducible]
def leading_term_ideal : Ideal (MvPolynomial σ k) := span (leading_term '' G'')


lemma leading_term_ideal_def : leading_term_ideal G'' = span (lm '' G''):= by
  ext q
  rw [leading_term_ideal]
  constructor
  ·
    intro hq
    rw [mem_span_iff''] at hq
    rcases hq with ⟨s, f, hs, hq⟩
    rw [hq]
    apply Ideal.sum_mem
    intro m hm
    apply Ideal.mul_mem_left
    have hm := Set.mem_of_subset_of_mem hs hm
    rw [Set.mem_image] at hm
    rcases hm with ⟨p, hp, hm⟩
    rw [←hm, leading_term_def', smul_eq_C_mul]
    apply Ideal.mul_mem_left --(span (lm '' G'')) _ (b:=lm p)
    apply Set.mem_of_subset_of_mem subset_span
    rw [Set.mem_image]
    exact ⟨p, hp , rfl⟩
  ·
    intro hq
    rw [mem_span_iff''] at hq
    rcases hq with ⟨s, f, hs, hq⟩
    rw [hq]
    apply Ideal.sum_mem
    intro m hm
    apply Ideal.mul_mem_left
    by_cases h : m = 0
    ·simp [h]
    have hm := Set.mem_of_subset_of_mem hs hm
    rw [Set.mem_image] at hm
    rcases hm with ⟨p, hp, hm⟩
    rw [←hm] at h
    have : p.lm = C p.leading_coeff⁻¹ * p.leading_term := by
      rw [leading_term_def', smul_eq_C_mul, ←mul_assoc, ←C_mul]
      have := p.leading_coeff_eq_zero_iff.not.mpr (p.lm_eq_zero_iff.not.mp h)
      rw [inv_mul_cancel this, C_1, one_mul]
    rw [←hm, this]
    apply Ideal.mul_mem_left
    apply Set.mem_of_subset_of_mem subset_span
    rw [Set.mem_image]
    exact ⟨p, hp , rfl⟩

lemma leading_term_ideal_span_monomial :
  leading_term_ideal G'' =
  span ((monomial · (1 : k)) '' ((G'' \ {0}).image (β:=σ→₀ℕ) multideg)) := by
  rw [leading_term_ideal_def, ←span_sdiff_singleton_zero_eq (lm '' G'')]
  congr
  have : lm '' G'' \ {0} = lm '' (G'' \ {0}) := by
    have : {0} = lm⁻¹' ({0} : Set (MvPolynomial σ k)) := by
      ext x
      simp [lm_eq_zero_iff]
    nth_rewrite 2 [this]
    exact Set.image_diff_preimage.symm
  rw [this, Set.image_image]
  apply Set.image_congr
  simp
  intro a _ ha
  exact lm_def_of_ne_zero ha

lemma rem_mem_ideal_iff {p : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} {I : Ideal (MvPolynomial σ k)}
  {r : MvPolynomial σ k}
  (h : G'.toSet ⊆ I) (hG' : is_rem p G' r):
  r ∈ I ↔ p ∈ I := by
  constructor
  · intro hr
    rw [hG'.2.choose_spec.2]
    exact add_mem (sum_mul_mem_of_subset' h _) hr
  ·
    intro hp
    rw [←sub_eq_of_eq_add' (hG'.2.choose_spec.2)]
    apply Ideal.sub_mem I hp
    exact sum_mul_mem_of_subset' h hG'.2.choose

lemma rem_sub_rem_mem_ideal {G' : Finset (MvPolynomial σ k)}
  {I : Ideal (MvPolynomial σ k)} (hG' : G'.toSet ⊆ I)
  {p r₁ r₂ : MvPolynomial σ k}
  (hr₁ : is_rem p G' r₁) (hr₂ : is_rem p G' r₂) : r₁-r₂ ∈ I := by
  have h₁ := eq_sub_of_add_eq' hr₁.2.choose_spec.2.symm
  have h₂ := eq_sub_of_add_eq' hr₂.2.choose_spec.2.symm
  rw [h₁, h₂]
  simp
  rw [←Finsupp.sum_sub_index _]
  ·exact sum_mul_mem_of_subset' hG' _
  · simp
    intro a _ b₁ b₂
    ring

lemma monomial_not_mem_leading_term_ideal {r : MvPolynomial σ k}
  {G' : Set (MvPolynomial σ k)}
  (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬LE.le (α:=σ→₀ℕ) g.multideg s)
: ∀ s ∈ r.support, monomial s 1 ∉ leading_term_ideal G' := by
  intro s hs
  rw [leading_term_ideal_span_monomial, mem_ideal_span_monomial_image]
  simp
  intro g hg hg'
  exact h g hg hg' s hs

lemma term_not_mem_leading_term_ideal {r : MvPolynomial σ k}
  {G' : Set (MvPolynomial σ k)}
  (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬LE.le (α:=σ→₀ℕ) g.multideg s)
: ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal G' := by
  intro s hs
  have := monomial_not_mem_leading_term_ideal h s hs
  by_contra h'
  apply this
  rw [(by simp [mem_support_iff.mp hs] : 1 =  (r.coeff s)⁻¹*(r.coeff s))]
  rw [←C_mul_monomial]
  exact mul_mem_left _ _ h'

lemma not_mem_leading_term_ideal {r : MvPolynomial σ k}
  {G' : Set (MvPolynomial σ k)}
  (h : ∀ g ∈ G', g ≠ 0 → ∀ s ∈ r.support, ¬LE.le (α:=σ→₀ℕ) g.multideg s)
  (hr : r ≠ 0) :
r ∉ leading_term_ideal G' := by
  rw [leading_term_ideal_span_monomial, mem_ideal_span_monomial_image]
  simp
  use multideg r
  constructor
  · rw [←leading_coeff_def, leading_coeff_eq_zero_iff]
    exact hr
  ·
    intro g hg hg'
    exact h g hg hg' r.multideg (r.multideg_mem_support_iff_p_ne_zero.mpr hr)

lemma rem_monomial_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r):
  ∀ s ∈ r.support, monomial s 1 ∉ leading_term_ideal G'.toSet := by
  exact monomial_not_mem_leading_term_ideal h.1

lemma rem_term_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r):
  ∀ s ∈ r.support, monomial s (r.coeff s) ∉ leading_term_ideal G' := by
  exact term_not_mem_leading_term_ideal h.1

lemma rem_not_mem_leading_term_ideal {p r : MvPolynomial σ k}
  {G' : Finset (MvPolynomial σ k)} (h : is_rem p G' r) (hr :r ≠ 0):
  r ∉ leading_term_ideal G' := by
  exact not_mem_leading_term_ideal h.1 hr

lemma rem_sub_rem_term_not_mem_leading_term_ideal
  {G' : Finset (MvPolynomial σ k)} {p r₁ r₂ : MvPolynomial σ k}
  (hr₁ : is_rem p G' r₁) (hr₂ : is_rem p G' r₂) :
  ∀ s ∈ (r₁-r₂).support, monomial s ((r₁-r₂).coeff s) ∉ leading_term_ideal G'
:= by
  apply term_not_mem_leading_term_ideal
  intro g hg hg' s hs
  have := Set.mem_of_subset_of_mem (support_sub σ r₁ r₂) hs
  simp [-mem_support_iff] at this
  cases' this with hs hs
  ·exact hr₁.1 g hg hg' s hs
  ·exact hr₂.1 g hg hg' s hs

end Ideal

end MvPolynomial
