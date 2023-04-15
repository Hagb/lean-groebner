import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Algebra.Hom.Embedding
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
-- import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.LibrarySearch

variable {σ : Type _} {a a' a₁ a₂ : R} {n m : σ} {s : σ →₀ ℕ}

namespace MvPolynomial
variable [CommSemiring R]

@[simp]
lemma smul_monomial: a' • monomial s a = monomial s (a' * a) := by
  rw [smul_eq_C_mul, C_mul_monomial]

theorem support_zero_iff (p: MvPolynomial σ R): p = 0 ↔ p.support = ∅ :=
  by
  constructor
  · intro hp
    rw [hp]
    exact support_zero
  · intro hps
    rw [as_sum p, hps]
    exact rfl
#align mv_polynomial.support_zero_iff MvPolynomial.support_zero_iff

@[simp]
theorem support_smul_eq [IsDomain R] {a : R} (ha: a≠0) {f: MvPolynomial σ R}:
    (a • f).support = f.support := Finsupp.support_smul_eq ha


@[simp]
theorem support_mul_monomial [IsDomain R] (ha: a ≠ 0):
    (p * (monomial s a)).support = p.support.map (addRightEmbedding s) := by
  let key (q) := ∃ (s': σ→₀ℕ) (a': R), monomial s' a' = q ∧
          (a' ≠ 0 → (p * (monomial s' a')).support = p.support.map (addRightEmbedding s'))
  have hkey: key (monomial s a) := by
    apply induction_on_monomial
    ·
      intros a'
      use 0, a'
      -- simp?
      simp only [monomial_zero', ne_eq, true_and]
      intro ha
      unfold addRightEmbedding
      rw [mul_comm, C_mul', support_smul_eq ha, Finset.map_eq_image]
      -- simp?
      simp only [add_zero, Function.Embedding.coeFn_mk, Finset.image_id']
    ·
      intros q n hq
      rcases hq with ⟨s', a', hq, key'⟩
      use s' + (Finsupp.single n 1), a'
      constructor
      ·rw [←hq, monomial_add_single, pow_one]
      ·
        intro ha'
        specialize key' ha'
        rw [monomial_add_single, pow_one, ←mul_assoc, support_mul_X, key']
        unfold addRightEmbedding
        rw [Finset.map_eq_image, Finset.map_eq_image, Finset.map_eq_image,
            Finset.image_image]
        -- simp?
        simp only [Function.Embedding.coeFn_mk, comp_add_right]
  rcases hkey with ⟨s', a', hkey', hkey⟩
  -- simp? [monomial_eq_monomial_iff, ha] at hkey'
  simp only [monomial_eq_monomial_iff, ha, and_false, or_false] at hkey'
  exact (hkey'.1 ▸ hkey'.2 ▸ hkey) ha

@[simp]
theorem support_monomial_mul [IsDomain R] (ha: a ≠ 0):
    ((monomial s a) * p).support = p.support.map (addRightEmbedding s) :=
    mul_comm p (monomial s a) ▸ support_mul_monomial ha