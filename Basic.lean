import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Algebra.Hom.Embedding
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

namespace MvPolynomial
variable {σ : Type _} {a a' a₁ a₂ : R} [CommSemiring R]
variable {n m : σ} {s : σ →₀ ℕ}
variable (p: MvPolynomial σ R)

-- Has been submitted to Mathlib/Mathlib4
@[simp]
lemma smul_monomial': a • monomial s a' = monomial s (a * a') := by  
  rw [smul_eq_C_mul, C_mul_monomial]
  -- exact (smul_eq_C_mul (monomial s a') a).symm ▸ C_mul_monomial

-- Have submitted to Mathlib/Mathlib4
theorem support_eq_empty': p.support = ∅ ↔ p = 0 := by  
  constructor  
  ·    
    intro hps    
    rw [as_sum p, hps, Finset.sum_empty]    
  ·    
    intro hp    
    rw [hp]    
    exact support_zero    

variable [NoZeroDivisors R] {a: R} (s: σ→₀ℕ) (ha: a ≠ 0) (p: MvPolynomial σ R)

-- Has been submitted to Mathlib/Mathlib4
@[simp]
theorem support_smul_eq': (a • p).support = p.support :=
  Finsupp.support_smul_eq ha

@[simp]
theorem support_mul_monomial:
    (p * (monomial s a)).support = p.support.map (addRightEmbedding s) := by
  classical
  rw [Finset.map_eq_image, Function.Embedding.coeFn_mk]  
  let key (q) :=
      ∃ (s': σ→₀ℕ) (a': R),
        (monomial s' a' = q ∧
        (a' ≠ 0 → (p * (monomial s' a')).support = p.support.image (·+ s')))
  obtain ⟨s', a', hkey', hkey⟩: key (monomial s a) := by
    apply induction_on_monomial    
    · intros a'
      use 0, a'
      simp
      intro ha
      rw [mul_comm, ←smul_eq_C_mul, support_smul_eq ha]    
    · rintro q n ⟨s', a', hq, key'⟩
      use s' + (Finsupp.single n 1), a'
      simp [monomial_add_single, ←hq]
      intro ha'
      rw [←mul_assoc, support_mul_X, key' ha', Finset.map_eq_image]
      simp [Finset.image_image, addRightEmbedding]
  simp [monomial_eq_monomial_iff, ha] at hkey'
  exact (hkey'.1 ▸ hkey'.2 ▸ hkey) ha

@[simp]
theorem support_monomial_mul :
    ((monomial s a) * p).support = p.support.map (addLeftEmbedding s) := by  
  simp only [add_left_embedding_eq_add_right_embedding,
            mul_comm p (monomial s a) ▸ support_mul_monomial s ha p]
