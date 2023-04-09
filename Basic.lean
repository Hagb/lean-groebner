import Mathlib.Data.MvPolynomial.Basic

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