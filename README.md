# Trying to formalize some lemmas and theorems about ideal and variety of multivariable in lean

Mainly based on the book [_Ideals, Varieties, and Algorithms_](https://link.springer.com/book/10.1007/978-3-319-16721-3).

Lemmas and theorems that have been formlized:

```lean
lemma mono_in_mono_ideal_iff (hA: A.nonempty): mono ∈ ideal.span A ↔ ∃ (p₁ ∈ A), p₁ ∣ mono

lemma mem_mono_ideal_iff_term_mem: p ∈ span A ↔ ∀ v ∈ p.support, monomial v (coeff v p) ∈ span A
```
