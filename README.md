# Trying to formalize some lemmas and theorems about ideal and variety of multivariable in Lean

I am learning algebraic geometry, and trying to formalize some lemmas and theorems about ideal and variety of multivariable in [Lean 4](https://leanprover.github.io)

Mainly based on the book [_Ideals, Varieties, and Algorithms_](https://link.springer.com/book/10.1007/978-3-319-16721-3).

## Definitions

- `TermOrder`: monomial orderings (Definition 1, page 71). The formal definition is from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Override.20default.20ordering.20instance/near/339882298 and https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Synonym.lean
- `multideg` multidegree, `lt` leading coefficient, `lm` leading monomial and `lt` leading term
<!--- `Reg`: division algorithm (partial Theorem 3, page 64) gives a remainder
- `isReg`: non-constructive equivalent definition of division-->

## Lemmas and theorems

- `mono_in_mono_ideal_iff`: (Leamma 2, page 70) Let $I=\left\langle x^\alpha | \alpha \in A \right\rangle$ be a monomial ideal. Then a monomial $x^\beta$ lies in $I$ if and only if $x^\beta$ is divisible by $x^\alpha$ for some $\alpha\in A$.
- `mem_mono_ideal_iff_term_mem`: (partial Lemma 3, page 71) Let $I$ be a monomial ideal, and let $f\in k\left[x_1,\dots,x_n\right]$. Then the following are equivalent:
    1. $f\in I$.
    2. Every term of $f$ lies in $I$.
- Some simple properties of monomial ordering
<!--- Division Algorithm is well defined-->

## TODO

- More properties of monomial ordering
- division algorithm (Theorem 3, page 64) giving a remainder
- Gröbner basis and its properties
