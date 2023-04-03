# Trying to formalize some lemmas and theorems about ideal and variety of multivariable in Lean

I am learning algebraic geometry, and trying to formalize some lemmas and theorems about ideal and variety of multivariable in [Lean](https://leanprover-community.github.io)

Mainly based on the book [_Ideals, Varieties, and Algorithms_](https://link.springer.com/book/10.1007/978-3-319-16721-3).

Lemmas and theorems that have been formlized:

- `mono_in_mono_ideal_iff`: (Leamma 2, page 70) Let $I=\left\langle x^\alpha | \alpha \in A \right\rangle$ be a monomial ideal. Then a monomial $x^\beta$ lies in $I$ if and only if $x^\beta$ is divisible by $x^\alpha$ for some $\alpha\in A$.
- `mem_mono_ideal_iff_term_mem`: (partial Lemma 3, page 71) Let $I$ be a monomial ideal, and let $f\in k\left[x_1,\dots,x_n\right]$. Then the following are equivalent:
    1. $f\in I$.
    2. Every term of $f$ lies in $I$.``
