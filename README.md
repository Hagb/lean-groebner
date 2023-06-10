# Lean4 formalization of Gröbner basis

(sorry for my bad English and bad math)

I am learning computational algebraic geometry, and have formalized Gröbner basis (and other things it needs) of multivariate polynomial in [Lean 4](https://leanprover.github.io).

Mainly based on the book [_Ideals, Varieties, and Algorithms_](https://link.springer.com/book/10.1007/978-3-319-16721-3).

## Definitions

- `TermOrder`, `TermOrderClass` ([`TermOrder.lean`](./TermOrder.lean)): monomial orderings and its class. The formal definition is learned from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Override.20default.20ordering.20instance/near/339882298 and https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Synonym.lean 
- `multideg`, `multideg'`, `multideg''` ([`Multideg.lean`](./Multideg.lean)): multidegree
- `leading_coeff`, `leading_term`, `lm` ([`Multideg.lean`](./Multideg.lean)): leading coeff, leading term and leading monomial
- `quo`, `rem`, `is_rem` ([`Division.lean`](./Division.lean)): the the quotient and the remainder of division with remainder
- `leading_term_ideal` ([`Ideal.lean`](./Ideal.lean)): the ideal span of leading terms of a set of multivariate polynomial.
- `is_groebner_basis` ([`Groebner.lean`](./Groebner.lean)): a finite set is a Gröbner basis of a ideal

## Main statements

### [`Division.lean`](./Division.lean)

(`rem_is_rem` and `exists_rem`) With a term order defined, such a multivariable polynomial $r\in k[x_i:x\in\sigma]$ exists for every multivariable polynomial $p$ and $G'$ a finite set of multivariable polynomial:

- for every $g\in G'\backslash\\{0\\}$, any terms of $s$ is not divisible by the leading term of $g$;
- such a function $q:G'\rightarrow k[x_i:x\in\sigma]$ exists:
    - for every $g\in G'$. $\text{multideg}(q(g)g)\le\text{multideg}(p)$,
    - $p=\sum_{g\in G'}q(g)g+r$.

I prove this statement by definition the division algorithm (`mv_div`, `quo`, `rem`) and proving its properties.

### [`Groebner.lean`](./Groebner.lean)

- `exists_groebner_basis`: with a term order defined, if the indexes of variables is finite, then all the ideals of the multivariable ring have Gröbner basis
- `groebner_basis_self`: Gröbner basis of a ideal is the Gröbner basis of the span of itself
- `groebner_basis_rem_eq_zero_iff`: the remainder of every elements in a ideal divided by the Gröbner basis of the ideal must be 0
- `groebner_basis_def`: for finite set $G'\subseteq k[x_i:x\in\sigma]$ and ideal $I$, $G'$ is a groebner basis of $I$ if and only if $G'\subseteq I$ and $0$ is a reminder of every $p\in I$ divided by $G'$
- `groebner_basis_is_basis`: every ideal is equal to the span of its Gröbner basis
- `groebner_basis_unique_rem`: the remainder of a multivariable divided by a Gröbner basis exists and is unique

## TODO

- Refactor to allow to deal with different kinds of term orders (there is a related [zulip topic](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Formalization.20of.20multideg.2C.20division.2C.20etc.2E.20of.20MvPolynomial))
- Lexicographic order is a term order
- remove `multideg'`
- More properties of Gröbner basis
- Submit to Mathlib4 (maybe partically, because I think the quality of most of my code is not high enough for Mathlib4)
- Improve the readability of the code, and write more comments and documents

## License

Apache License 2.0
