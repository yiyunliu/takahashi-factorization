# A Coq mechanization of the factorization theorem for the untyped lambda calculus
This repository contains mechanized proofs Hindley's postponement
theorem for the head reduction
([normalization_h.v](theories/normalization_h.v))
and leftmost-outermost reduction
([normalization_lo.v](theories/normalization_lo.v)) strategies.

The proof is based on
[Takahashi's
proof](https://www.sciencedirect.com/science/article/pii/S0890540185710577)
and structured in a way similar to [Accattoli et
al. 2019](https://link.springer.com/chapter/10.1007/978-3-030-34175-6_9).

I managed to prove
postponement for leftmost-outermost reduction directly without using
the complex setup involving indexed parallel reduction, a proof device
introduced by Accattoli to work around the limitation of Takahashi's
method.

Indexed parallel reduction is nice on paper, but is painful to
mechanize, especially when the development relies on simultaneous
substitution for its metatheory; the generalized substitution property
(morphing lemma) would require adding up the number reductions for
each pair of reductions to substitute. The development avoids indexing
altogether and instead uses Takahashi's * operator to bound the
reduction steps.

Despite Accattoli's observation that Takahashi's method fails to work
on leftmost-outermost reduction, it's possible to revise her statement
of Lemma 2.4 to a more generous statement (`ipar_starseq_morphing` in
the development) to remove the dependency on the left-substitutivity
of the essential reduction relation. This revised statement not only
holds for both head and lo reductions, but is also much easier to
prove.
