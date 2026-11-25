# Cohomological k-consistency on group coset-CSPs

This is a research side thread. The main document is `paper.tex` (compiled to `paper.pdf` with `tectonic -X compile paper.tex`).

**Theorem A.** Ó Conghaile's cohomological k-consistency solves every r-ary coset-CSP at level max(3, r) over every finite group in a class C.
- C is the class of groups with a normal series whose factors are abelian, of order coprime to their index, and acted on through abelian groups.
- Examples: S3, A4, the dihedral groups of order 2n with n odd, all groups of square-free order, all Z-groups, and every group of order below 24 except the non-abelian 2-groups.
- The proof exists on paper only.

**Theorem B.** For every non-nilpotent group G, none of these solves the ternary coset-CSP over G: ℤ-affine k-consistency (at every sublinear level), BLP+AIP and CLAP.
- So these algorithms can solve all coset-CSPs over G only if G is nilpotent. Lichter–Pago showed that 2-nilpotent groups of odd order suffice.
- For S3, the template even pp-constructs the Lichter–Pago template OR_T[Z2^[3], Z3^[3]].
- With Theorem A, every non-abelian group in C separates the cohomological algorithm from these three algorithms.

**Theorem C.** Both cohomological and ℤ-affine k-consistency are preserved under pp-constructions, at constant and at sublinear levels. This is machine-checked in Lean.

Contents:
- `paper.tex`, `paper.pdf`: the current write-up.
- `note.tex`, `note.pdf`: the first note, which covers only pp-construction invariance. It is superseded by the paper and partly by Barto–Hadek–Zhuk (2026).
- `lean/`: the Lean 4 + Mathlib formalization of Theorem C and its supporting lemmas. Build it with `lake build`; see `lean/README.md`.
- `checks/`: Python scripts and their logs; see `checks/README.md`.

Status: draft, not refereed.
- An independent internal check covered Theorem A and the S3 case of Theorem B. It found no gap, and its corrections are in.
- The general part of Theorem B was re-checked only by the author, against the source of Lichter–Pago. That re-check fixed one statement: for CLAP, the accepted no-instance is B plus one disjoint tuple, as in their Lemma 5.6.
