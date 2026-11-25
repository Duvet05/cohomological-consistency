# CohCons: Lean formalization

Machine-checked parts of `../paper.tex` (and of the earlier `../note.tex`). The development
uses Lean 4 (v4.37.0-rc1) and Mathlib.

```sh
lake exe cache get   # prebuilt Mathlib, once
lake build           # checks everything
```

Every theorem below depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), and there is no `sorry`.

## Two algorithms at once

Stability carries a Boolean parameter `pin`. Every result is stated for both values.

- `pin = true` means cohomological k-consistency: every pinned system `L(B,S)` has an
  integer solution.
- `pin = false` means ℤ-affine k-consistency: the unpinned system `L(B,S)` has an integer
  solution.

`Solvable pin k S` is that condition. `Stable pin B A k S` adds the k-family conditions
(S1) and (S2), and `Accepts pin k B A` asks for a nonempty stable family.

## What is proved

| Paper | Lean | File |
|---|---|---|
| Stable families, acceptance | `Stable`, `Solvable`, `Accepts` | `Basic.lean` |
| Cohomological k-consistency as a removal process | `initial`, `Bad`, `Step`, `Run`, `Terminal`, `Outcome`, `AlgAccepts` | `Basic.lean` |
| Lemma 2.2 for `C` (any removal order) | `run_accepts_iff`, `algAccepts_iff`, `outcome_independent` | `Basic.lean` |
| ℤ-affine k-consistency as defined by Dalmau–Opršal and Lichter–Pago | `Consistent`, `kcons`, `AffAlgAccepts` | `Basic.lean` |
| Lemma 2.2 for `Z` | `affAlgAccepts_iff` | `Basic.lean` |
| Lemma 2.3(i) soundness | `accepts_of_hom` | `Basic.lean` |
| Lemma 2.3(iii) `C` accepts ⇒ `Z` accepts | `Accepts.toAffine` | `Basic.lean` |
| Lemma 3.1 (transfer) | `transfer` | `Transfer.lean` |
| Lemma 2.3(ii) monotonicity | `accepts_mono` | `Transfer.lean` |
| Template homomorphisms | `accepts_of_template_hom` | `Transfer.lean` |
| pp-powers (gadget instances) | `accepts_gadget`, `hom_of_gadget_hom` | `PPPower.lean` |
| Removing equality | `accepts_quot`, `hom_of_quot_hom` | `Equality.lean` |
| Gadget sizes | `size_gadget_le`, `size_quot_le` | `Main.lean` |
| Theorem C | `solves_of_ppConstr` | `Main.lean` |
| Constant and o(n) levels | `solves_const_of_ppConstr`, `solves_sublinear_of_ppConstr` | `Main.lean` |
| `Solves true` / `Solves false` are about the two algorithms | `solves_true_iff`, `solves_false_iff` | `Main.lean` |

`Transfer.lean` contains one lemma, `transfer`, that covers the common part of all the
reductions. It pushes a stable family forward along a map of domains σ and a map ι that
commutes with restriction. Solutions, pinned or not, are pushed forward by summing over
fibres.

## How the formal statements match the paper

- **Partial maps:** they are `β → Option α`. A family is a `Finset` of partial maps. The
  variable `z_{X,f}` is `z f`, because the domain of `f` is `X`.
- **Equation (C):** it is stated for `Y ⊆ X`. `sys_iff_strict` proves this is the same
  system as the version with `Y ⊊ X`.
- **Cohomological k-consistency:** it is a removal process. Any element that fails a
  k-consistency check or a pinned-system check may be removed, one at a time or many at
  once, and all terminated runs agree.
- **ℤ-affine k-consistency:** `kcons B A k` is the largest k-consistent family, which is
  the output of the k-consistency algorithm. The algorithm accepts iff `L(B, kcons)` has an
  integer solution. Lichter–Pago also reject when some `κ(X)` is empty, but equation (N)
  already forces every `κ(X)` to be nonempty, so this changes nothing.
- **Equality:** `eq` is the binary relation of tuples whose entries are all equal.
- **pp-power formulas:** they are lists of atoms over the symbols of Γ together with
  `eq`, with existential variables `Fin m`.
- **Arities:** the signatures created by pp-power steps have positive arities. This is used
  only for the size bound `‖I♯‖ ≤ c‖I‖`.

## Not formalized

- Theorem A (Section 4 of the paper), which uses group cohomology and Galois rings.
- The concrete pp-construction of Theorem B. It is checked by the script
  `../checks/ppconstruct_or_from_s3.py`.
- The characterizations of BLP+AIP and CLAP by minor conditions, BOP18's characterization of
  pp-constructibility by minion homomorphisms, and the lower bounds of Lichter–Pago and
  Conneryd–Ghannane–Pang. These are cited results.
