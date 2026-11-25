# Computer checks for `../paper.tex`

These are plain Python 3 scripts with no dependencies. Run them with `python3 -I <script>`.

| Script | What it checks | Log |
|---|---|---|
| `ppconstruct_or_from_s3.py` | Theorem B, exhaustively. The 3rd pp-power **P** of S3^[3] and the Lichter–Pago template `OR_T[Z2^[3], Z3^[3]]` are homomorphically equivalent. Every relation of **P** is a coset, and each one is the stated pp-formula over ternary cosets of S3 (with at most one auxiliary variable). It covers all 51 cosets of Z2^3 and all 184 cosets of Z3^3, in about 15 s. | `ppconstruct_or_from_s3.log` |
| `ppconstruct_schmidt.py` | The general construction of Theorem B, for six groups H = E ⋊ Z_q: S3, D10, Z7:Z3, A4, Z11:Z5 and F2^3:Z7. Every relation of the pp-power **T** is a coset (a subgroup check on H^3, or an affine check for the Z_q-relations). The map from the Lichter–Pago or-template into **T** is a homomorphism. The twist matrices satisfy N_0 = 0, N_1 = 1, and N_s is invertible for s ≠ 0. It takes about 5 min. | `ppconstruct_schmidt.log` |
| `decomp_check.py` | The structural lemmas of Section 4 on random instances (arity 2–3, repeated variables) over 13 groups of the class C. These are the exact shape formula (Lemma 4.2), the eigenspace splitting (Lemma 4.3(b)), coherence of `c(τ)`, the decomposition (Lemma 4.4) and the dichotomy (Lemma 4.5). It builds the Galois ring, the Teichmüller group, the characters, the points, blocks and components, and the systems `L_K(γ)` and `A_K`. Usage: `decomp_check.py [trials] [seed] [group] [--mutant]`. The `--mutant` flag replaces χ(q°)⁻¹ by χ(q°) and must produce `decomp_FAIL`, which shows that the check can detect a wrong formula. It was written during an independent check of the draft. | `decomp_check.log` |
| `locality_check.py` | Whether coordinatewise fibre translations exist (the conclusion of Lemma 4.2). They exist for every sampled coset over S3, D10, Z7:Z3, Z5:Z4 and A4. They fail for many cosets over the non-coprime groups D4 and Z9:Z3, which shows that coprimality is needed. | `locality_check.log` |
| `nonabelian_action_check.py` | An exploratory test with a non-abelian action, F5^2 ⋊ S3. Random instances rarely produce interesting structure, so the result is inconclusive. | — |

None of these runs the cohomological algorithm itself. That would need integer Hermite or Smith normal forms, and small instances do not separate it from ℤ-affine consistency anyway.
