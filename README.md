# Demystifying Tubal Tensor Algebra — Lean 4 formalization

A Lean 4 / Mathlib formalization of all numbered results of
H. Avron and U. Mor, *Demystifying Tubal Tensor Algebra* (arXiv:2506.03311v2).

* `mapping.md` maps every numbered result (theorems, lemmas, propositions, corollaries,
  definitions, examples, remarks, facts, the algorithm) to its Lean declaration(s), and lists the
  (few, justified) places where the paper has typos.
* Everything is proved: no `sorry` and no axioms beyond Lean's standard ones.

## Building

```sh
# Lean toolchain via elan (https://github.com/leanprover/elan)
lake exe cache get      # download prebuilt Mathlib
lake build              # build the formalization
python3 scripts/axiom_audit.py   # check that no non-standard axiom (or sorry) is used
```

## Layout

| File | Contents |
|---|---|
| `TubalAlgebra/Defs.lean` | `⋆_M` (Eq. 5), row-conjugation condition, the type `KM M` of tubes |
| `TubalAlgebra/Frobenius.lean` | Theorem 1 (Frobenius) |
| `TubalAlgebra/Realness.lean` | Lemmas 2, 7, 63, 64, 65 |
| `TubalAlgebra/KMRing.lean` | Theorem 3, Proposition 6, Lemma 8, the ring `𝕂_M` |
| `TubalAlgebra/NotField.lean` | Proposition 5 |
| `TubalAlgebra/TubalRing.lean` | Definition 10 (tubal rings) |
| `TubalAlgebra/Canonical.lean` | Definition 12, Propositions 13, 66 |
| `TubalAlgebra/Count.lean` | number of tubal rings up to isomorphism |
| `TubalAlgebra/Module.lean` | Theorems 19, 20 |
| `TubalAlgebra/Tensor.lean` | Definitions 21, 23, Remark 22, Proposition 24 |
| `TubalAlgebra/Transform.lean` | Fact 25, Examples 26, 27 |
| `TubalAlgebra/MatrixSVD.lean` | matrix SVD and the Eckart–Young theorem |
| `TubalAlgebra/TSVD.lean` | Definitions 28, 29, 31, Theorem 30, Lemma 32 |
| `TubalAlgebra/EckartYoung.lean` | Lemma 33, Corollary 34, Theorems 35, 37, Definition 36 |
| `TubalAlgebra/Section9/*.lean` | Section 9: Lemma 38 – Proposition 62, Theorem 11 |
| `TubalAlgebra/Hilbert.lean` | Propositions 70, 71 |
| `TubalAlgebra/Examples/*.lean` | Examples 4, 14–18, Eq. (3), 67–69, Algorithm 1 |

## Candidate contributions to NLAlib

`ForNLALib/` is a separate Lake package (Lean/Mathlib v4.33.1, depending on
[NLAlib](https://github.com/NLA-lib/NLAlib)) that collects the general numerical-linear-algebra
results of this formalization, rewritten in NLAlib's conventions as proposals for upstreaming.
The formalization does not depend on it; see `ForNLALib/README.md`.
