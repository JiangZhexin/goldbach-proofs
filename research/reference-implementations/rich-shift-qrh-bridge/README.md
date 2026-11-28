# Binary-shift low-representation exceptional set: research draft

**Status: conditional Lean bridge, not a proof submission. Do not register this branch as a proof.**

Target: [L-goldbach-cut-6944b43b41bba1c895117f7b](https://www.goldbach.tech/?lemma=L-goldbach-cut-6944b43b41bba1c895117f7b).

The entry point is `RichShiftFinal263.exact_statement_of_public_zero_free_strip`.
Its conclusion is the frozen task statement. It has one explicit premise:
nonvanishing of every Dirichlet L-function to the right of 7/8, away from the
principal pole. The remainder of the argument was checked locally with
Lean 4.36.0 and the project's Mathlib pin; the entry point's axiom report
listed only `propext`, `Classical.choice`, and `Quot.sound`. The premise
is an argument, not an axiom, and this check does not discharge it.

The route uses the weighted singular model at a cutoff P comparable to
N^0.263, the corresponding zero-density and minor-arc bounds, and finite
transport for each allowed binary shift. The [public zero-free source](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
has the required statement. Its integration into the workbench's trusted
dependencies is not established; see the related [dependency discussion](https://github.com/CGandGameEngineLearner/goldbach-proofs/discussions/3806).

This snapshot includes the locally developed source graph reachable from
the entry point. `SOURCE-SHA256.txt` records it. It is not a standalone
Lake project: as listed in `EXTERNAL-IMPORTS.txt`, replay also needs Mathlib
and the compatible support libraries from the local build (Zeta23,
PrimeNumberTheoremAnd, LeanLab, and the OpenAI Ostmann arithmetic library).
Their source is not bundled. Existing source attribution notices are
preserved. The frozen task file, verifier settings, and allowed imports
are not changed. No verification or merge is requested by this upload.
