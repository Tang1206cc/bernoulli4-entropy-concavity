# Lean formalization

This working branch formalizes the result published in
[v1.0.1](https://github.com/Tang1206cc/bernoulli4-entropy-concavity/releases/tag/v1.0.1).

The first verified milestone is `Bernoulli4.equalWeight_midpoint_curvature`.
For every positive common weight it computes the second derivative of the
Shannon entropy at `p = 1/2` as `-16 + 6 * Real.log 6`. The proof starts
from the sixteen weighted outcomes, merges collisions, and derives the
binomial probability polynomials. The uniform curvature bound for arbitrary
positive weights is the next theorem to be assembled.

Use the pinned toolchain from `lean-toolchain` and the dependency revisions
in `lake-manifest.json`. From this directory, with Elan installed, run

```sh
lake exe cache get Bernoulli4.lean
lake build
lake env lean Audit.lean
```

The audit checks the exact dependency list of the exported midpoint theorem
against Lean's standard mathematical axioms.
