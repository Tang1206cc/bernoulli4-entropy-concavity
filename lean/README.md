# Lean formalization of the four-Bernoulli theorem

The formalization starts from the sixteen outcomes of four independent
Bernoulli variables with a common parameter. Outcome masses are grouped by their weighted value before evaluating
Shannon entropy. The weights are arbitrary positive
reals. The paper and its separate Python verification package are archived
in [v1.0.1](https://github.com/Tang1206cc/bernoulli4-entropy-concavity/releases/tag/v1.0.1).

| Lean theorem | Statement |
| --- | --- |
| `Bernoulli4.sharp_curvature_bound` | The second derivative on the open parameter interval is at most `-16 + 6 * Real.log 6`. |
| `Bernoulli4.sharp_curvature_equality_iff` | Equality holds exactly at equal weights and parameter one half. |
| `Bernoulli4.curvature_lt_midpoint` | For each fixed positive weight vector the curvature is strictly below its midpoint value at every other interior parameter. |
| `Bernoulli4.entropy_strictConcave` | The entropy is strictly concave on the closed unit interval. |
| `Bernoulli4.entropy_symm` and `Bernoulli4.entropy_lt_midpoint` | The entropy is symmetric and uniquely maximized at one half. |

The integer case tree certifies coverage for real weights. Its leaves
either rule out a pattern using a checked linear combination, or identify
one of 216 witnesses. The kernel then checks their correspondence to the
23 profiles and verifies the entropy loss identity and curvature budget
for every profile. The mixed-loss bounds use explicit sixth derivatives
and convexity. The analytic proof in the Lean library is independent of
the supplemental 136-interval Python check.

## Build and audit

Install Elan and use the pinned versions in `lean-toolchain` and
`lake-manifest.json`. Run the following from this directory.

```sh
sed -nE 's/^(public )?import (Mathlib[.][[:alnum:]_.]+)$/\2/p' Bernoulli4/*.lean | sort -u | xargs lake exe cache get
lake build
lake env lean Audit.lean
```

The audit checks the axiom dependencies of the exported theorems against
Lean's standard mathematical axioms. The optional Python generators
reproduce the case data and algebraic identity source from the published
certificates. The generated sources are included in the Lean build.
