# Release notes — v1.0.0

26 November 2026. This release contains the English public research draft and its exact verification materials.

## Mathematical content

- The theorem covers four independent Bernoulli variables with a common parameter and arbitrary fixed, strictly positive real weights. With natural logarithms, $H_w''(p)\le -16+6\log 6$ on $0<p<1$. Equality holds exactly when all four weights are equal and $p=1/2$.
- The exact classification covers 522 candidate rational row spaces, 216 positive feasible spaces, 306 excluded spaces, and 23 equality types modulo coordinate permutations.
- Five elementary entropy-loss functions and exact finite comparisons give the sharp uniform curvature bound. All-orders coefficient positivity is proved analytically.
- A separate rational interval calculation verifies strict curvature on all 23 types using 136 cells. It shares the exhaustive classification but does not use the analytic loss-function bounds.
- A second classification implementation uses determinants, Cramer's rule, and nonnegative row-space obstructions.

## Final revisions

- Defined the fixed finite support explicitly and justified smoothness on the open parameter interval.
- Distinguished equality types from entropy templates and stated their correspondence in this four-variable classification.
- Clarified endpoint continuity, symmetry, and the scope of the two curvature calculations.
- Added the sharp curvature proof, equality characterization, and direct exact midpoint derivative checks for all 23 types. The three certificate data files retain their original mathematical contents.
- Credited the prior weighted formulation, the reported count of 23 types, and the existing partial four-variable work.
- Kept all three requested authors in the manuscript, PDF metadata, README, and citation files.

## Reproducibility and packaging

- Separated the paper, proof programs, derivation notes, and recorded verification outputs into clear directories.
- Updated path handling so the combined verifier and table checks work from both the repository root and an unrelated working directory.
- Retained explicit rejection of optimized Python execution in assertion-based verification entry points.
- Included a XeLaTeX build helper and an explicit fallback for minimal Debian TeX installations.
- Included a GitHub Actions workflow with fixed action commits and a Python 3.10/3.12 test matrix.
- Added citation metadata, license scopes, optional preprint metadata, and a release hash manifest.

The manuscript and repository materials are English. Chinese names identify the human authors. External peer review, a DOI, and formal proof-assistant verification are not part of this release.
