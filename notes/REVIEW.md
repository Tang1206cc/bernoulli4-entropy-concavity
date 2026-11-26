# Internal review and verification

Version 1.0.0 · prepared 26 November 2026

This note records the checks performed while preparing the public research draft. The reviews were internal AI reviews. They are not external refereeing, an endorsement by a third party, or a proof-assistant kernel check.

## Mathematical review

The review checked the statement and its hypotheses, the complete classification argument for arbitrary positive real weights, the analytic entropy-loss identities, the all-orders coefficient arguments, the signs in the curvature budget, and the extension of strict concavity to the endpoints. The final review also checked the sharp curvature comparison and the full equality characterization.

The proof has two distinct components. The manuscript justifies the reduction to a finite classification and proves the analytic inequalities. Exact rational programs check the entire finite catalogue, its certificates, and every coefficient budget used by the proof. A finite numerical scan is not used to infer the theorem over all real weights or all parameter values.

Three final clarifications were incorporated: the finite support is fixed while the Bernoulli parameter varies; equality types mean labeled subset partitions modulo coordinate permutations; and the interval curvature calculation is separate from the analytic loss-function estimates while sharing their classification input.

No mathematical release blocker was identified in the internal reviews. The conclusion remains open to correction through independent scrutiny of the manuscript and accompanying code.

## Computational checks

The recorded combined verification checks:

- The full 522-space universe and every positive/excluded classification certificate.
- Every entropy-loss identity, exact midpoint derivative, and rational comparison for the sharp bound in the 23-row table.
- All 136 rational interval cells, including coverage and rational logarithm enclosures.
- Exact equality of the three template catalogues.
- Exact regeneration of both tables included in the manuscript.

The additional classification implementation uses determinant span tests and Cramer's rule. It reconstructs the 216 feasible spaces and 23 permutation orbits and checks a nonzero nonnegative row-space vector for each of the 306 excluded spaces. It is a separate implementation of the finite classification, not an independent source of the underlying theorem.

The interval calculation uses the probability polynomials directly. Its bound on $-p(1-p)H_w''$ proves strict curvature, while the manuscript's analytic argument supplies the sharp uniform bound $H_w''\le -16+6\log 6$ and the equality characterization.

Local command outputs are provided in [combined.txt](../verification/combined.txt) and [classification_independent.txt](../verification/classification_independent.txt). The programs use exact integers and rational numbers. Finite coefficient checks are transcription checks; the proof of positivity for every series index remains the analytic argument in the paper.

## Release checks

The verification commands and manuscript-table checks were run from the repository root and an unrelated working directory. All five assertion-based command-line entry points reject `-O` and `-OO`. Core mathematical algorithms and the three JSON certificate files were preserved during directory relocation. The release includes recorded [integrity checks](../verification/release_integrity.txt).

The bundled records identify the local execution environment. The GitHub workflow records the remote runs for Python 3.10 and 3.12.

The final PDF was rebuilt from the shipped source and inspected for author information, tables, formula layout, cross-references, and font/overflow issues. The final archive was extracted into a fresh directory, its hash manifest was checked, and the main and separate classification checks were rerun there.

## Attribution and scope

The weighted formulation, the reported count of 23 types, and the prior partial four-variable analysis are attributed to the sources listed in the manuscript and README. The checked sources did not identify an earlier complete proof for all four positive weights; that finding does not establish categorical priority.

The result concerns four summands with a common parameter. It makes no claim for arbitrary numbers of summands, or joint concavity in unequal Bernoulli parameters. The optimal curvature constant applies uniformly within the stated four-variable setting. The release preserves the requested author order: Ziyao Tang, Ming Ding, ChatGPT.
