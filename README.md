# Strict entropy concavity for weighted sums of four Bernoulli variables

**Ziyao Tang (唐梓耀), Ming Ding (丁铭)**

Public research draft **v1.0.1** · 26 November 2026 · English manuscript

[Read the manuscript](paper/bernoulli4_manuscript.pdf) · [Review and verification](notes/REVIEW.md) · [Release notes](RELEASE_NOTES.md) · [Citation metadata](CITATION.cff)

## Result

Let $B_1,\ldots,B_4$ be independent Bernoulli random variables with a common parameter $p$, and fix arbitrary positive real weights $w_1,\ldots,w_4$. Write

$$H_w(p)=H\!\left(\sum_{i=1}^4 w_i B_i\right),$$

where $H$ is discrete Shannon entropy with natural logarithms. The manuscript proves

$$H_w''(p)\le -16+6\log 6\qquad(0<p<1).$$

For each fixed weight vector, $H_w''$ is uniquely maximized at $p=1/2$. The upper bound is attained exactly when all four weights are equal and $p=1/2$, so $16-6\log 6$ is the optimal uniform strong-concavity constant. The entropy is strictly concave on $[0,1]$, symmetric under $p\mapsto1-p$, and uniquely maximized at $p=1/2$. The theorem includes irrational weights, repeated weights, and simultaneous subset-sum collisions. It concerns four fixed positive weights and one shared Bernoulli parameter.

This establishes the four-variable case of the recursive entropy-concavity conjecture in [Neunhäuserer, Conjecture 3.1](https://arxiv.org/abs/2609.05546v2). The arbitrary-length conjecture remains a separate problem.

## Verify the finite computations

Use **Python 3.10 or later** and its standard library. Verification needs no network access or third-party mathematics packages. From the repository root:

```sh
python proof/verify_all.py
```

The recorded local run passed all five checks:

1. Exhaustive classification for every positive real weight vector: **23 types**.
2. Exact entropy-loss identities, midpoint derivatives, and rational comparisons for the sharp bound.
3. A separate rational interval curvature check: **136 closed cells**.
4. Exact agreement of the classification, analytic, and interval template catalogues.
5. Both manuscript tables match their regenerated exact sources.

For a separately implemented classification check:

```sh
python proof/independent_classification_check.py
```

That checker uses determinants and Cramer's rule rather than the primary row-reduction routines. It also verifies a nonzero nonnegative row-space obstruction for each of the 306 excluded spaces.

Run the assertion-based verification programs without `-O` or `-OO`; their command-line entry points explicitly reject those modes. Local outputs are in [verification/combined.txt](verification/combined.txt) and [verification/classification_independent.txt](verification/classification_independent.txt).

## How the proof works

**Exact classification.** Every nontrivial equality between two subset sums gives one of 25 mixed-sign hyperplanes. Enumerating their possible row spaces, testing positive feasibility by rational vertices, and constructing witnesses that avoid all unforced equalities gives the complete catalogue:

| Rank | Candidate row spaces | Positive feasible spaces | Types modulo coordinate permutations |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 1 |
| 1 | 25 | 25 | 4 |
| 2 | 181 | 115 | 10 |
| 3 | 315 | 75 | 8 |
| **Total** | **522** | **216** | **23** |

The proof of completeness applies to arbitrary positive real weights. The small-integer examples are readable representatives, not the justification for completeness.

**Analytic curvature.** The entropy lost when equal sums merge is expressed using five elementary functions. The manuscript proves the required inequalities for all parameter values, including an all-orders power-series argument. The midpoint comparison uses the quartic coefficient of $F_{13}$. Exact rational comparisons across all 23 types show that every curvature maximum occurs at $p=1/2$ and that the equal-weight type uniquely attains $-16+6\log 6$. Finite coefficient checks in the program check transcription; the all-orders argument is in the paper.

**Separate interval check.** A second calculation differentiates the probability polynomials directly and encloses logarithms with rational bounds and an explicit remainder. It verifies $-p(1-p)H_w''(p)>1/50$ on all 23 types, using continuous endpoint extensions and symmetry. It shares the classification with the analytic proof but does not use the five-function estimates. The sharp uniform bound and its equality case follow from the analytic proof.

## Files

| Location | Contents |
| --- | --- |
| `paper/` | English PDF, XeLaTeX source, generated classification and budget tables, PDF build helper |
| `proof/classification.py`, `proof/classification.json` | Complete rational enumeration, witnesses, exclusions, and subset partitions |
| `proof/analytic_proof.py`, `proof/analytic_templates.json` | Exact entropy-loss reconstruction, midpoint derivatives, and sharp comparisons |
| `proof/curvature_certificate.py`, `proof/curvature_certificate.json` | Rational interval curvature certificate and verifier |
| `proof/verify_all.py` | Combined verification, including catalogue linkage and manuscript tables |
| `proof/independent_classification_check.py` | Determinant/Cramer implementation and exclusion certificates |
| `proof/manuscript_tables.py` | Deterministic table generation and comparison |
| `notes/` | Classification derivation, analytic derivation, and internal review summary |
| `verification/` | Recorded local verification and release-integrity results |
| `.github/workflows/verify.yml` | Configured verification workflow for Python 3.10 and 3.12 |
| `release/` | Citation and optional preprint-deposit metadata |
| `SHA256SUMS.txt` | SHA-256 hashes of every other file in the release |

## Regenerate data and tables

The commands below intentionally rewrite the generated proof data or table sources. Ordinary verification above is sufficient to check the supplied release.

```sh
python proof/classification.py
python proof/analytic_proof.py
python proof/curvature_certificate.py --output proof/curvature_certificate.json
python proof/manuscript_tables.py
python proof/verify_all.py
```

Individual certificate and table checks are also available:

```sh
python proof/classification.py --verify proof/classification.json
python proof/curvature_certificate.py --verify proof/curvature_certificate.json
python proof/manuscript_tables.py --check
```

## Rebuild the PDF

The supplied PDF is ready to read. Rebuilding it requires a configured **XeLaTeX** installation and these fonts: Liberation Serif, Liberation Sans, DejaVu Sans Mono, and Noto Serif CJK SC for the Chinese author names.

```sh
python paper/build_pdfs.py
```

The helper runs two passes, keeps intermediate files in `paper/_build/`, and writes `paper/bernoulli4_manuscript.pdf`. For a minimal Debian installation with incomplete TeX format/lookup configuration, the explicit fallback is:

```sh
python paper/build_pdfs.py --minimal-tex
```

Typesetting dependencies are separate from proof verification. They are not needed to run the certificate checks.

## Relation to prior work

- **Neunhäuserer:** [Recursive overlap Bernoulli distributions and an entropy concavity conjecture](https://arxiv.org/abs/2609.05546v2), Conjecture 3.1. The four-variable recursive law corresponds, up to translation and $p\mapsto1-p$, to weights $(1,a_2-a_1,a_3-a_2,a_4-a_3)$.
- **Amir's answer:** [MathOverflow question 514729](https://mathoverflow.net/questions/514729) formulates the positive-weight problem and reports 23 four-variable collision types, numerical checks of all 23, and analytic arguments for seven. The formulation and the count 23 are prior work. This manuscript supplies complete exact coverage and analytic estimates for every type.
- **Hillion and Johnson:** [A proof of the Shepp–Olkin entropy concavity conjecture](https://doi.org/10.3150/16-BEJ860), *Bernoulli* 23(4B) (2017), 3638–3649. Their theorem treats unweighted sums and includes the equal-weight case here. [Author preprint](https://arxiv.org/abs/1503.01570).

## Status, credit, and reuse

This is a public research draft with internal AI mathematical, computational, and literature review. It has not undergone external peer review or proof-assistant kernel formalization. No categorical priority claim is made. Readers can inspect the full analytic argument and rerun the finite certificate checks.

The local verification records are in [verification/](verification/). The [GitHub Actions workflow](https://github.com/Tang1206cc/bernoulli4-entropy-concavity/actions/workflows/verify.yml) checks both Python 3.10 and 3.12.

The authors used **ChatGPT (GPT-6.2 Astra)** to assist with mathematical derivations, internal proof checking, development and testing of the Python verifiers, and manuscript preparation. Tang and Ding take responsibility for the mathematical claims and the manuscript.

Use [CITATION.cff](CITATION.cff) or [release/citation.bib](release/citation.bib) when citing this version. The PDF and reproducibility archive are attached to the [v1.0.1 release](https://github.com/Tang1206cc/bernoulli4-entropy-concavity/releases/tag/v1.0.1).

Python code, JSON proof certificates, and workflow configuration are under **MIT**. The manuscript, generated TeX tables, and prose documentation are under **CC BY 4.0**. See [LICENSE](LICENSE) for the file-by-file scope.
