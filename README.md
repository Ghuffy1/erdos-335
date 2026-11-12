# Erdős problem 335

## A periodic-summand characterization

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer

This repository contains the mathematical proof notes and Lean 4 formalization of a characterization of positive-density sets of positive integers satisfying

$$d(A+B)=d(A)+d(B).$$

The stronger formulation identifies a modular boundary case and, under a strict modular-density surplus, three structural alternatives with exact tests that retain every exceptional element. The result is submitted for mathematical review as a complete solution of Erdős problem 335, catalogued as JSP-000278.

- [Mathematical proof and overview](paper/README.md)
- [Closed stronger theorem and original positive-count formulation](Erdos335/FullPeriodicClassification.lean)
- [Closed earlier full characterization](Erdos335/FullClassification.lean)
- [Definitions of the stronger structural alternatives](Erdos335/PeriodicRefinementSpecification.lean)
- [Verification and reproduction](verification/README.md)
- [Authorship, AI assistance, and prior work](ATTRIBUTION.md)

## Formal targets

```lean
Erdos335.Proposed.full_classification
Erdos335.Proposed.full_classification_original_positive_counts
Erdos335.Proposed.full_periodic_classification
Erdos335.Proposed.full_periodic_classification_original_positive_counts
```

Both original-count theorems quantify over arbitrary subsets of the positive natural numbers, assume positive ordinary input densities, and give an if-and-only-if characterization of the required ordinary sumset density. Their closed proofs include the local inverse analysis, global assembly, and all terminal alternatives.

## Reproduce the proof

Lean is pinned to `leanprover/lean4:v4.34.0`. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`, with its transitive dependencies fixed in `lake-manifest.json`.

```sh
python scripts/check_sources.py
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean verification/CheckAxioms.lean
lake env leanchecker --fresh -v Challenge
```

The recorded development run compiled the complete source, audited 2,602 named declarations, and completed an empty-environment kernel replay of the imported proof closure. Its only audited axiom dependencies were `propext`, `Classical.choice`, and `Quot.sound`. All 892 canonical Lean files and dependency pins in this public snapshot have the same bytes as that verified run. The accompanying reproduction and source comparison describe the check performed on this publication snapshot. [Verification record](verification/README.md)

External mathematical acceptance, publication priority, and prize eligibility are subject to review. The official catalog and original problem describe the target. [Erdős 335](https://www.erdosproblems.com/335), [JSP-000278](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#jsp-000278)
