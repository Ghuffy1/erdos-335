# Attribution

## Project authors

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer are the named authors of this submitted work. The project used OpenAI Codex for mathematical research, proof review, Lean development, and preparation of the submission. The submitting team is responsible for the mathematical and formalization claims. The repository preserves the proof sources and evidence needed to review those claims.

The named team developed the full characterization and its stronger periodic-summand refinement. The public source snapshot preserves the verified code. Per-person credit and prize allocation remain matters for the authors and the organizer's attribution review. No independent human-verifier credit is asserted here.

## Mathematical antecedents

The proof uses the intermediate-scale and all-residue inverse results of Ethan Ackelsberg and Florian Richter, compact and Loeb inverse-theorem methods of John T. Griesmer, and the classical density and sumset theorems of Kneser, Mann, and Dyson. The detailed mathematical source notes identify the statements used. Patrick White and Claude's July 2026 working report is credited for the earlier ultimately periodic criterion. The new claims concern the complete unrestricted characterization and its stated refinement. [Mathematical notes](paper/README.md)

## Imported formalizations

- The finite Kneser formalization by Augustinas Bakšys and Yaël Dillies is imported from `YaelDillies/MiscYD` at `ca0b3bbc903dae81e361f5f30f8ed8c98d43fad8`. Original headers and the Apache 2.0 license are preserved. [Provenance](third_party/MiscYD_Kneser.json)
- Mann/Dyson counting support is adapted from Steve Hubbard's `sthubbar/goldbach-lean` at `559706d617bc554787e10dba07066dc63ab69cb5`, whose header credits Claude assistance. The provenance record describes the adaptation, and original files and Apache 2.0 license are preserved. [Provenance](third_party/Mann_Dyson.json)
- Additive-circle equidistribution support is adapted from the source recorded in the NumStability provenance file. Its original file and MIT license are preserved. [Provenance](third_party/NumStability_Equidistribution.json)

Mathlib and Lean retain their respective upstream authorship and licenses. Imported formalizations and classical theorems retain the credits stated above.
