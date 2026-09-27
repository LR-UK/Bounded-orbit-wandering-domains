# Prepared Palomar submission

The six revised-paper targets are proved. Submit the publicly uploaded repository
at the immutable commit identified in the delivery's `UPLOAD-INSTRUCTIONS.txt`.
Nothing has been uploaded or submitted by the assistant.

- Challenge: `PaperChallenge`
- Solution: `PaperSolution`
- Comparator configuration: `comparator.json` (identical to `comparator-paper.json`)
- Metadata: `formalization.yaml`
- Local audit: `verification/paper-submission.json`
- Compiler: `leanprover/lean4:v4.35.0-rc2`

The primary comparator selects all six introductory statements. Earlier
formulations retain `comparator-legacy.json` and `comparator-singular-limits.json`.

After uploading, let the provided Linux CI run the metadata contract and official
Comparator with its bundled independent kernels. Use the full immutable commit
SHA for the submission. See VERIFICATION.md for the completed local checks and
the external checks that have not yet been run.

## Why there are two paper files

PaperChallenge.lean independently states the six targets from the revised paper
(Theorems 1.2-1.5, with separate cases exposed individually). Its proof holes
are intentional specifications. PaperSolution.lean supplies the matching proved
declarations through the supporting libraries. These are the current revised
paper statements; the earlier submission pairs are retained in Legacy/.
The current configuration does not require those older pairs.

Palomar requires separate challenge and solution modules, but their names are
configurable. A single configuration can select multiple theorem declarations.
See the [submission rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).

Adding mathematical results is distinct from a maintenance update of an existing
registry entry: the [protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md#registration-versions-and-publication)
assigns corrections and dependency updates a further version, and new mathematical
results a new identifier. This package does not choose or modify a registry ID.
