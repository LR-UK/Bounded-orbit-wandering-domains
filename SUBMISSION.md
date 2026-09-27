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
