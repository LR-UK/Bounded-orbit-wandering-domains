# Prepared Palomar submission

This is a source package for review and publication, not an already submitted
or registered Palomar entry.

- Project directory: repository root.
- Challenge module: `Challenge`.
- Solution module: `Solution`.
- Comparator configuration: `comparator.json`.
- Metadata: `formalization.yaml`.
- Licence: Apache-2.0, with inherited notices retained.
- Lean: 4.34.0.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

The Challenge has two intentional theorem holes and only Mathlib imports.
The Solution does not import the Challenge. Comparator is configured to compare
the two theorems and all nine public supporting definitions, including the
sphere's uniform-space instance, and to enable NanoDa.

Local build, source, axiom and declaration checks are described in
VERIFICATION.md. Official Palomar Comparator/NanoDa and metadata-policy
validation have not been run in this environment.

For actual submission, publish these sources (including both contained
dependencies) in a public GitHub repository and select its full immutable
40-character commit SHA. Use that repository and SHA with the root layout above.
No repository URL, public commit or submission identifier has been invented.

Preparation follows the official instructions inspected on 22 September 2026:
https://palomar-registry.org/how-to-submit
and the configuration shape in:
https://github.com/PalomarRegistry/PalomarTemplate

