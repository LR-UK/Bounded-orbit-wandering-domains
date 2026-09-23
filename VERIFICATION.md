# Local verification

The Lean 4.34.0 build of Submission and Challenge succeeded against Mathlib
5ed2965256430c3649e86755f9576b54eca72435. The full build involved 3,782 jobs,
including cached dependencies. Challenge has two intentional proof holes.
The Solution and root proof modules have none.

The final two theorem axiom reports and the Fatou-component bridge report
use only propext, Classical.choice and Quot.sound. These reports cover
transitive proof dependencies.

Two separate environments export the two theorem types and nine supporting
definition types and bodies. Comparison erases bound-variable display names
and nonsemantic metadata, retaining constants, universe information, binder
information and expression structure. This is a local syntactic audit, not
the official Palomar Comparator or NanoDa.

Run `python3 scripts/verify_submission.py` to reproduce the checks.
The current report and logs are in verification/. Challenge has only Mathlib
direct imports, with none shadowed by project or contained-dependency sources.

Official Comparator, NanoDa and metadata-policy validation remain unrun.
The supplied configuration enables NanoDa and permits only standard axioms.
The older area-development logs are historical evidence, not the current
submission report. The finite-puncture metric hypothesis is not proved here.

