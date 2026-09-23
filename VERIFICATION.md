# Local verification

The entire-function theorem now assumes boundedness of one point's forward
orbit, not boundedness of the union of the Fatou components. The theorem
remains conditional on the explicit classical curvature −1 metric facts.

The Lean 4.34.0 build of BoundedWanderingDomains, Submission and Challenge succeeded against Mathlib
5ed2965256430c3649e86755f9576b54eca72435. The build log records all jobs, including cached dependencies. Challenge has two intentional proof holes.
The Solution and all supporting proof modules under BoundedWanderingDomains/ have none.

The final two theorem axiom reports and the auxiliary bridge, covering, filling and planar-topology reports
use only propext, Classical.choice and Quot.sound. These reports cover
transitive proof dependencies.

The audit also covers Schottky confinement, the trapped-disc bridge, local
power-coordinate injectivity, eventual injectivity on shrinking discs, and
the assembled bounded-point-orbit theorem, as well as the area contradiction.

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
