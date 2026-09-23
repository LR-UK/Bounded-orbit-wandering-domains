# Prepared Palomar submission

## Form values

| Field | Prepared value |
| --- | --- |
| Title | Absence of bounded-orbit wandering domains |
| Project directory | `.` (repository root) |
| Challenge module | `Challenge` |
| Solution module | `Solution` |
| Comparator configuration | `comparator.json` |
| Metadata | `formalization.yaml` |
| Responsible maintainer | Lasse Rempe |
| Repository | Supply the public GitHub repository containing this package |
| Commit | Supply its full immutable 40-character commit SHA |

Compared theorems:

- `BoundedWanderingDomains.no_local_bounded_wandering_domains`
- `BoundedWanderingDomains.no_bounded_wandering_domains_transcendental_entire`

The accompanying configuration compares seven public definitions and permits
only `propext`, `Classical.choice` and `Quot.sound`.

## Submission description

We formalise the absence of wandering Fatou components containing a point
with bounded forward orbit for transcendental entire functions. The result
requires boundedness only of one point orbit. We also prove a local absence
theorem for simply connected trapped components when only one point orbit is
compactly contained in the iteration domain. Whole-component compact containment
and eventual injectivity are no longer hypotheses. This local statement covers
plane-valued maps analytic near compact closure(V). The former classical hyperbolic metric
assumption is now proved: the submission includes disc-covering existence,
the curvature −1 metric and the total-area formula. The independently stated
Challenge and the proved Solution have the same two public theorem signatures
and the same seven supporting definitions.

## Publish and submit

1. Preserve the earlier conditional and version 1.0.0 commits/tags. Put the contents of this
   package at the root of the intended public GitHub repository, including
   contained dependencies, licences, metadata and `.github/workflows/ci.yml`.
   Use a new commit for this stronger local theorem (project version 1.1.0). Exclude `.lake` caches.
2. Run the included CI. Check that the official Comparator and its independent
   kernels finish successfully, as well as the build and metadata checks.
   The local execution status and any environment limitation are documented
   in VERIFICATION.md; a local diagnostic is not a substitute for Comparator.
3. Copy the full commit SHA (`git rev-parse HEAD`) and repository URL into
   https://submit.palomar-registry.org/ with the root-directory values above.
   If the earlier result has been registered, enter its existing Palomar ID
   to request a new version. Each version has its own immutable commit.
   The submitting author should supply any authorisation/account fields from
   their own account. No account details or public commit have been invented.
4. Review the preview and submit. Registry validation and human review remain
   separate from the preparation of this archive.

Prepared against PalomarSubmission commit
`e48a86d0495356b5131a92c9406aa6e27cf99e56` and PalomarTemplate commit
`cb5c79b69a740d2dc299071fc35994627050d77a`, inspected 23 September 2026.
The current verifier requires Lean 4.35.0-rc2 or newer; this package pins that
release and its matching Mathlib tag.
