# No bounded-orbit wandering domains

We prove that transcendental entire functions do not have bounded-orbit wandering domains.

This answers a major open question in the field. The proof builds upon Zihao Ye's new proof of Sullivan's No Wandering Domains theorem, and was obtained with assistance by generative AI. We also formalise a stronger theorem, which shows that locally defined holomorphic functions do not have orbits of simply connected wandering domains on which the iterates are univalent.

This is an unconditional formalisation, prepared with the use of Generative AI for submission to Palomar. In order to achieve an unconditional formalisation, a number of classical results had to be newly (auto-)formalised, including results concerning the hyperbolic metric for a finitely punctured sphere, and its area.  

Both public results are in [Solution.lean](Solution.lean). Their independent
statements are in [Challenge.lean](Challenge.lean), using only Mathlib imports. The statements of the challenge theorems have been checked by the authors.

## Exact statements

1. **Entire functions.** A pairwise disjoint forward orbit of actual Fatou
   components cannot contain a point with bounded forward orbit. Boundedness
   of the union of the components is not assumed. Simple connectivity and
   eventual injectivity are derived for auxiliary trapped components.
2. **Local functions.** The function is analytic near the compact closure of
   an open set V and has no constant germ there. The relevant simply connected
   trapped components lie in one compact subset of V and satisfy eventual
   injectivity on each fixed intrinsic disc. Such a component orbit cannot
   be pairwise disjoint. These dynamical hypotheses remain explicit.


The definition of the Fatou set, using normality, uses subsequential locally uniform convergence of sphere-valued iterates into the one-point compactification of ℂ. 
Transcendental entire means complex differentiability everywhere and inequality to every complex polynomial.

The eight short supporting definitions are included in the comparison.

## Build and verification

The toolchain is `leanprover/lean4:v4.35.0-rc2`. Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. From this directory:

```sh
python3 scripts/fetch_cache.py
python3 scripts/verify_submission.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
./scripts/verify-comparator.sh
```

The verification script builds with bounded parallelism, then runs the full
Lake target check. The Python metadata check requires PyYAML. The final command requires Linux
with working unprivileged user namespaces and bubblewrap; it uses the bundled
Palomar Comparator, NanoDa and con-ron without weakening their checks.
See [VERIFICATION.md](VERIFICATION.md) for the actual results and limitations.
The two `sorry`s in Challenge are intentional statement placeholders; Solution
does not import Challenge. No proof holes or extra axioms are permitted in
Solution's dependency closure.

## Organisation and provenance

- `BoundedWanderingDomains/`: analytic, dynamical and area arguments.
- `RiemannDynamics/`: attributed uniformisation port and the final bridge.
- `RMT4/`: attributed supporting analytic source.
- `dependencies/`: four contained source dependencies and vendored Schoenflies.
- `verification/`: reproducible audit scripts' outputs and supporting exporters.
- `history/`: clearly separated earlier-stage documents and logs.

There are no sibling-project dependencies. Mathlib and its pinned Git
dependencies are fetched by Lake. Build caches are not distributed.
The mathematical proof outline is in [BOUNDED_POINT_PROOF.md](BOUNDED_POINT_PROOF.md).
The new unconditional connection is in
`RiemannDynamics/BoundedWanderingSolution.lean`.

Mathematical direction: Lasse Rempe. Paper authors: Nikolai Prochorov,
Lasse Rempe and James Waterman. AI-assisted formalisation: OpenAI ChatGPT/Codex.
Third-party proofs retain their own authorship and licences; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and `formalization.yaml`.
The manuscript is being prepared separately. No independent human review or
Palomar acceptance is claimed.

## Licences

The original project development is distributed under the Apache License,
Version 2.0; see the complete text in [LICENSE](LICENSE).
The `project.license` value in `formalization.yaml` is `Apache-2.0`.

Included third-party source retains its own copyright, authorship and licence
notices. [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) identifies the sources,
adaptations and bundled licence texts. In particular, the Palomar metadata
validator retains its [MIT licence](verification/palomar-contract/LICENSE).
Keep these licence files, source notices and adaptation records with any
redistribution of the included source.

## Submission

Use [SUBMISSION.md](SUBMISSION.md) for the prepared form values and remaining
publication step. The current submission form is
https://submit.palomar-registry.org/ . A public repository and the full immutable
commit SHA are required. This archive has not been published or submitted.
