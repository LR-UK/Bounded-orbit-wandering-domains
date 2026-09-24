# Prepared Palomar submissions — version 1.3.0

Use the same reviewed, publicly pushed immutable commit for either configuration.
No submission is made by these files.

| Field | Bounded-orbit update | Entire and local singular-limit results |
| --- | --- | --- |
| Repository | LR-UK/Bounded-orbit-wandering-domains | Same |
| Project directory | . | . |
| Comparator | comparator.json | comparator-singular-limits.json |
| Challenge module | Challenge | SingularLimitsChallenge |
| Solution module | Solution | SingularLimitsSolution |
| Metadata | formalization.yaml | formalization.yaml |
| Responsible maintainer | Lasse Rempe | Lasse Rempe |
| Commit | Full SHA of final publicly pushed snapshot | Same |
| Existing ID | Existing bounded-orbit ID, if assigned | New result; do not reuse that ID |

The first compares the strengthened local theorem without simple connectivity
and the entire bounded-point-orbit theorem. The second compares locally uniform
subsequential convergence to a derived spherical singular value on every entire
wandering component. The entire singular-limit theorem and both earlier bounded-orbit results
assume neither simple connectivity nor injectivity. The added local singular-limit
theorem assumes simple connectivity but derives the required injectivity; its
working domain has compact closure and f is analytic without constant germs
near that closure. See LOCAL_SINGULAR_LIMITS.md. The local statement still requires one point's
entire orbit to lie in a compact subset of its analytic iteration domain.

The two sphere area estimates are proved in NewResults and audited transitively.
They are not presented as standalone Challenge declarations in these submissions.

Before submitting, run the strict local verification and both protected Comparator
commands listed in README, or check the corresponding GitHub Actions results.
This environment cannot create the user namespace required by bubblewrap;
no official Comparator/independent-kernel pass is claimed locally.

The current requirements were checked at https://palomar-registry.org/how-to-submit
on 24 September 2026. Use https://submit.palomar-registry.org/ when ready and retain
the submission status link. The prepared archive is not a public Git commit until
its history is pushed. Do not overwrite, withdraw or resubmit the pending earlier
submission automatically.
