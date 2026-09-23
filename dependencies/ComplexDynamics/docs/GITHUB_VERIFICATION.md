# GitHub verification

The prepared workflow is manual: open **Actions → Verify Lean proofs → Run
workflow** after uploading. It does not publish releases, documentation,
packages, or source elsewhere. Initial local checks are recorded in
`verification/`; GitHub-hosted checks have not yet run.

The workflow uses pinned versions of `actions/checkout` and
`leanprover/lean-action`, installs the pinned Lean toolchain, obtains Mathlib's
cache, and invokes the same `scripts/verify.py` used locally. It uses read-only
repository permissions. GitHub-hosted verification is initially on Linux;
the preparation was verified locally on Windows.

For EremenkosConjecture only, create a repository Actions secret called
`LEAN_DEPENDENCIES_TOKEN` with read access to the private ComplexApproximation
and ComplexDynamics repositories (a fine-grained token with Contents: read).
The ordinary `GITHUB_TOKEN` cannot read other private repositories. The
workflow assumes all three have the same owner and the documented names.
Its two dependency-ref inputs should be set to the commit IDs being reviewed;
`main` is convenient for development but does not pin a reproducible snapshot.
Missing credentials cause an explicit failure, not a successful skipped audit.

This secret is configured in GitHub Settings, never in a source file or an
issue. It is not needed for local builds from authenticated sibling clones.
After the review workflow is established, maintainers can enable push and
pull-request triggers. No cross-repository token is needed for the other two
projects.

Sources checked for preparation:
- [GitHub checkout: private repositories](https://github.com/actions/checkout#checkout-multiple-repos-private)
- [Lean's standard action](https://github.com/leanprover/lean-action)
