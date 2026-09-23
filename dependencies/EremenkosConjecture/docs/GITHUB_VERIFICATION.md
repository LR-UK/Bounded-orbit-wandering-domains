# Optional GitHub verification

The workflow is manual: Actions → Verify Lean proofs → Run workflow. It does
not publish anything. GitHub-hosted checks for the new four-project arrangement
have not run; local verification records are in `verification/`.

First upload the prepared FunctionTheory repository privately under the same
owner as the other projects. Local builds already work with sibling directories
and do not require this upload.

For ComplexApproximation, configure `LEAN_DEPENDENCIES_TOKEN` as a repository
Actions secret with Contents: read access to FunctionTheory. For
EremenkosConjecture, give that secret read access to FunctionTheory,
ComplexApproximation, and ComplexDynamics. The ordinary repository token does
not provide access to the other private repositories. Never put credentials in
source files. FunctionTheory and ComplexDynamics need no cross-repository token.

Set each dependency-ref input to the reviewed commit ID. The `main` default is
convenient but does not pin a reproducible sibling snapshot. The workflow
checks out the directories beside each other, records their commits, installs
the pinned Lean toolchain, obtains Mathlib's cache, and builds and audits each
relevant library. Missing private credentials cause an explicit failure.

The workflows use pinned versions of [GitHub checkout](https://github.com/actions/checkout#checkout-multiple-repos-private)
and [lean-action](https://github.com/leanprover/lean-action). They have read-only
repository permissions. The local preparation was checked on Windows; the
manual GitHub workflows use Linux.
