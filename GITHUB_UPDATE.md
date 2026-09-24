# GitHub update package — version 1.3.0

The package contains complete source, a Git bundle with the recovered history,
a patch relative to the previously recovered public baseline, verification
reports and release notes. The companion RESTORE.txt identifies the exact commit.
No remote branch has been pushed and no Palomar submission has been made.

## Review in your existing Windows checkout

Keep any personal uncommitted changes safe before switching branches. From the
existing repository in PowerShell, substitute the actual extracted bundle path:

```powershell
git status
git fetch "C:/path/to/formalisation-history.bundle" formalise-spherical-singular-limits-recovered
git switch -c review-formalisation-1.3 FETCH_HEAD
lake build
python scripts/verify_submission.py
python scripts/verify_metadata.py
python scripts/audit_attribution.py
```

This creates a review branch with the full history. It does not overwrite main.
If main has subsequently advanced, merge the review branch into your current
branch and retain your later edits; do not reset main to the archived commit.
The Git bundle is preferable to copying files because it preserves history and
allows Git to detect conflicting edits.

When ready, push the review branch and open a pull request, or merge it locally
into main after review and push. The included GitHub Actions workflow checks
both independent Challenge configurations with Comparator and its bundled
independent kernels. Linux with working bubblewrap user namespaces is required
for those checks; the Python/Lake checks also work from Windows with Lean installed.

## Included changes

- All three new sphere-area and entire singular-limit results are proved.
- The entire theorem gives a constant locally uniform limit function on the
  original wandering component, not just accumulation of image domains.
- Simple connectivity is removed from the local bounded-point-orbit theorem.
- The Eremenko–Lyubich tract dependency retains its source attribution and licence.
- Deprecated names and unused tactics in the active dependency closure are fixed.
- Both Challenge configurations are independent of the proved source and use
  only Mathlib imports. Metadata, CI, cache traversal and audits include the new work.

A bounded local derived-singular-set theorem is included with simple connectivity
explicit and injectivity derived. See LOCAL_SINGULAR_LIMITS.md. No meromorphic
extension is claimed.
The two area theorems remain supporting results for registry purposes.
See SUBMISSION.md for the two possible later Palomar submissions.
