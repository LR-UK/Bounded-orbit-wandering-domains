# GitHub update — version 1.4.3

Version 1.4.3 puts all supporting Lean files in subfolders, leaving only
`Challenge.lean` and `Solution.lean` at the top level. It preserves
all six completed paper theorems, includes the unchanged original entire-function
statement in the main comparison, and retains the import/duplication improvements from
version 1.4.1. See LAYOUT_UPDATE.md for renamed module entry points and checks.
The source archive, Git bundle and verification reports are prepared locally.
No remote has been changed.

To bring the history into an existing checkout, fetch the supplied bundle and
create a review branch:

```powershell
git fetch "C:/path/to/derived-set-unified-submission-github.bundle" local-paper-formalisation
git switch -c review-paper-formalisation FETCH_HEAD
lake build
python scripts/verify_paper.py --all
```

Keep any existing personal changes when integrating this branch. The bundle
preserves the recovered history and allows Git to detect conflicts with later
work. The source zip is a self-contained alternative for inspection; it includes
all local path dependencies and excludes build caches.

The GitHub workflow now verifies Challenge/Solution, validates metadata
and attribution, and runs the protected official Comparator with its bundled
independent kernels. See SUBMISSION.md for the corresponding Palomar setup.
