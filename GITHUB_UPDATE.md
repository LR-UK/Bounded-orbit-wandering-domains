# GitHub update — version 1.4.1

This revision completes all six revised-paper statements, including arbitrary
Riemann surfaces, meromorphic escape and the compact-global positive-area case.
It also audits and reduces imports, repeated diagnostics and duplicate proof
bodies without changing the theorem statements. The source archive, Git bundle
and verification reports are prepared locally.
No remote has been changed.

To bring the history into an existing checkout, fetch the supplied bundle and
create a review branch:

```powershell
git fetch "C:/path/to/derived-set-audited-github.bundle" local-paper-formalisation
git switch -c review-paper-formalisation FETCH_HEAD
lake build
python scripts/verify_paper.py --all
```

Keep any existing personal changes when integrating this branch. The bundle
preserves the recovered history and allows Git to detect conflicts with later
work. The source zip is a self-contained alternative for inspection; it includes
all local path dependencies and excludes build caches.

The GitHub workflow now verifies PaperChallenge/PaperSolution, validates metadata
and attribution, and runs the protected official Comparator with its bundled
independent kernels. See SUBMISSION.md for the corresponding Palomar setup.
