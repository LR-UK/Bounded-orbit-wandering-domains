# Applying the reorganised archive

## If the existing folder is already a GitHub checkout

Keep that checkout. You do not need to initialise Git again, reconnect the
remote, create a new GitHub repository or move the `.git` directory.
The separate extraction folder is just a staging area for this update.

1. Back up the existing project, or commit your current work locally. Preserve
   any personal edits, particularly to `formalization.yaml`.
2. Extract the archive somewhere else. Open the extracted
   `bounded-wandering-palomar` folder: this contains the repository files.
3. In the existing checkout, move the old supporting `.lean` files from the
   root into a backup folder **outside** the checkout. Leave `Challenge.lean`
   and `Solution.lean` in place. The exact 50 moved filenames are listed in the
   extracted `verification/moved-sources.json`; only remove those old root
   copies. Their replacements are under `BoundedWanderingDomains/`.
4. Copy the **contents** of the extracted `bounded-wandering-palomar` folder
   into the existing checkout, replacing matching files. Do not create an
   extra nested `bounded-wandering-palomar` folder. Keep the existing `.git`
   directory and `.lake` cache. Merge any personal metadata edits into the
   supplied metadata rather than losing them.
5. Open the existing checkout in VS Code. From its root run:

   ```sh
   lake build Submission Challenge
   ```

   Supporting modules need rebuilding because their module names changed;
   the existing dependency cache can still be reused. The two `sorry`
   warnings in Challenge are intentional. Solution has no proof holes.
6. Review the changes in GitHub Desktop or VS Code Source Control. The old
   supporting files should appear as moves/renames or as corresponding
   deletions and additions. Commit and push in the usual way. Your existing
   repository history and GitHub connection remain intact.

For the full local declaration and axiom audit, additionally run:

```sh
python scripts/verify_submission.py
```

Use `python3` instead of `python` where that is your Python command.
Official Palomar Comparator and NanoDa remain separate verification steps.

## If the project has not yet been connected to GitHub

Use the newly extracted `bounded-wandering-palomar` folder directly as the
project root. Build there, then initialise/publish that folder as planned.
There is no previous Git checkout to preserve in this case.

## Scope of this update

Version 0.12 changes the entire theorem from a bounded union of Fatou
components to a bounded orbit for one point in the initial component. The
main new modules are `PointOrbitBridge.lean`, `LocalDiscInjectivity.lean`
and `BoundedPointWandering.lean`; the area proof uses `EventualCompactDiscs.lean`
and `ShrinkingChartDiscs.lean` added in the preceding update. There are now
55 supporting modules. The local Challenge theorem retains its hypotheses.

Update the full source tree, `Challenge.lean`, `Solution.lean`, the umbrella
import, metadata and verification files together. If the earlier move to
`BoundedWanderingDomains/` has already been applied, skip step 3 above.
Curvature −1, co-authors, licences and the agreed project description are
preserved. Review the strengthened Challenge statement before submitting.
