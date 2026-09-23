# Reviewing the public statements

Start with `MAIN_RESULTS.md` and the project's `MainTheorems.lean` file.
Each displayed theorem has an explicit type and a one-line proof referencing
the substantive development. The normal library build and axiom audit include
these declarations. Definitions and nonstandard conventions are linked in the
mathematical guide; reviewing them is part of reviewing each statement.

This supplies a small, checked interface for private mathematical review.
It is not an independent formal-fidelity check: the gallery imports completed
proof modules. No Palomar acceptance or Comparator verification is claimed.

The [official Palomar template](https://github.com/PalomarRegistry/PalomarTemplate)
currently separates a `Challenge.lean` statement surface from `Solution.lean`
and uses Comparator plus provenance metadata. A later submission should select
the advertised results, isolate the required definitions, prepare that exact
interface and metadata, and run the required independent checks at a fixed
reviewed revision. This has not yet been done. Private review can proceed
using the fully proved gallery supplied here.
