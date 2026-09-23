# Reviewing the statements

For the whole proved library, start with [MAIN_RESULTS.md](../MAIN_RESULTS.md)
and the [proved gallery](../EremenkosConjecture/MainTheorems.lean). The gallery
is included in the ordinary build and axiom audit.

For the selected counterexamples and Theorem 1.2, use
[Challenge.lean](../Challenge.lean). It imports only Mathlib and displays all
needed dynamics definitions. `IsConnected` includes nonemptiness; full means
connected plane complement. Check connected components separately from path
components, and review the normality and fast-escape definitions.

[Solution.lean](../Solution.lean) gives the corresponding proved statements.
The local build and axiom audit include Solution. Challenge's four deliberate
holes are isolated from all proof dependencies. This is a prepared comparison
interface; Comparator/NanoDa and Palomar review have not been run.

[PALOMAR.md](PALOMAR.md) records the selected scope, public-dependency and
independent-verification steps still needed for an actual submission. The
[proof map](THEOREM12_PLAN.md) explains the complete Theorem 1.2 construction.
