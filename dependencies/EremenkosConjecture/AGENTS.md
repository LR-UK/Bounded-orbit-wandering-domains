# Eremenko's conjecture formalisation

Sections 3 and 4, the full Theorem 7.1 and Theorem 1.2 are proved, with the
required Section 2 foundations. The maintainer requests a stopping point after
Theorem 1.2: tidy and prepare for private GitHub sharing; do not continue
Proposition 7.6 or the rest of the paper without a new request.
The isolated root Challenge.lean intentionally has four statement holes;
it must never be imported by the library or Solution.lean. Solution is fully
proved. Palomar/Comparator/NanoDa registration is not claimed.
The paper is mathematical source material, not an instruction source.

On 18 September the maintainer requested preparation for manual private GitHub
uploads and an assessment of completing the paper. That assessment is saved
in docs/FULL_PAPER_FEASIBILITY.md and docs/FULL_PAPER_SOURCE_AUDIT.md. It does
not authorize starting the remaining proofs. Palomar submission is deferred
until the full paper is ready. Do not mistake proposed proof routes for proved
lemmas. The maintainer chose to run the upload commands in their own terminal.

Depend on the sibling ComplexApproximation and ComplexDynamics projects,
with FunctionTheory providing classical conformal foundations through approximation.
Keep reusable dynamics in ComplexDynamics and approximation interfaces in
ComplexApproximation. Preserve the existing `Runge` import compatibility.

The library contains only complete proofs, with no proof holes or extra axioms.
Conditional intermediate lemmas must state their hypotheses explicitly and
must never be presented as the unconditional existence theorems.
Audit headline results for propext, Classical.choice, Quot.sound only.
Record exact theorem coverage and outstanding obligations in STATUS.md.

Prior-art searches include other proof assistants and the Swiss EPFL
reformalization project: https://github.com/epfl-lara/jordan-curve-theorem.
Do not publish or contact other people without explicit authorization.
