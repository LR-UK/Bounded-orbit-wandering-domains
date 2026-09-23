# ComplexApproximation formalisation project

The repository and Lake package have been renamed. The existing `Runge`
imports, namespace, and theorem names are preserved; `ComplexApproximation`
is the new umbrella import. Development of neighbourhood-holomorphic Arakelian
approximation resumed on 16 September 2026 at the maintainer's request and is
now proved, with the explicit bounded-exhaustion-holes hypothesis. Its
Cauchy–Pompeiu foundation and actual-domain interfaces are included in the
125-result audit, including horizontal unions and their union with a disk.
See `docs/ARAKELIAN_PLAN.md` for the proof route and scope.

Runge's approximation theorem is complete: arbitrary-compact rational
approximation, prescribed poles, and polynomial approximation with connected
complement. Preserve all three results and their recorded verification.

The user requests that searches for existing mathematics include other proof
assistants and EPFL's reformalization project (the Swiss project initially recalled
as being in Zurich): https://github.com/epfl-lara/jordan-curve-theorem.

## Proof integrity

- `Runge/` and `Runge.lean` contain only completed proofs. No `sorry`, `admit`,
  extra axioms, unchecked native evaluation, or weakened substitutes for the goal.
- `RungeTargets/` checks the original statements against completed proofs.
  The main library must never import this compatibility module.
- Keep hypotheses mathematically faithful. In particular, analytic on a compact
  set means analytic on an open neighbourhood, unless a different condition is
  explicitly stated.
- Check the axioms of headline results. Only Lean's standard axioms are allowed:
  `propext`, `Classical.choice`, `Quot.sound`.
- Preserve pinned dependencies. Keep `STATUS.md` honest about what was actually
  compiled and which obligations remain. A skeleton is not a verification.
- Consult `docs/PROOF_PLAN.md` before continuing after a context reset.

## Workflow

Run `lake build` for proved material; `lake build RungeTargets` checks the original
statements. Run `lake env lean scripts/Audit.lean` for the recorded axiom audit.
Advance a concrete mathematical lemma per iteration; use Mathlib results where
possible. Do not claim that the full theorem is proved until the exact target is
derived without unresolved dependencies.
