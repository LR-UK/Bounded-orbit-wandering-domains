# Results outside this conditional submission

The intended bounded-point-orbit statement is now proved. Its hypothesis is

```lean
Bornology.IsBounded (Set.range (fun n : ℕ => (f^[n]) z))
```

for a point z in the initial Fatou component. The earlier bounded-union
hypothesis has been removed. Simple connectivity and eventual disc
injectivity are derived through auxiliary trapped components; neither is an
assumption of the entire-function Challenge theorem.

Remaining work:

- Construct the metric family satisfying `ClassicalHyperbolicMetrics`.
  This remains an explicit classical hypothesis of both final theorems.
- Weaken the hypotheses of the local Challenge theorem, which currently
  retains compact containment of the whole trapped-component orbit, simple
  connectivity and eventual intrinsic-disc injectivity.
- Prove the derived-singular-set statement.
- Generalise to meromorphic functions or compact Riemann surfaces.

The remaining items are not asserted by this submission.
