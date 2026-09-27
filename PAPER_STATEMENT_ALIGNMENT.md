# Revised-paper statement alignment

All six targets are proved. The source is the author's
`handoff/reference/no-bounded-WD-2.tex`, supplied 25 September 2026.
Challenge imports only Mathlib; Solution imports proved source and
does not import Challenge. Local comparison checks six theorem types and
36 supporting declarations, including the local-map structure and its constructor.

- **1.2 entire:** a transcendental entire function, actual Fatou components,
  forward containment and pairwise distinct components give a strictly increasing
  subsequence converging locally uniformly to infinity on the initial component.
- **1.2 meromorphic:** the same conclusion for non-rational meromorphic maps in
  normal form, with Fatou neighbourhoods avoiding poles and prepoles. Poles are
  allowed; their representative values are not used by admissible iterates.
- **1.3(1):** no marked orbit in an actual wandering normality component is
  contained in a compact subset of the local map's open source: for each such
  compact set K, some iterate lies outside K. This does not assert eventual
  escape from every compact set. No simple connectivity or injectivity is assumed.
- **1.3(2):** a measurable positive-chart-area set in `trapped \ omega`, with
  pairwise disjoint forward images and injectivity on its forward saturation,
  has saturation not contained in any compact subset of the source. This now
  includes compact global sphere and torus maps and all other surface cases.
- **1.4:** an entire wandering marked orbit has a subsequence converging to a
  derived spherical singular value, allowing infinity.
- **1.5:** if all normality components met by a wandering component orbit are
  simply connected, a marked orbit has a subsequence escaping every compact
  subset of the ambient surface or converging to a derived singular value of
  the actual local map. No auxiliary restricted-map singular set is substituted.

The challenge statements have not been weakened. The final comparison work
aligned the meromorphic definitions' canonical complex instances and named
rationality/Claim wrappers, so the independent declarations match exactly.
The LocalMap structure is checked transitively by Comparator; it is not listed
as a definition-hole target, because it is an inductive structure.
