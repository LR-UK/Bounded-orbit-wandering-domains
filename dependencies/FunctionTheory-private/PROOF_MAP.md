# Proof map

[Main results](MAIN_RESULTS.md) · [Complete module index](docs/MODULE_INDEX.md)

```mermaid
flowchart TD
  M[Mathlib] --> T[Tau Ceti: attributed classical analysis]
  T --> R[Riemann mapping and normalized uniqueness]
  T --> N[Montel and Hurwitz]
  T --> S[Schwarz reflection]
  R --> A[Actual-domain interface]
  M --> H[Holomorphic functions on their domains]
  H --> A
  N --> K[KernelSubsequence]
  I[KernelImage: nondegenerate limit lies in kernel] --> K
  L[InverseLimits: limits remain inverse] --> K
  R --> D[RiemannInverseBounds: Cauchy estimate]
  K --> B[BoundedKernel]
  D --> B
  B --> C[KernelConvergence: full direct and inverse sequences]
  R --> C
  C --> E[KernelSeparation: compact avoidance]
  M --> IB[ImaginaryBounds: local bounds from a halfplane]
  IB --> UB[HalfPlaneKernel: unbounded-domain convergence]
  K --> UB
  C --> UB
```

The last compact-avoidance statement is a general convergence lemma, also
usable independently. The diagram describes the mathematical proof route;
the generated [JSON graph](docs/import-graph.json) records exact direct imports.
Tau Ceti's 138 source modules are listed separately in its
[upstream manifest](third_party/TauCeti/UPSTREAM.json).

## Relationship between projects

```mermaid
flowchart LR
  Mathlib --> FunctionTheory
  Mathlib --> ComplexDynamics
  FunctionTheory --> ComplexApproximation
  ComplexApproximation --> EremenkosConjecture
  ComplexDynamics --> EremenkosConjecture
```

The Eremenko Theorem 7.1 proof uses explicit maps and approximation. Importing
the conformal foundations into an umbrella module does not make them necessary
dependencies of that theorem's mathematical argument. The general-continuum
Theorem 1.2, now proved in EremenkosConjecture, applies the additional conformal machinery.

## Strip-end estimates

```mermaid
flowchart LR
  R[Tau Ceti real-axis reflection] --> I[ImaginaryReflection: quarter-turn]
  I --> J[ReflectionInjectivity: simple zero and positive derivative]
  H[Boundary continuity, axis values and open-half injectivity: hypotheses] --> J
  J --> A[StripEndAsymptotics]
  A --> E[StripEndCoordinates: exponential identity and logarithm branch]
  X[Exponential identity and strip bounds: hypotheses] --> E
  E --> B[StripBounds: derivative bounds on closed insets]
  C[Injective holomorphic neighbourhood: hypothesis] --> B
  B --> U[StripUniformity and application iterate control]
```

The geometric application must supply the boundary continuity, axis values,
halfplane mapping property and exponential identity used by these analytic
results. The general geometric assertion of Lemma 7.2 is not yet completed.

## Whole-set escape from boundary convergence

```mermaid
flowchart LR
  H[Inverse convergence on the CLOSED strip: hypothesis] --> K[KernelSeparation: compact avoidance]
  K --> E[StripKernelEscape: uniform real-part escape]
  R[Compact closed rectangles] --> E
```

This reduction identifies the boundary-convergence input still missing in the
general-continuum application. Open-strip convergence alone is insufficient.

## Geometric boundary normalization: checked

```mermaid
flowchart TD
  C[Tau Ceti Caratheodory continuity] --> J[JordanBoundary: interior and boundary normalization]
  R[ReflectionInjectivity] --> S[StraightBoundaryExtension]
  J --> S
  Y[CayleyCoordinates] --> S
  S --> I[StraightBoundaryInverse: analytic positive-derivative coordinate]
  I --> M[StripEndMap: map, both asymptotics and right-end limit]
  E[StripEndCoordinates and StripCoordinates] --> M
  G[Simply connected domain, left bound, full right tail, Jordan exponential image] --> M
  M --> A[Eremenko DecoratedStripControl: uniform iterate control]
```

The geometric assumptions in G are explicit. This route supplies the
reflection data previously left as analytic inputs. The decorated-domain
construction and uniform whole-continuum estimate still remain open.

`StripEndMap` also feeds into
[StripProper](FunctionTheory/Conformal/StripProper.lean): compact left
truncations plus the translation asymptotic give bounded displacement, hence
properness on a closed inset and a closed image. This supplies a topological
property needed when transporting the unbounded approximation sets.

[The compact-subset loop criterion](FunctionTheory/Topology/SimpleConnectivity.lean)
is independent of the conformal-map development. The application combines it
with filled compacta and its attributed Jordan–Schoenflies dependency.

The boundary-injectivity route is now included:
`Topology/BoundaryApproach` supplies chart transfer, while the unchanged public
`Inverse/BoundaryCluster` theorem supplies injectivity. The application combines
these with Schoenflies to obtain Carathéodory's closure homeomorphism.

## Convergence across a shared boundary arc

```mermaid
flowchart LR
  R[Public Rouche theorem] --> D[Image disk inclusion]
  D --> L[Injectivity: lower bound on outer annulus]
  L --> B[Bounded circle-reflected family]
  S[Public circle Schwarz reflection] --> B
  V[Public Vitali and Mathlib identity theorem] --> C[Convergence on symmetric collar]
  B --> C
  N[Constructed symmetric neighbourhoods] --> C
  C --> A[SharedArcConvergence: closed disk away from exceptional points]
```

The shared-arc condition must be proved for the varying domains in the
application. The theorem does not infer it from open-disk convergence alone.

## The separating quadrilateral route

```mermaid
flowchart TD
  A[Public length-area and area formula] --> B[Uniform annulus: choose inner radius before maps]
  B --> C[Some right semicircle has short image]
  K[Interior kernel convergence] --> R[Control on compact radial reference segment]
  R --> D[Crosscut image lies near minus one]
  C --> D
  G[Shrinking gate on attachment line] --> S[Continuous scalar barrier]
  D --> T[Connectedness traps the whole separated side in a cap]
  S --> T
  T --> L[Disk-to-strip coordinate: Re at most log delta]
  L --> E[Uniform leftward escape of the whole attached side]
```

The source half-annulus is a quadrilateral of large modulus. Length-area
provides precisely its short-crosscut consequence. The theorem consumes
explicit domain and kernel hypotheses; the paper-specific construction is
still an application obligation.

## Local Caratheodory at a slit tip

```mermaid
flowchart TD
  A[Uniform length-area] --> C[Short circular crosscut]
  P[Properness: endpoint cluster values lie on the unit circle] --> D[Crosscut image in a small boundary cap]
  C --> D
  D --> B[Connected disk outside the cap]
  B --> O[Small oscillation on the entire local approach region]
  O --> S[Singleton boundary cluster set]
  S --> L[Unique unit-circle boundary limit]
  G[Explicit slit-plane geometry] --> L
```

Only local geometry at the selected boundary point is used. The exterior-map
application and its checked compact enclosure construction are described in the sibling
[application note](../EremenkosConjecture/docs/LOCAL_CARATHEODORY.md).


## Riemann mapping on the sphere

```mermaid
flowchart TD
  Ray[Ray: attributed two-chart sphere atlas] --> Coordinates[Holomorphic sphere coordinates]
  Coordinates --> Omitted[Choose an omitted point as infinity]
  Two[Two omitted points] --> Proper[Coordinate domain is proper in the plane]
  Omitted --> Proper
  SC[Simple connectivity preserved by the coordinate homeomorphism] --> Plane[Tau Ceti plane Riemann mapping]
  Proper --> Plane
  Plane --> Sphere[Biholomorphism of the actual spherical domain with the disk]
  Coordinates --> Sphere
```

The sphere coordinate is explicit, so this does not require a general
uniformization theorem for Riemann surfaces. See the
[exact statement](docs/RIEMANN_SPHERE.md).


## Local boundary geometry and the actual kernel

```mermaid
flowchart TD
  L[Local straight-boundary continuity] --> R[Positive conformal reflection]
  R --> S[Strip map and both exponential end estimates]
  F[Filled attachment domains] --> G[Narrow gate and full straight tail]
  G --> K[Exact right-halfstrip kernel]
  K --> C[Interior kernel convergence]
  U[Uniform boundary caps] --> N[Right-end normalization convergence: OPEN]
  C --> N
  S --> I[Uniform inset and derivative control]
  N --> A[Adapted Arakelian induction: OPEN]
  I --> A
```

The compact Jordan enclosure through the free attached-segment tip is also
proved in every prescribed neighbourhood. The new strip-map theorem does not
require the exponential image to have Jordan boundary.
