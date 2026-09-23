# Deferred neighbourhood characterization

The maintainer suggested Fournodavlos's characterization on 17 September
2026. [Theorem 1.3, *On a characterization of Arakelian sets*](https://arxiv.org/pdf/1107.0393)
characterizes closed planar Arakelian sets by a basis of open neighbourhoods
whose complements in the sphere are connected. This is recorded for future
work and is not being added as a dependency of the Theorem 1.2 construction.

The paper's convention permits a disconnected open neighbourhood: its
components are simply connected. A future Lean statement must preserve this
convention; requiring the neighbourhood itself to be connected would fail
already for two points with disjoint small neighbourhoods.

The existing library proves the concrete approximation geometry needed by
the current application. The general characterization is not yet formalised.
