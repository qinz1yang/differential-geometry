# ActionStrict

## Role

`exists_lStrict` is the L-specific consumer of the generic
`exists_strict_subdiv` theorem.  It removes zero-length pieces from a finite
monotone chart-`H¹` realization while retaining a strictly increasing map `q`
back to the original positive pieces.

The result transports the original chart centers and dependent `timeH1`
witnesses to the strict subdivision.  It exposes exact first/last-node and
per-piece endpoint equations, and it reproves the chart-source and coordinate
representation facts in the compressed indexing.  Thus downstream finite-node
and two-piece-window consumers can use the strict realization without
reconstructing which original witness belongs to a compressed segment.

Only the dependent `timeH1` value is transported across the proved segment-
length equality.  The public interface does not expose an `Eq.rec` term and
does not replace the original-index witness `q` by value-only node
deduplication.

## Verification and progress

Focused verification and the targeted module refresh passed without warnings
or placeholders.  The theorem
uses only the topological chart data and complete inner-product model needed by
the stated `timeH1` witnesses; it introduces no compactness, Ricci-flow,
finite-dimensionality, or manifold-smoothness assumption.

This theorem is a realization transport producer, not the terminal minimizer
or reduced-volume theorem.  `exists_lMinimizer` and `redVolume_anti` remain
0%.  The generic strict-subdivision infrastructure and this L-specific
realization transport are each 100%.  Dedicated finite-node assembly is about
96--98%, while dedicated L-geometry remains about 92--94%; P2 remains below
1% and the whole Poincare program remains about 3--5%.
