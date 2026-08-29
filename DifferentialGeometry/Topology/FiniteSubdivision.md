# FiniteSubdivision

## Result

`exists_strict_subdiv` compresses a finite monotone subdivision
`t : Fin (m + 1) → α` in a linear order.  It returns a strict subdivision
`s : Fin (k + 1) → α` and a strictly increasing map
`q : Fin k → Fin m` which enumerates exactly the positive original segments.

For every compressed segment `i`, the theorem records both endpoint
identities

```text
s i.castSucc = t (q i).castSucc
s i.succ     = t (q i).succ.
```

It also preserves the first and last node.  Thus a dependent local witness
indexed by the original segment, such as a chart or a `timeH1` object with
length `t (q i).succ - t (q i).castSucc`, transports to the compressed segment
without losing its source index.  If all original segments have zero length,
the output has `k = 0` and consists of the single common endpoint.

## Construction

The proof filters `Fin m` by strict positivity of the adjacent endpoint pair
and uses Mathlib's `Finset.orderEmbOfFin` to enumerate that finite set in the
original order.  Gaps between consecutive selected segments contain no strict
increase; monotonicity therefore makes every such gap constant.  This proves
the endpoint identities and strictness of the compressed nodes.  Value-only
`List.destutter` or `List.dedup` was not used as the public interface because
it does not retain the original segment carrying the chart or Sobolev witness.

## Verification and project position

Focused verification passed without warnings or placeholders.  The theorem is
generic order infrastructure and introduces no L-geometry assumptions or new
foundational class.

The finite repeated-node compression API is complete for its stated interface.
Its later L-specific transport and finite-node assembly are separate consumer
steps.  `exists_lMinimizer` and `redVolume_anti` remain 0%; the dedicated
L-geometry and P2 percentages are unchanged by this generic producer.
