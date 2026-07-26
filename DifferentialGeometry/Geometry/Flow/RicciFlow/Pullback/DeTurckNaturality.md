# DeTurckNaturality

## Source status

`connDiff_push` is source-written and awaits focused elaboration after the
current named export.  No placeholder, axiom, opaque producer, new class,
instance, or notation is present.

## Result

For a diffeomorphism `Phi`, the theorem proves

```text
dPhi (connDiff g (Phi*h) u v)
  = connDiff ((Phi^-1)*g) h (dPhi u) (dPhi v).
```

The proof is not a coordinate assertion.  It chooses a smooth extension of
`u`, applies the existing pointwise Levi-Civita naturality theorem once to
each endpoint, and subtracts.  Smoothness of the pushed-forward extension is
supplied by the canonical fixed-time pushforward theorem.

## DeTurck trace bridge

`deTurckVF_push` takes the `g`-trace of `connDiff_push` and proves the
naturality formula

```text
Phi_* (deTurckVF g (Phi*h))
  = deTurckVF ((Phi^-1)*g) h.
```

`push_deTurckVF` exports the same fact at an arbitrary target point, after
using surjectivity of `Phi`.  This is the exact vector-field rewrite consumed
by the inverse harmonic-map gauge.

The proof pushes the canonical source orthonormal frame through `dPhi`, checks
that it is orthonormal for `(Phi^-1)*g` using `pullbackMetric_inner` and the
two differential cancellation identities, and applies `connDiff_push` term by
term.  It consumes the small public arbitrary-orthonormal-trace wrapper
`deTurckVF_eq_trace`; that wrapper still has to be exported from
`DeTurckVFConnDiffVariation` after the in-progress named build releases the
shared Lean dependency.

This remains gauge machinery; harmonic-map heat-flow existence and the exact
`ricci_flow_forward_unique` endpoint remain 0%.
