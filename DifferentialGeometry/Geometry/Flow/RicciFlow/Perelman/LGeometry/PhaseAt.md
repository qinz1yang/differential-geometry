# `PhaseAt.lean`

## Result

`exists_lPhaseSol_at` constructs a local solution of the regularized L-phase
ODE through an arbitrary chart-interior state `z0` at an arbitrary square-root
base time `s0`, provided `T - s0^2` is a regular flow time.  It returns a
positive radius, a phase path with `z s0 = z0`, and the pointwise derivative
equation on `Ioo (s0 - epsilon) (s0 + epsilon)`.

## Construction

The proof autonomizes the original nonautonomous phase field as

```text
(s, z) |-> (1, lPhaseField S T x0 s z)
```

and applies the native manifold integral-curve existence theorem directly at
state `(s0, z0)` and parameter time `s0`.  The first component has derivative
one, so a local constant-derivative argument identifies it with the actual
parameter throughout a symmetric interval about `s0`.  Projecting the second
component then gives the required phase solution.

This is not obtained by translating the zero-time theorem: the occurrence of
`T - s^2` in the phase field is left unchanged.  No solution, Euler equation,
extra regularity package, reference import, new class, or frontier wrapper is
assumed.

## Verification and progress

Focused verification passed without warnings or placeholders.  The arbitrary-
base-time phase existence producer is 100% complete.  The terminal
`exists_lMinimizer` and `redVolume_anti` remain 0%; dedicated L-geometry
machinery is approximately 98%, reused generic infrastructure is 100%, P2
remains below 1%, and the whole Poincare program remains approximately 3--5%.
