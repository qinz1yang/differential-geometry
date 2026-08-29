# ShortMinimizing

## Result

`lRegInit_shrink` is the shrinking-terminal counterpart of `lRegInit_var`.
For regularized L-rays with square-root terminal times `B n > 0` contained in
one compact regular slab, an action estimate

`lRegAction ... 0 (B n) <= A * B n`

uniformly bounds their initial tangents.  The proof uses compact-slab scalar,
gradient, and Ricci bounds, then applies the explicit `lRegInit_bdd` estimate
with `eps = R = B n`; cancelling the positive factor `B n` leaves a bound
independent of `n`.

## Frontier

This closes the bounded-initial-vector part of the short-time minimizing-ray
argument.  The target still missing is

```lean
theorem lInj_eventually
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    ∀ᶠ tau in 𝒩[>] (0 : Real), Z ∈ lInjDomain S T x tau
```

The smallest missing native geometric producer is the bounded-set endpoint
injectivity statement

```lean
∀ R, ∃ eps > 0, ∀ b, 0 < b → b < eps →
  Set.InjOn (fun W ↦ lRegCurve S T x W b) (Metric.closedBall 0 R).
```

Its expected proof is to use one chart at `x`, divide the chart displacement
by `b`, and prove uniform convergence on the compact tangent ball to `2 * W`,
together with uniform convergence of its derivative to `2 • 1`.  The existing
`lRegCurve_smoothAt`, `lRegCurve_zero`, and `lRegCurve_vel_zero` give the
pointwise joint smoothness and zero-time derivative data, but no exported API
currently packages the removable quotient continuously on a compact parameter
set or turns the uniform derivative estimate into the displayed injectivity.

Once this producer exists, the exact minimizing route is: at time `2 * tau`
choose an endpoint minimizer with `exists_lMinVec`; compare its action with the
fixed `Z` ray; apply `lRegInit_shrink`; put both initial vectors in one closed
ball; use bounded-set endpoint injectivity to identify the minimizer with `Z`;
then the defining witness `sigma = 2 * tau` proves membership in
`lInjDomain S T x tau`.

## Routes audited

1. **Minimizer compactness plus endpoint injectivity.**  This is viable and is
   now complete through initial-vector boundedness.  It stops only at the
   bounded-set endpoint injectivity statement above.  The obstacle is a
   missing local-analysis API, not a typeclass or coercion error.
2. **Direct short-time strict convexity.**  The second-variation and index-form
   files prove nonnegativity from a minimizing hypothesis, but provide no
   converse theorem making the regularized action globally strictly convex.
   More importantly, there is no confinement theorem forcing every global
   minimizer into one convex coordinate neighborhood before such a chart
   argument can be applied.
3. **Parabolic scaling to a Euclidean model.**  `Scaling.lean` transports
   individual L-rays and L-exp data under exact rescaling, but the project has
   no smooth compact convergence interface for the rescaled flows as the scale
   tends to zero.  Thus this route would introduce a substantially larger
   geometric-convergence frontier.

The first route is therefore the smallest honest route.  Its remaining
producer looks like substantial but local finite-dimensional differential
geometry; it should be solvable without a new Ricci-flow class or a stronger
consumer assumption, but it is not a routine one-line consequence of the
current API.

## Verification

Focused verification is GREEN and warning-free.  There are no placeholders or
reference-tree imports.  The only public declaration, `lRegInit_shrink`, is
within the twenty-character name limit.
