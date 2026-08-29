# SmallEndpoint

## Result

`lEnd_inj_small` proves the bounded-ball short-time endpoint producer:
for every radius `R`, all sufficiently small positive square-root times `b`
make

```text
W |-> lRegCurve S T x W b
```

injective on `Metric.closedBall 0 R`.

The theorem uses only regularity of `T`; it does not add an injectivity
hypothesis, a generalized flow object, or a new foundational class.  The
public name is within the twenty-character limit.

## Proof route

On a compact product neighborhood of the tangent ball at time zero, the proof
uses the normalized chart displacement

```text
Phi(W,b) = (1/2) * (chart_x(lRegCurve(W,b)) - chart_x(x)).
```

Its time derivative at zero is exactly `W`, by `lRegCurve_vel_zero` and the
identity derivative of the basepoint chart.  The removable quotient is written
as the interval average of the joint time derivative of `Phi`.  Joint `C2`
regularity gives a continuous spatial derivative of this integrand.
`paramInt_tendstoUnif` makes the quotient derivatives converge uniformly to
the identity on the closed ball, and `injOn_of_fderiv_near_id` supplies the
quantitative injectivity.  The fundamental theorem of calculus and
`smul_integral_comp_mul_left` transfer quotient injectivity back to each
positive-time endpoint slice.

The generic quantitative lower-Lipschitz step was already present in the
native tree.  The only new generic inputs used here are the checked parametric
integral differentiation and compact-uniform interval-average convergence
lemmas; no duplicate wrapper was added.

The module imports `Exp` directly.  Its initial `ShortMinimizing` import was
unnecessary and was removed so that the endpoint producer can sit strictly
below the later source-exhaustion assembly without an import cycle.

## Verification

Focused verification is GREEN and warning-free.  There are no placeholders,
admitted facts, or reference-tree imports.

## Next exact theorem

The next producer is `lInj_eventually` in the upper assembly module
`SmallExhaustion.lean`.  Its route is fully geometric: choose endpoint
minimizers at a later shrinking time, use `lRegInit_shrink` to put their
initial tangents and the fixed tangent in one closed ball, apply
`lEnd_inj_small` to identify the minimizer, and package the later time as the
strict-domain witness.

`lEnd_inj_small` and its dedicated bounded-ball endpoint-injectivity brick are
**100%**.  The upper `SmallExhaustion.lInj_eventually` theorem is now also
**100%**; its dedicated source-exhaustion machinery is roughly **70--75%**.
`redVolume_anti` remains **100%**, while the separate `redVolume_zero_lim`
capstone remains unstated and unproved at **0%**.  Reused generic
infrastructure for this brick is **100%**.  P2 remains below **1%**, and the
whole Poincare program remains approximately **3--5%**.
