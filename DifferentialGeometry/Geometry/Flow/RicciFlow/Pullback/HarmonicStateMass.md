# HarmonicStateMass status

## Mathematical role

The coefficient chart `S ↦ hmfAdd q S` is nonlinear.  Therefore a coefficient
velocity cannot be paired by the zero-section form `hmfMass`: it must first be
pushed through the derivative of the local addition at the current state.
This file implements that correction on every finite spectral trial space.

## Source-written facts

- `bilin_coer_near` is the quantitative openness lemma for a finite bilinear
  family: a coercive form remains coercive, with half the lower constant, on a
  sufficiently small state ball.
- `hmfSpecVar` is the derivative of the represented map with respect to the
  finite spectral coefficient.
- `hmfSpecVar_line` identifies its value on a direction with the derivative of
  the corresponding one-dimensional coefficient line.
- `hmfSpecVar_state` identifies that line derivative with `hmfStateVar`.
- `hmfSpecMassPt` pairs two pushed coefficient directions by the target metric.
- `hmfSpecMassOp` integrates the pointwise bilinear map against the moving
  domain volume.
- `hmfSpecMass_cont` turns joint pointwise continuity on a coefficient ball
  into operator-norm continuity of the finite mass for a fixed domain metric.
- `hmfSpecMass_apply` evaluates the integrated operator pointwise under the
  natural integrability hypothesis.
- `hmfSpecMass_state` proves that this operator is precisely the finite
  restriction of the faithful state mass.

No endpoint theorem, axiom, placeholder, or new foundational instance is
introduced here.

## Verification

Source and static review only.  Focused Lean verification is pending because
the shared workspace currently has one long named build restoring the
Ricci--DeTurck edge-energy dependency closure.  Endpoint forward uniqueness
remains 0%.

## Next analytic lemma

On the uniform local-addition coefficient ball supplied by `hmfSpecMap_cd`,
prove the hypothesis of `hmfSpecMass_cont`, namely joint continuity of

`(u,x) ↦ hmfSpecMassPt q S u x`.

Compact parametric integration then gives continuity of
`u ↦ hmfSpecMassOp q (g t) S u`; its zero-state identity and openness of
coercivity give a smaller ball on which the faithful mass is uniformly
invertible.  The finite ODE must use that state-dependent inverse.  Reusing
`hmfFinMass` away from zero would solve the wrong coordinate equation.

## Honest progress

- Faithful finite mass definitions and exact line/state bridge: source-written,
  not yet Lean-verified.
- Uniform state-mass continuity/coercivity: 0%.
- Harmonic-map heat-flow existence and diffeomorphism realization: 0%.
- Exact `ricci_flow_forward_unique`: 0%.
