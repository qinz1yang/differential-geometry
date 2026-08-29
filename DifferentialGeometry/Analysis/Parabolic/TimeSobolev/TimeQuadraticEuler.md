# TimeQuadraticEuler

## Scope

This generic one-dimensional calculus layer differentiates `timeQuad` and
derives its fixed-endpoint weak Euler equation after adding a differentiable
position potential.  It does not assert Tonelli regularity or any manifold
Euler equation.

## API

- `timeOp_inner_comm`: the integrated operator is symmetric under the natural
  almost-everywhere self-adjointness hypothesis.
- `timeQuad_line`: the genuine affine-line derivative of the quadratic energy.
- `sameTimeEnds`: the affine fixed-endpoint class through a time-`H¹` curve.
- `timeQuadPot`: kinetic quadratic energy plus an arbitrary position potential.
- `timeQuad_weak_euler`: a fixed-endpoint local minimizer satisfies the weak
  Euler identity against every zero-endpoint time-`H¹` variation when the
  potential derivative is represented by a time-`L²` force.

## Verification

Focused verification passes without warnings or placeholders.

## Project position

The generic weak-Euler producer is complete (100%) and is the first calculus
input for the later Tonelli regularity upgrade.  The next separate generic
stage must turn this variational identity into time regularity of the momentum
and then of the curve.  The L-geometry regularity theorem and
`exists_lMinimizer` remain unproved (0%); this file is dedicated generic
infrastructure only.
