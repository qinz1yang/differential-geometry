# LowRegSmoothBridge

## Role

This file supplies the first faithful geometric bridge out of the genuine
low-regularity fixed-point nonlinearity.  It never replaces the solver horizon
by a later solution-dependent subinterval.

## Source status

- `symm_h2_of_state` transfers the lower `H2` state bound to the symmetrized
  smooth representative used by `coreN`.
- `lowRegN_on_core` applies `Dense.extend_eq` using the core continuity exported
  by `lowreg_partial_sol`'s construction.
- `lowRegN_on_smooth` identifies the dense extension with the concrete
  `deTurckSmoothN` value of a smooth representative.
- `lowReg_force_smooth` transports the fixed-point forcing identity to the
  genuine smooth Ricci--DeTurck forcing on the same measure `timeMeasure T`.
  Its smooth-family and ball pins are geometric data to be produced by the
  remaining bootstrap, not a claimed existence result.

## Canonical API audit and exact frontier

The current `ForcingFiniteOrderTimeRegularity`,
`ForcingCoordinateTimeRegularity`, and
`MaxRegSolutionJointlySmooth` producers are specialized to a high base order
`a` (their hypotheses include `2 * dim + 10 <= a` or stronger) and return an
unknown `d <= T`.  The new fixed point has base order `a = 1`.  Therefore those
theorems cannot be applied directly, and their returned `d` cannot be renamed
to the solver's horizon without violating the uniform-horizon requirement.

The smallest next analytic producer is a low-regularity, same-horizon analogue
of the finite-order forcing bootstrap.  In consumer shape it must take the
`a = 1` Duhamel field, its `lowRegN` forcing equality and state-ball membership
on `timeMeasure T`, and return on `Set.Icc 0 T` a smooth representative family
`F` with all-order spectral jet-mass bounds, the spectral pin
`smoothCcToTensorHs g0 3 (F t) = field t`, and the lower `H2` ball bound for
every `t`.  Its proof must choose any auxiliary smoothing budget before the
final solver horizon, from explicitly controlled constants; it may not first
solve on `T` and then return an unknown solution-dependent `d <= T`.

Once that producer exists, `lowReg_force_smooth` feeds the existing
`RealizeTransport` and `DeTurckRicciPde` identities, after which the canonical
joint chart-Gram reconstruction can be used on the same `T`.

This remains fixed-`g0`, dimension-three machinery.  No generic-family
uniformization and neither public endpoint theorem is claimed here.

Lean verification is deferred while the shared named build occupies the sole
Lean slot.  No `sorry`, `admit`, axiom, new class, instance, or notation is
introduced.
