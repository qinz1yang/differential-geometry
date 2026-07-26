# StateCoerciveMass status

## Source theorem

`stateMass_exists` is the finite-dimensional Picard--Lindelof producer for
the faithful nonlinear equation

`M(t,u(t)) u'(t) = R(t,u(t))`.

It uses uniform coercivity, time continuity at fixed state, and state
Lipschitz bounds for both the mass and residual.  The inverse-mass Lipschitz
estimate is derived from `IsCoercive.sharp_var_le`; the theorem chooses a
positive time on which the Picard trajectory remains inside the input state
ball and returns the untruncated equation there.

`coerOn_of_lip` is the quantitative uniform-radius bridge used before that
theorem: a common state-Lipschitz bound and a common zero-state coercivity
bound retain half the coercivity on any ball satisfying `K R ≤ c / 2`.

## Verification

Source-complete with no placeholder.  Focused Lean verification is queued
behind the single active Ricci--DeTurck edge-energy build.  Until that check
passes, this is unverified machinery and not an accepted endpoint producer.

## HMF use

The intended consumer is the finite spectral harmonic-map heat equation with
the state-dependent local-addition mass `hmfSpecMassOp` and the true negative
Dirichlet-energy residual `hmfSpecResid`.
