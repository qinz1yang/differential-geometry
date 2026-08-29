# `CovariantDerivativeDifference.lean`

## Result

`covAlong_diff` states the difference between covariant derivatives along the
same differentiable raw curve for two Levi-Civita connections.  The right-hand
side applies `CovariantDerivative.difference` to the field and curve velocity
at the evaluation point.

The theorem is the narrow generic bridge needed by the Ricci-flow
backward-connection argument.  It lives in the connection layer and is reused
after fully applying the connection difference; no Ricci-flow assumption or
parallel tensor hierarchy is introduced.

## Verification

Focused verification passed without warnings.  There is no remaining blocker
in this module.
