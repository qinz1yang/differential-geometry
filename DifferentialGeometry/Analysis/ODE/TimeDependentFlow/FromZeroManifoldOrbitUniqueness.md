# FromZeroManifoldOrbitUniqueness

## 2026-07-19 analytic-producer work

`bare_fromZero_local` is the public initial-edge form of the existing
chart-Grönwall argument.  Given a common bare velocity field, one chart ball
with a time-uniform spatial Lipschitz bound, and two one-sided integral curves
starting at the same point, it returns a positive common window on which the
curves agree.

The proof was already present as a private source lemma; this change exposes
the exact reusable interface without changing its hypotheses or proof.

Verification status: the focused check passes, and the named module artifact
has been refreshed.  This is ODE uniqueness machinery, not by itself either
analytic Ricci-flow endpoint theorem.
