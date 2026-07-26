# HmfStateFixed status

## Source theorem

`stateSplit_fixed` is the abstract rough fixed point for a genuinely
state-dependent principal coefficient.  Its
principal flux depends on the path value, and the proof uses the exact two-arm
state/gradient difference split.  The critical rate is

`4 * (eps + 2 * L * R) + K * R`.

This is a valid general package.  For the expected strong HMF chain-rule
cancellation, however, its faithful specialization has `L = 0`: the vertical
derivative of the local addition cancels between the time derivative and the
leading tension term.  The necessary nonzero state-Lipschitz term is instead
the quadratic third arm in `HmfStateQuad.lean`.

## Verification and remaining realization

Source-complete with no placeholder, but focused Lean verification is queued
behind the single active Edge build.  The remaining geometric producer must
realize `A`, `Q`, the rough model, and both heat potentials from finite HMF
charts, then prove smoothing and the gauge PDE identity.  Forward Ricci-flow
uniqueness remains 0% until that realization and gauge undoing are checked.
