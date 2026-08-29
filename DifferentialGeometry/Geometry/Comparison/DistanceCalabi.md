# DistanceCalabi

## Status

Focused verification is warning-free GREEN.

`calabiData_of_tail` is the localized producer for the Calabi upper support. It
takes an explicit `CalabiTailData` and assumes the Ricci quadratic lower bound
only along that tail's intrinsic geodesic. The original `exists_calabiData`
public theorem is retained as a compatibility theorem and supplies the local
hypothesis from its global `RicciBoundedBelow` input.

The implementation reuses `VolumeComparison.exists_intrMean_on`; it does not
duplicate the Jacobi/Riccati or post-tail support proof.

`CalabiTailData.shrink` restricts a chosen tail to any shorter endpoint beyond
time one. `CalabiTailData.mem_eball` proves the whole tail lies in a prescribed
outer metric ball from the honest reach inequality
`tail.left + tail.ell * tail.b < R`. `exists_calabiTail_lt` chooses such a
shortened tail whenever the endpoint distance is below `R`, and
`exists_calabiData_lt` combines this with a ball-local Ricci lower bound. Its
Ricci hypothesis is conditional on positive transverse dimension, so the
one-dimensional branch does not carry an unused curvature assumption.

## Next theorem

Build the time-dependent Calabi distance upper support from this explicit tail.
The two length-variation paths must remain inside the same outer ball so their
absolute Ricci bounds can be supplied locally rather than globally.

This is infrastructure for the local Calabi cutoff needed by `shiRm1_ball`; it
does not prove `shiRm1_ball` or `smooth_nlc` by itself.
