# LateVolumeLow

## Role

This module turns the half-dimension reduced-length fence into one positive
reduced-volume floor on a compact manifold for every terminal time in a
half-open forward interval.

## Checked endpoint

`redVolume_late_low` assumes `a0 < a < omega` and
`Ico a0 omega subset D.regular`. It produces one `v0 > 0`, independent of the
terminal time, basepoint, and positive backward time, such that

```text
a <= T < omega, 0 < tau <= T - a0
  -> v0 <= redVolume S T x tau.
```

The proof chooses the fixed intermediate slice `(a0 + a) / 2`, obtains its
positive volume contribution from `redVolume_slice_low`, and for each terminal
time constructs a compact-slab Riemann bound and terminal-metric completeness.
`exists_redLen_le` supplies a low endpoint; `exists_redMin_vec` replaces it by
an actual minimizing ray, `lRegDomain_of_slab` continues that ray to the fixed
initial slice, and `redVolume_anti` transfers the slice floor to every shorter
positive backward time.

The theorem does not need `0 < a0`; the strict inequalities already provide
all positive backward-time facts used by the proof.

## Verification and next frontier

Focused verification is warning-free green, and the named module artifact is
refreshed successfully. `redVolume_late_low` is therefore 100%.

The next capstone `smooth_nlc` remains 0%. The late floor is now complete, but
the controlled-ball upper estimate still needs one short-scale threshold
uniform over the half-open terminal-time interval. The existing fixed-time
threshold depends on a compact-slab scalar-gradient bound; replacing it needs a
genuine scale-invariant local first-curvature-derivative producer
`shiRm1_ball` on a smaller cylinder inside an Rm-controlled parabolic ball,
followed by the scalar-gradient adapter `lGrad_ball`. The current Shi APIs all
use whole-manifold curvature control, and a finite-cover argument cannot repair
the noncompact half-open time interval.
