# H1H2AppCc

## Main result

`appCc_h1_h2_h1` states the dimension-three estimate

`H1(operator coefficient) x H2(covariant field) -> H1(covariant output)`.

The coefficient hypothesis is exactly the squared intrinsic `L2` jet sum over
`Finset.range 2`; it does not assume a pointwise coefficient bound or a second
coefficient derivative.

## Proof architecture

- The output and the `nabla Phi * U` Leibniz arm use the canonical spectral
  `H2 -> L-infinity` estimate for `U` and metric `L2` control of `Phi` and
  `nabla Phi`.
- The only mixed arm, `slotExtend Phi * nabla U`, uses the checked general
  mixed-tensor `H1 -> L6` theorem, exact slot-extension fibre scaling,
  finite-volume `L6 -> L3`, and `L6 x L3 -> L2` Holder.
- `hs_le_jet` converts the resulting zeroth and first output jets to the
  consumer's spectral `H1` norm on the same background metric.

This avoids the inadmissible coarse route that would require a pointwise
coefficient bound or an `H2` coefficient.

## Verification

Focused source verification passes without local warnings, and the named
`H1H2AppCc:olean` target is exported.  The theorem and its product machinery
are 100% complete and contain no placeholders.

The worktree's physical path made one deep upstream `.olean` output exceed the
Windows legacy path limit.  The checked recovery used the locked build wrapper
with a temporary Lake configuration whose `buildDir` was a short junction to
the same current `.lake/build` tree.  The current-source
`Sharp -> Bounded -> Explicit` dependency chain and then `H1H2AppCc:olean`
all built successfully through that short output path; the temporary
configuration and junction were removed after verifying the final artifact in
the ordinary build tree.
