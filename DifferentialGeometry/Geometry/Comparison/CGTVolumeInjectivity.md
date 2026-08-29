# CGTVolumeInjectivity

## P1b E1 quantitative producer

- `intrInj_ge_vol` combines the radial-local CGT bound with the existing
  segment-ball and pull-volume comparison bounds.
- Its full-curvature hypothesis is the ambient bound on
  `Metric.eball p (ENNReal.ofReal (3 * R / 4))`. The radial bound consumed by
  `intrInj_ge_cgt_on` follows from `intrFrame_mem_eball`; no global
  `Rm04GlobalBound` is required.
- A supplied lower bound `v` for the radius-`s` metric ball controls the
  numerator. The denominator is bounded explicitly by the Euclidean model
  sphere factor at radius `s` plus the framed tangent-space sphere factor at
  radius `r₀ + s`.
- No public no-conjugacy hypothesis remains. The radius fit puts every
  `t • z`, for `z` in the radius-`r₀ + s` tangent ball and `0 < t < 1`, inside
  the local-diffeomorphism ball. `framedExp_not_conj` then supplies exactly the
  no-conjugacy input consumed by `intrPullVol_le_hyp`.

## Verification

- The first focused verification failed in the theorem header: the
  `RiemannianBundle` variable was declared before the two competing tangent-space
  normed instances were disabled.
- The instance attributes are now installed at file scope before
  `RiemannianBundle`, matching the warning-free `CGTInjectivity` ordering.
- Focused verification is warning-free GREEN. The named module refresh is also
  GREEN (4072/4072). The theorem statement and proof body were unchanged by the
  instance-order repair.
- After the ambient-curvature and generated-no-conjugacy interface edit,
  focused verification is again warning-free GREEN (24.0 seconds). The current
  named module refresh is GREEN (4073/4073).

## Program status

- The weaker public interface of `intrInj_ge_vol` is verified. It is not itself
  the compact-closure E1 endpoint. P1b remains zero of two exact endpoints.
- Dedicated P1b machinery remains about 92%; the whole P0–P9 infrastructure
  remains at the authoritative 15–25%.
