# MeasureBridge status

## 2026-07-16

- Added `volume_restrict_eq`: on a chart source, canonical Riemannian volume
  and the corresponding chart-local measure have equal restrictions.
- Added `chart_int_eq_global`: any chart-local integrable real function that
  vanishes off that chart source is globally integrable, with equal global and
  chart-local integrals.
- The proof reuses the existing measurable nonnegative lintegral comparison;
  it does not repeat partition-of-unity bookkeeping in the consumer.
- Focused and targeted verification passed.
- These are measure-transfer producers for the global Lipschitz IBP assembly,
  not a Perelman noncollapsing endpoint.
