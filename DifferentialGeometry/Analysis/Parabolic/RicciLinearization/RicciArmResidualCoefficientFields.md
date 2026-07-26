# RicciArmResidualCoefficientFields

## 2026-07-13 public metric-tensor evaluation

`metricCcTensor_apply` is now the canonical public evaluation theorem for
`metricCcTensor`.  It states the fully applied scalar identity

`ccTensorBilin g₀ (metricCcTensor g₀ g) x v w = g.inner x v w`.

The theorem lives beside `metricCcTensor` and `metricCcTensorFib`; no consumer
wrapper or new assumption was added.  Its proof is the former private proof and
uses an applied scalar normal form rather than equality of whole tensor or Hom
objects.  Focused verification passed.

The targeted export refresh did not reach this module because the unrelated,
actively claimed upstream file `RicciIdentitySmoothFrame.lean` failed at line
201 with `unexpected token 'omit'`.  No change was made to that lane; rerun the
module refresh after its owner restores a green upstream tree.

Honest scope: `metricCcTensor_apply` is complete (100%).  It is one small
realization brick for identifying the `g₀`-tagged metric-difference coefficient;
`scalar_crit_tame` itself remains unstated and unproved (0%).  Uniform coefficient
jet control and the final spectral Sobolev estimate remain separate frontiers.
