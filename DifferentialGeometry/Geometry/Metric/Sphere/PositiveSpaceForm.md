# PositiveSpaceForm

## Role

`constPosQuotient` is the geometry-native producer behind
`ham3_space_box`.  It replaces the original manifold by the existing
same-universe standard-model copy, pulls the positive constant-curvature
metric across that diffeomorphism, identifies the normalized universal cover
with the round three-sphere, and packages the conjugated deck action using
`roundQuotientUC`.

The theorem consumes exactly the compactness, connectedness, boundarylessness,
dimension, and constant-curvature data already stored by the Hamilton
endpoint.  The `Inhabited`, locally path-connected, and semilocally simply
connected structures used to form the universal cover are derived locally;
they are not new endpoint assumptions.

## Verification and progress

Focused verification, the exact module refresh, and the downstream Hamilton
replay pass.  The former `UniversalCover.fibre_countable` `sorry` exposed by
the first audit is replaced by the refined polygon-code proof.  The final
axiom replay for `constPosQuotient` and `ham3_space_box` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

`constPosQuotient`, the dedicated positive-space-form machinery, and the
Hamilton-facing `ham3_space_box` theorem are each complete and trusted (100%).
The whole HCG infrastructure remains conservatively about 60%.
