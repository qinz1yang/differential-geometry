# `ChartVariation.lean`

## Result

`exists_chartVar` realizes a compactly supported smooth model-coordinate
field along a curve as the transverse field of a global smooth variation.
The variation is fixed wherever the field vanishes.  A compact thickening and
a bounded sine parameter keep the perturbation inside one chart.

The theorem needs no completeness, connectedness, metric, or continuous
Riemannian-bundle assumption.  This is the generic producer required by the
fixed-endpoint fundamental-lemma argument.

## Verification and use

Focused verification and the targeted export refresh passed without warnings.
`IsLCritical.isLGeo` consumes the theorem to prove the criticality-to-Euler
converse.
