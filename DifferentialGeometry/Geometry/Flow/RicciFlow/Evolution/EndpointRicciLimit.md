# EndpointRicciLimit

## Role

`ricci_tendsto_left` is the G4 producer for the direct BBS endpoint route. It
takes the smooth endpoint metric and full chart-Gram left convergence produced
by `exists_endMetric`, and proves pointwise left convergence of Ricci to
the Ricci tensor of that endpoint.

## Route

The proof uses sequential compactness rather than a new direct time-regularity
estimate for spatial metric derivatives. For every sequence tending to the
left endpoint, shift past the uniform-equivalence tail and apply
`metricPreconvFull` through order two. The G3 chart-Gram limits identify the
extracted smooth metric with the prescribed endpoint metric. Existing
`ricciConv_of_dnConv` then transfers the resulting two-jet convergence to Ricci
convergence. `tendsto_of_subseq_tendsto` upgrades this extraction for every
subsequence to convergence of the original sequence.

## Current state

Focused verification and targeted export passed. The axiom probe contains only
the standard `propext`, `Classical.choice`, and `Quot.sound` axioms, with no
`sorryAx`. `ricci_tendsto_left` is therefore 100% and axiom-clean as the G4
producer theorem. It introduces no new analytic black box: its inputs are the
already verified metric precompactness, fixed-reference tail bounds, G3
uniqueness, and Ricci-from-jets estimates. The combined BBS consumer remains to
be checked separately.

## Honest accounting

G4 closes only the `ricci_match` field of the alternate
`CinftyLimitData` producer. Hamilton's main positive-Ricci theorem and every HCG
endpoint theorem remain separate endpoints and must not inherit this local
percentage.
