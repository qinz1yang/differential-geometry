# Metric contraction Leibniz grid

## 2026-07-14 rank-cast norm normal form

`norm_castRankCc_db` records that the proof-only covariant-rank transport
`castRankCc_db` preserves the intrinsic smooth-tensor norm.  This small
canonical projection lemma lets downstream `L²` estimates normalize a rank
cast through `SmoothCcTensor.norm_toL2` without whole dependent-tensor
equalities.  The theorem uses no additional geometric assumptions.

Focused verification and the named module build passed.  This helper is
complete (100%) and introduces no new analytic frontier.

