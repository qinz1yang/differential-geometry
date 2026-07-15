# Galerkin forcing time-L2 limit

## 2026-07-14 compactness API cleanup

The file now consumes the rank-generic `tendsto_of_coeff` theorem from
`TensorHsInterpolationLimit`.  Its former private coefficient-to-Sobolev proof
was an exact lower-layer duplicate and has been removed; no theorem statement
or consumer assumption changed.

The lower theorem passed focused verification and its `.olean` was refreshed.
This consumer file's focused check is currently blocked before local
elaboration by the missing upstream
`CurvatureCoefficientDifferenceJetTower.olean`; a narrow refresh is running.
This is stale-import/tooling fallout, not a theorem or analytic obstruction.
The existing forcing-limit endpoint is unchanged.  `scalar_gal_subseq` remains
not started (0%); its dedicated compactness machinery is about 75% complete.
Perelman no-local-collapsing remains not started (0%); its dedicated analytic
machinery is about 44% complete.
