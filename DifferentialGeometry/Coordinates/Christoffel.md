# Christoffel Coordinate Notes

## 2026-05-10

- Added `torsion_coeff_eq_christoffel_skew`, a general local-frame identity:
  torsion components are the skew Christoffel coefficients minus the local-frame
  bracket component.
- The proof worked directly from `CovariantDerivative.torsion_apply` and
  coefficient-linearity. The theorem must carry the same local hypotheses as
  mathlib's torsion API: finite-dimensional model space, complete model space,
  and a `C^2` manifold structure.
- Initial focused checks failed because those torsion API hypotheses were not
  present in the previously lightweight Christoffel file. Keeping them
  theorem-local avoided strengthening the whole module.
- Remaining risk: downstream callers need to supply or infer the `C^2` manifold
  instance when using the torsion component theorem.

## 2026-05-10 scalar genericity

- Worked: generalized local-frame Christoffel coefficients, connection
  differences, torsion coefficients, and time-derivative/evolution wrappers from
  `Real` to generic `ð•œ` where the coordinate layer permits it.
