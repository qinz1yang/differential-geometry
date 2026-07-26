# BishopJacobi notes

## 2026-07-18 curve-density monotonicity

- Proved `curveMean_le_hyp` and `curveRatio_anti`. Under the Jacobi, Wronskian,
  linear-independence, dimension, and Ricci hypotheses, the transverse Jacobi
  density divided by the hyperbolic model density is antitone on the positive
  time interval.
- Focused verification and the exported module refresh passed.
- The theorem compares a chosen perpendicular Jacobi family. A separate
  change-of-basis/block-Gram determinant lemma must connect it to
  `normalChartDensity`; the direction-dependent positive factor should cancel
  in radial ratios.
