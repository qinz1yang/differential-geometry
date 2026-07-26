# SmoothStrongPair

## Purpose

This module is the reverse-realization bridge from a classically smooth
geometric Ricci--DeTurck path to the precise strong Sobolev pair consumed by
`deTurckStrong_unique`.

## Source-complete producers

- `smoothPath_strong` packages a continuous `H^(a+2)` path, its continuous
  `H^a` derivative, and the pointwise semilinear equation into canonical
  `timeL2` forcing/high-field and `timeH1` low-field objects.  The trace,
  cross-scale link, parabolic equation, and Nemytskii identity are all proved
  as actual `Lp` equalities.  The represented `timeH1` path is identified with
  the supplied path by the Banach-valued fundamental theorem of calculus.
- `deTurckRHSBase` recasts the geometric right-hand side into the fixed
  background tensor carrier, and `rhsBase_eq_lap_rem` proves its exact
  Laplacian-plus-remainder split.
- `metricDiff_pde` converts the geometric bilinear Ricci--DeTurck equation for
  a metric path into the exact `unitModel` equation for its fixed-background
  metric-difference tensor.  It uses `realize_metricDiff`, so the realized
  metric in the spectral right-hand side is proved equal to the moving metric
  rather than carried as an extra hypothesis.
- `smoothLap_coeff` and `smoothLap_eq_scale` identify the smooth rough
  connection Laplacian with the loss-two spectral Laplacian.
- `smoothRem_eq_N` identifies the smooth remainder embedding with the concrete
  smooth DeTurck nonlinearity.
- `smoothGeom_strong` uses the common derivative from `smoothHs_deriv` to
  identify the geometric PDE derivative componentwise, then exports the
  strong pair for the live symmetric Sobolev nonlinearity
  `deTurckSobolevNHa2Symm`.
- `exists_pathNBound` supplies a finite pointwise forcing bound on a compact
  closed window, and `exists_mixBudget` supplies explicit positive
  force-ball/contraction horizons from the two mixed constants and that bound.
- `smoothGeom_unique` compares two already translated smooth tensor paths by
  constructing their exact strong triples and applying
  `deTurckStrong_unique`.
- `metricRD_unique` is the geometric local capstone: for two
  `MetricFamilySmoothOn` Ricci--DeTurck families with the same metric at an
  interior restart time, it constructs the two metric-difference paths,
  derives joint smoothness, zero initial data, symmetry, component PDE, and
  realization identities, invokes `smoothGeom_unique`, and concludes equality
  of the original metrics on the translated closed window.

No high-order trace at the initial edge is assumed: the theorem works on a
closed window whose tensor path is already smooth on an open neighborhood.
This is therefore the correct producer for windows compactly contained in the
smooth time interval.  Starting the first window from merely C0 agreement at
the left edge remains a separate parabolic startup problem.

## Verification state

The source contains no `sorry`, `admit`, axiom, or opaque placeholder.  A
focused Lean check has not yet been run because a shared named Lean build is
active.  Until that check is green, theorem completion is honestly recorded as
source-assembled rather than verified.

## Remaining route

After focused verification, the next producer is the automatic short-window
shrink: derive the fibre-smallness and high-Sobolev truncation-ball hypotheses
from the zero metric difference and continuity, combine them with
`exists_pathNBound` and `exists_mixBudget`, and iterate `metricRD_unique` across
the common regular interval.  The Ricci-flow endpoint still additionally needs
the harmonic-map heat-flow/common DeTurck gauge and its gauge PDE identity.

The mathematically distinct original-edge issue is unchanged: this file does
not propagate equality from merely `C0` common initial data into a first smooth
window, and no such claim is hidden in `metricRD_unique`.

Endpoint accounting: `ricci_flow_forward_unique` remains **0%** until its exact
Lean theorem is proved and verified.  The reverse-realization and local
Ricci--DeTurck machinery are separate producer progress.
