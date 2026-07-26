# Smooth cutoff energy

## Goal

Prove `exists_cutoff_energy` from the checked intrinsic distance tent and the
support-preserving smooth `W¹,²` approximation theorem. The consumer-facing
normal form is an outer-ball-supported smooth amplitude with half-ball `L²`
mass and a `5 / r` metric-gradient `L²` bound. Squaring these inequalities is
the Dirichlet-energy form used by the Perelman cutoff contradiction.

## 2026-07-17 active proof

The proof uses `riemDistTent g a r`, whose value is one on the half-radius
ball, whose topological support lies in the radius-`r` ball, and whose
intrinsic Lipschitz constant is `4 / r`. Positivity of the inner-ball volume
supplies a positive approximation tolerance. `exists_smooth_supp` then gives
a smooth amplitude with the same outer support margin and controls both the
function error and the metric-gradient error.

The remaining assembly is scalar. The inner mass uses the indicator of the
half-ball and Minkowski; the gradient bound uses `gradFun_sub`, the metric
triangle inequality, the sharp tent gradient bound, and the outer-ball
indicator norm. No global frame, varying-fibre equality, new consumer
assumption, or `HasLocallyConstantChartAt` is involved.

## 2026-07-17 completed proof

`exists_cutoff_energy` now passes focused verification without warnings.  The
proof fixes the Borel measurable-space instance locally, applies
`exists_smooth_supp` with the explicit bound `B = 1`, and carries out both
estimates entirely in scalar `eLpNorm` normal form.  The zero-gradient support
branch proves the fully applied equality `g.inner x 0 0 = 0`; it does not ask
typeclass search to normalize an unapplied Hom-valued metric object.

The theorem adds no consumer assumption and uses neither a selected global
frame nor `HasLocallyConstantChartAt`.  It supplies the energy-equivalent
smooth cutoff producer required by the Perelman contradiction.  The theorem
and its dedicated cutoff machinery are **100%**.  The next frontier is the
cutoff W upper contradiction; that theorem has not yet been stated or proved
and remains theorem-level **0%**.
