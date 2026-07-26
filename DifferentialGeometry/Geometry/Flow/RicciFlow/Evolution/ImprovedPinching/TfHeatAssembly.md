# TfHeatAssembly.lean

## 2026-06-13

Removed explicit local smoothness inputs from the Levi-Civita-specialized
`tfHeat_lc` and `tfHeat_metric` surfaces after the curvature symmetry wrappers
began deriving that data internally.  Remaining local `hcov` producers in this
file are internal and feed still-generic APIs.

Verification: focused check passed.  No new `sorry` or `admit`.

## 2026-06-14 hcov/hmc cleanup

Synced the `ricci_heat_mc` caller after all-time metric compatibility became an
internal fact of that producer.  Earlier local hcov arguments to concrete
Levi-Civita curvature symmetry wrappers are also gone; the remaining
compatibility/smoothness hypotheses in this area are for genuinely generic
metric-family or arbitrary-connection APIs.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed redundant explicit `infty+1` manifold assumptions from the concrete
metric heat assembly surface.  The existing global smooth manifold context is
enough for the checked proofs.

Verification passed for the edited file.
