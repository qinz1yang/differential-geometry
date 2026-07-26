# RicciNorm Notes

## 2026-06-14 hmc cleanup

`ricci_heat_mc` no longer asks callers for all-time metric compatibility of
`S.base.connection`.  It builds the realized metric family using the canonical
metric-connection compatibility at each real time.

Verification passed for the edited file and module refresh.

## 2026-06-14 manifold instance cleanup

Removed the explicit `IsManifold I ((infty : WithTop NatInfinity) + 1) M`
assumption from this concrete metric file.  The file already carries the global
smooth manifold instance it needs; no theorem statement needs to expose the
`infty+1` spelling.

Verification passed for the edited file.
