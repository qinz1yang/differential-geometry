# MapConvergenceComp.lean

## Status

Verified.  This file adds the reusable composition-convergence layer for
`MapCInfConvOnCompacts`.

## What Landed

- `MapCPConvOn.comp_tendsto_atTop` and
  `MapCInfConvOnCompacts.comp_tendsto_atTop`: convergence is stable under any
  reindexing that tends to infinity, not only strict subsequences.
- Localized derivative extraction and reconstruction helpers for open domains:
  `MapCPConvOn.tendstoUniformlyOn_iteratedFDeriv`,
  `MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv`, and
  `mapCPConvOn_of_tendstoUniformlyOn`.
- Moving-evaluation derivative convergence:
  `MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving`.
- `MapCInfConvOnCompacts.comp`: same-index `C^∞` composition convergence on
  open domains.  The proof uses `iteratedFDeriv_comp` plus
  `FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO`; it does not
  manually expand ordered partitions.

## Notes

The composition theorem assumes `Set.MapsTo (B k) U V` for every `k` and
`Set.MapsTo Binf U V`.  This is the honest smooth-composition condition needed
to view `A k ∘ B k` as smooth on `U`.  The compact corral for the moving
evaluation points is derived internally from order-0 convergence of `B k`.

This discharges the pure analysis part of the former Step-B Faà-di-Bruno
frontier.  The two-parameter `lbl399` consumer is wired in `C4/StepBApproxIso`.
