# ConvFieldOpenPDE

## 2026-07-17 open-window PDE readout

`OpenConvOut.gInf_pde` selects a canonical compact window that is a
neighborhood of the requested regular time, invokes the checked
`ConvOut.gInf_pde` on that window, and upgrades `HasDerivWithinAt` to
`HasDerivAt`.  It assumes the same lower and covariant-tail estimates already
consumed by the raw open-window producer and adds no endpoint hypothesis.

The stale import chain was repaired and refreshed. Focused verification now
passes without warnings; no local theorem repair or additional hypothesis was
needed.

## 2026-07-18 grow-local input propagation

The open-window PDE readout now carries `hcovTail` only on `bf.grow k`, matching
the fixed-window PDE consumer. Focused verification and the exact module
refresh pass.
