# KochLammLateKern

## Status

Source complete. The focused Lean check passes with no local warnings.

## Intended theorem

`klTermKernel_memLp` proves that

`(s,y) ↦ H_(t-s)(x-y)`

belongs to `L^((n+4)/(n+2))` on `(t/2,t] × V`. The proof uses:

- exact spatial power mass `heatPow_shift`;
- Fubini's product integrability criterion;
- the identity `klHeatExp = -n/(n+2)`; and
- terminal-half integrability from `klTimePow_intble`.

This avoids the invalid step of extracting a uniform spatial-slice `L^q`
bound from a space-time `KLSource0` hypothesis.

## Remaining late value step

The next producer pairs this kernel with the source on a restricted terminal
cylinder using space-time Hölder. A spatial shell decomposition is still
needed because the kernel theorem is global in space while each
`KLSource0.late_lq` bound is local to one ball.

The endpoint `ricci_flow_forward_unique` remains 0%.
