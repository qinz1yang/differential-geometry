# ChartWkpSupport

## Status

Source-written only. A different named build owns Lean verification, so none
of the claims in this note should yet be counted as elaboration-verified.

## Mathematical content

The file closes the support problem for weak component limits without choosing
a smooth representative.

- `secComp_zero_kernel` shows that every POU-weighted component vanishes on
  the chart target outside the fixed compact POU image.
- `secCompLimit_ae_zero` passes that vanishing property to the scalar Sobolev
  limit by convergence in measure and an a.e.-convergent subsequence.
- `secCompRep` uses the existing compact representative operation.
- `secCompRep_ae`, `secCompRep_mem`, and `secCompRep_tendsto` show that this
  representative is a.e. unchanged, remains in the same `W^{k,p}` space, and
  is the norm limit of the original components.
- `secCompRep_support` supplies the pointwise topological-support inclusion
  needed by the quantitative cross-chart theorem.

No extra regularity is assumed, and no axiom, opaque producer, `sorry`, or
`admit` is introduced.

## Honest progress

- Support inheritance and compact representative: 100% source-written, 0%
  Lean-verified in this lane.
- `wkpTensor_limit`: the support obligation is discharged in source; the exact
  endpoint is assembled in `ChartWkpComplete.lean` but remains 0% until Lean
  verification.
- `ricci_flow_unif_existence`: 0%; this is infrastructure only.

