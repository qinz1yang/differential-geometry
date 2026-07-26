# FineWeightBound

## Role

The componentwise fine-chart reassembly estimate naturally produces one
strictly positive real weight for each finite tensor component.  This file
contains the independent finite-sum step that replaces those weights by their
sum:

- `weight_sum_bound` bounds the weighted `ENNReal` sum by the total weight
  times the unweighted sum;
- `weight_sum_pos` proves that total weight is positive for a nonempty finite
  component type.

The lemmas are independent of the currently blocked `FineTensorRepack` export
and introduce no assumptions, instances, placeholders, or notation.

## Verification state

Focused Lean verification passes without local warnings.  Both declarations
are fully verified and contain no placeholder.  This file is the smallest
unblocked producer needed after the coordinatewise estimate in
`FineTensorBound.lean`.

File-local finite-weight machinery is 100% complete.  The bounded fine-atlas
reassembly remains unverified because `FineTensorRepack.olean` is absent, and
the exact theorem `ricci_flow_unif_existence` remains theorem-level 0%.
