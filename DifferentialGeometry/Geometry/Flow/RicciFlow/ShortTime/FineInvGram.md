# Fine inverse-Gram bounds

## Proved source facts

- `invGram_buffer_bnd`: metric equivalence supplies a family-uniform
  entrywise inverse-Gram bound on the compact chart buffer chosen before any
  coefficient-dependent refinement radius.
- `gramD_buffer_bnd`: an order-one raw Gram jet bound controls every first
  coordinate partial, with only the fixed model-basis constant lost.
- `invGramD_buffer_bnd`: the inverse-matrix derivative identity converts the
  preceding `C^0` inverse and `D^1` Gram bounds into a uniform first-partial
  bound for inverse Gram entries.
- `invGram_fderiv_bnd`: the canonical finite-dimensional
  `opNorm_le_sum_coord` estimate turns coordinate partial control into a full
  Fréchet derivative bound.
- `invGram_freeze_lip`: convex mean value on any refined closed coordinate
  ball of radius `R <= r₀` gives the required Lipschitz freezing estimate.

The construction is non-circular: `r₀` and its compact buffer are fixed by
chart geometry first; all coefficient constants are then obtained on that
buffer; a later fine-cover radius can be selected from those constants while
remaining at most `r₀`.

## Verification state

Source implementation completed on 2026-07-19.  Lean verification is still
pending because the shared named build/export lane currently owns the build
lock.  No `sorry`, `admit`, axiom, opaque placeholder, or strengthened metric
regularity assumption was introduced.

Endpoint accounting remains unchanged until checked downstream assembly:
`ricci_flow_unif_existence` is 0%, while this fixed-buffer inverse-Gram lane is
source-complete but not yet verified.
