# LocalDiffeomorphism

## Current state

- `exists_open_nhds_expMap_diffeoOn` remains the stable qualitative local
  exponential-diffeomorphism API.
- `exists_exp_pd_chart` exposes the stronger producer already proved by the
  concrete construction: the selected partial diffeomorphism's target is
  contained in the base chart source.
- Focused verification passed without warnings or local `sorry`s.

## Choice-spec frontier

The current `NormalCoordinates.expMapDiffeo` still chooses from the older weak
existential.  Its chosen witness therefore cannot be proved to satisfy target
containment merely because `exists_exp_pd_chart` has a good witness: the
property is absent from the proposition passed to `Classical.choose`.

Two attempted routes failed for exactly this reason: definitional reduction of
the old choice and explicit simplification of its existence proof.  The
smallest correct next step is to change the existing `expMapDiffeo` definition
to choose from `exists_exp_pd_chart`, update its two projection lemmas, and add
`exp_target_sub_chart`.  Do not add a second exponential branch.

This is a missing choice-spec/API bridge, not new exponential geometry.
`StepB1RawInput` and textbook B1 remain 0%; the generic producer here is
complete, while the downstream readout containment is not.
