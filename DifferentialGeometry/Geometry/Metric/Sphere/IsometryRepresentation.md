# IsometryRepresentation

## Status

The intended producer is `orth_rep_of_iso`: a positive-dimensional round-sphere
action supplied as metric-preserving diffeomorphisms is represented by a
monoid homomorphism into the ambient orthogonal group.

The proof extends the differential of each action map at one fixed sphere point
with `ambient_iso_of_tan`, identifies the resulting sphere diffeomorphism
globally using `localIso_rigid`, and reflects the action laws through
`sphereDiffeo_inj`.

The complete producer is now verified. Once `LocalIsometryRigidity` was
available, the consumer needed only two local elaboration repairs:

- derive `NeZero n` from the existing positivity hypothesis and use
  `finrank_euclideanSpace_fin` to synthesize the corresponding Euclidean model
  `NeZero` instance;
- consume the function equality returned by `localIso_rigid`, then lift it to
  equality of bundled diffeomorphisms with `Diffeomorph.ext`.

No consumer-specific assumption or new wrapper class was introduced. The
focused check and the exact target refresh both passed, and the file is
`sorry`-free.

## Project accounting

- `orth_rep_of_iso`: proved and verified (100%).
- Round-sphere action-to-orthogonal-representation machinery: 100%.
- Global constant-curvature classification machinery: still incomplete.
- `ham3_space_box`: theorem not proved (0%); this file is dedicated machinery.
- Dedicated `ham3_space_box` topology/global-geometry machinery: about 45%.
- Wider Hamilton positive-Ricci infrastructure: about 80%.
- Whole HCG compactness infrastructure: about 60%.
