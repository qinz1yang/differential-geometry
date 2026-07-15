# StepCAtomJoin

## 2026-07-09 common live-slot refinement

- `existsLiveJoint` runs the live origin-metric extraction and one finite
  Pi-valued forward-transition extraction in sequence, returning their
  composite strict subsequence.
- Metric convergence is preserved through the transition refinement with
  `MapCInfConvOnCompacts.comp_subseq`.
- Only `LiveSlot` participates.  Its overlap and maps-to hypotheses are
  eventual, and the source-ball hypothesis is one eventual condition for the
  fixed source family `beta`; finiteness supplies a common tail.  Thus neither
  dead slots nor finitely many early fallback centers acquire false geometric
  obligations.
- The theorem asks only for the forward overlap/domain/mapping data it uses.
  It no longer requests and discards reverse domains, reverse maps, or cocycle
  assumptions.
- The transition extraction is internally packaged as the Pi-valued map
  `E -> (LiveSlot L pb r -> E)` on one common open source domain.  The public
  result projects it back to `LiveSlot L pb r -> E -> E`, matching
  `stepCAtom_conv`.  It also returns the per-index transition smoothness and
  `NormalOverlapOn` facts after the common tail shift, together with the fact
  that each live slot is now an actual `some` centre rather than its totalized
  fallback.  The consumer therefore does not have to recover hidden eventual
  data.  This is the fixed-`beta` atom needed by the Step-C join; an outer finite
  diagonal over source slots remains separate.
- The upstream Derivation wall was repaired on 2026-07-10. `existsLiveJoint`
  now passes focused verification and the targeted build together with its
  downstream atom package.

## Progress accounting

- Common metric/transition subsequence machinery: implemented and verified on
  the honest eventual one-sided interface.
- `StepB1RawInput` producer theorem: 0%.
- Textbook B1 theorem: 0%.
- Dedicated Step-B1 machinery: about 63%.
- Chapter 4 machinery: about 66%.
- Whole HCG compactness machinery: about 46%.
- Conditional and final compactness endpoints: 0%.

## 2026-07-13 H6 live-slot extraction

Added `existsLiveJointH6`. A fixed bounded target coordinate ball provides the
order-zero anchor; H6 source/target metric-ball and exponential-ball
containments provide every positive derivative bound. Per-live-slot bounds are
assembled with `IsometryDerivBoundsOn.pi`, so the existing Pi-valued
Arzela--Ascoli extraction is reused unchanged.

The theorem is focused-green and the exported artifact was refreshed. The
finite source-slot diagonal now consumes the H6 path. A zero-consumer audit then
allowed the old S6 compatibility entrypoint `existsLiveJoint` to be removed;
`existsLiveJointH6` is canonical. Removing the endpoint's temporary S6 field is
a separate downstream task. Focused verification after the cleanup passed.

The downstream task is now complete: the finite source-slot diagonal uses the
H6 entrypoint, and the endpoint S6 field/type were removed after a zero-consumer
audit.  The remaining sparse interacting-target redesign is independent of S6.
