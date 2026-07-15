# StepCWeights.lean

## 2026-07-09 Generic pointwise weight producer

The old `StepB1Producers.normWeights_data` was tied to a normed model-space
source.  That prevented the concrete manifold-valued Step-C atoms from feeding
the otherwise base-space-independent `centerAverage.WeightDataOn` interface.

This file adds the lower, arbitrary-base-type layer:

- `rawWeights` and its sum, nonnegativity, positivity, delta, and active-slot
  lemmas;
- `rawWeights_data`, producing `WeightDataOn` without any vector-space or
  smoothness structure on the source;
- `cutRaw`, the base-preserving kill formula abstracted away from any particular
  bump representation;
- `cutRaw_sum_pos` and `cutWeights_data`, which show that a covered atom family
  with a base-supported kill factor has a positive denominator and the required
  active-hat behavior.

Focused verification and the targeted module build passed without local
warnings.  This closes the source-type normalization gap.  It does not yet
construct the intrinsic radial atoms or the unconditional live-center join
endpoint.

Honest progress: the `StepB1RawInput` producer theorem is still unstated and
therefore 0%; its dedicated machinery is now about 52%.  Step-B machinery is
about 52%, Chapter-4 machinery about 60%, and the whole HCG compactness
machinery about 44%; the final compactness endpoints remain 0% proved.
