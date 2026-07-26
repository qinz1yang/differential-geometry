# ConvFieldOpenComplete

## Current status

`OpenConvOut.complete_at` is the direct completeness consumer for the natural
reference surface `R := P.metric`.  It obtains a positive global lower bound
for the chosen interior time from `OpenConvOut.metric_lower` and transfers
`MetricComplete P` to the time-slice metric with
`MetricComplete.complete_of_lower`.

No completeness field was added to `OpenConvOut`, and no new lower-bound or
radius assumption was introduced.  The target is packaged with the existing
pointed-manifold update `{ P with metric := co.gInf t }`.

Focused verification passed without warnings.  The exact module refresh also
passed.

The theorem itself and its dedicated two-lemma assembly are 100%.  It is a
consumer of the lower-bound and metric-completeness producers, not an
unconditional source of those inputs.  The unconditional HCG compactness
endpoint remains 0%; overall HCG support machinery remains about 60%.
