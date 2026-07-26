# ConvFieldOpenLower

## Current status

`OpenConvOut.metric_lower` selects one canonical compact window around an
interior time and applies the checked fixed-window lower-bound closure theorem.
The comparison coefficient is allowed to depend on the window, which is
exactly the quantifier order needed for time-slice completeness.

No lower-bound provenance is added to `OpenConvOut`: the theorem consumes an
explicit windowwise lower bound on the already selected sequence.  Raw
producers can discharge it with `gSeqExt_lower`.

Focused verification passed.  The theorem and its dedicated lower-bound
machinery are 100%.  The unconditional HCG compactness endpoint remains 0%.
