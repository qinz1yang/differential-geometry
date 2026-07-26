# ConvFieldOpenZero

## Current status

`OpenConvOut.gInf_zero_eq` selects a canonical closed window containing zero
and applies the existing fixed-window `gInf_zero_eq`.  It does not change the
subsequence, limit family, or time-zero convergence hypothesis.

Focused verification passed.  The theorem and its dedicated open-window
adapter machinery are 100%.  The unconditional HCG compactness endpoint
remains 0%.
