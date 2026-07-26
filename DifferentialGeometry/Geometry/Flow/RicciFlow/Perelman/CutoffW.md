# CutoffW

## Status

`normalize_cutoff` states the exact normalization bridge needed after
`exists_cutoff_energy`: a nonzero smooth cutoff becomes a unit-`L²` amplitude,
keeps its support, and its Dirichlet energy is divided by the original squared
`L²` norm.

`exists_cutoff_wdata` applies that bridge to the intrinsic ball cutoff and
gives the explicit outer-gradient/half-ball-mass ratio bound.  The scalar
assembly theorem `exists_cutoff_wform` then feeds this data to `w_form_upper`,
under only continuity and a ballwise upper bound for the scalar coefficient.
It now also preserves the proved Dirichlet integrability in its conclusion so
the positive-amplitude producer can consume the actual cutoff without adding
an assumption.

Focused verification and targeted module verification passed without local
warnings.  The cutoff square-form upper theorem and its integrability producer
are complete (100%).
