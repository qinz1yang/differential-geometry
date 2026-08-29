# CutMultiCore

`lCut_other` closes the symmetry point needed by the multiple-minimizer cut
argument.  If a cut tangent and a distinct tangent both minimize to the same
endpoint at the cut time, the second tangent cannot remain minimizing later:
strict pre-cut uniqueness would identify the two tangents.  Hence the second
tangent belongs to the same fixed-time cut domain.

This is dedicated cut-locus infrastructure, not the measure-zero endpoint.
`lCutMulti_null` remains 0% until it is stated and proved.  Focused
verification passed without warnings.
