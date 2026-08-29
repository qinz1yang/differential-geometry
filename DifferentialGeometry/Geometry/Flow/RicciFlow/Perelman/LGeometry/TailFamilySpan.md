# TailFamilySpan

## Result

`lTailFamily_ext_of` is the preserving-domain continuation producer.  Starting
from a supplied positive-start regularized L-family on a connected open time
domain, it continues that same family to a prescribed time while retaining the
whole original domain.

`lTailFamily_span` first reaches time zero and then applies the preserving
continuation to a terminal time.  It returns one jointly smooth family whose
connected open time domain contains zero, the positive start, and the terminal
time, with the actual velocity at the positive start still serving as its
parameter.

## Role

This removes the apparent need for a separate extension theorem for a Jacobi
field along the original minimizing curve.  The affine velocity-line field of
the spanning family is defined on one neighborhood of the entire compact
segment from zero to the terminal time.  `exists_lTail_germ` can therefore
globalize the central curve and this field while preserving both on that whole
segment, after which the existing global minimizing index theorem applies.

## Verification and progress

Focused verification passes without warnings or placeholders, and the named
module artifact has been refreshed.  The preserving continuation and the
single spanning family are complete (100% each).  Endpoint differential
injectivity, the Calabi local inverse, the all-point weak barrier, and
`exists_redLen_le` remain unproved (0% each).  `redVolume_anti` remains complete
(100%); dedicated L-geometry is about 49%, and reused generic infrastructure is
complete (100%).
