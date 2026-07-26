# HeatKernelPDE

This file supplies the first exact PDE producer for the fixed-atlas
parametrix.  It differentiates the already defined normalized Euclidean
Gaussian and proves that, at every positive time, its time derivative equals
the orthonormal trace of `heatD2`.

The source proof uses only the explicit Gaussian formulas, the derivative of
`sqrt`, finite-dimensional Parseval, and algebra.  In particular it does not
assume a heat-solver identity or a bounded heat-potential map.

The file is source-complete and its focused Lean check passes without local
warnings.  It contains no `sorry`, `admit`, axiom, opaque declaration, or
heartbeat override.  The explicit Euclidean heat-equation producer in this
file is 100%; the two exported Ricci-flow endpoint theorems remain 0% until
their exact Lean statements are proved and verified.

The next producer is the zero-initial-trace Duhamel identity
`(∂t - Δ) Hf = f` for the actual time-integrated heat potential.  After that,
linear conjugation gives the frozen anisotropic identity consumed by the
retraction parametrix.
