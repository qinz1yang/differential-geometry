# HeatKernelApprox

This file proves the quantitative approximate-identity boundary term needed
by the actual Duhamel equation.  The normalized Gaussian has a finite first
half moment, and for global spatial `1/2`-Holder data the pointwise heat
convolution converges to the datum at rate `sqrt (sqrt t)`.

The source proof uses the explicit Gaussian, dilation of Haar measure, its
proved mass-one identity, and the Holder increment estimate.  No convergence
or heat-potential property is assumed as an input.

The file is source-complete and its focused check passes without local
warnings.  It contains no `sorry`, `admit`, axiom, opaque declaration, or
heartbeat override.  This file's approximate-identity machinery is 100%; the
two exported Ricci-flow endpoint theorems remain 0% until their exact Lean
statements are proved and verified.

Together with `HeatKernelPDE`, this leaves differentiation under the spatial
and time integrals as the next exact producer for `(∂t - Δ)Hf = f`.
