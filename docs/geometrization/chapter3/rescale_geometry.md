# Positive metric normalization and the exact net bound

Nine public theorems and one definition in four leaves transport actual
metric structures under d_new = c*d_old, c>0. The identity is a uniform
equivalence; completeness is equivalent, Hausdorff dimension of every set
is unchanged, and open and closed balls of radius c*r equal the original
radius-r sets (including nonpositive r). Public conclusions explicitly name
the original and rescaled metric/uniform/topological structures.

For any ordered-domain function, rescaled extended variation is at most
ofReal(c) times the old variation, without continuity or finiteness premises.
This proves arbitrarily short continuous curves for the actual rescaled
metric by applying the old property with error epsilon/c. No assertion that
an arbitrary curve is continuous is introduced.

For kappa>0, four-point comparison at curvature parameter kappa in the
original metric is equivalent to parameter1 in the metric scaled by
sqrt(kappa). The equivalence also holds for local comparison neighborhoods,
since the constructed rescaling preserves topology. This is exact angle
normalization, not a general monotonicity theorem in curvature. Kappa=0 is
excluded from this rescaling and remains handled by the accepted zero-to-
kappa weakening theorem.

For 0<c<=1, R>=0, epsilon>0 and any natural n and real L, the exact natural
ceiling bound N(n,L,cR,c*epsilon) is at most N(n,L,R,epsilon), where
N=(1+ceil(4*L^2*sqrt(n)*sinh(2R)/epsilon))^n. Convexity gives
sinh(2cR)<=c*sinh(2R); cancellation is legitimate because c and epsilon
are positive. This preserves the original unscaled uniform bound rather
than introducing a constant depending on kappa.

Source bodies checked: blueprint207A MC10 full1102-1119; AC35 full3843-3883
with its explicit sqrt normalization; AC64 full5374-5421, retaining its
conditional sharp8R/KL route. The accepted metric rescaling, angle identity
and convex hyperbolic-sine proofs were read. At pinned Mathlib c55e6e786f49,
the uniform-equivalence completeness proof, both Lipschitz dimension
inequalities and the partition-based variation bound were inspected; exact
locators and hashes are in the source record. Existing AKP/BBI checks and
errata qualifications are reused for unchanged model-angle claims. In
particular, the printed general-k BBI10.6.2 coefficient is not imported.

This supplies normalization infrastructure. Joining it to the fixed-
curvature dimension-to-covering producer, treating zero curvature, and
assembling growing-region SAME-limit extraction remain subsequent work.
No sharp8R theorem, full Chapter3/4 completion or PC migration binding is
claimed. Blueprint207 and earlier mathematical leaves remain unchanged.
