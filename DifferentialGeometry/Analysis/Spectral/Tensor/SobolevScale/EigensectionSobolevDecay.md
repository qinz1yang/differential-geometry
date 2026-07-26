# EigensectionSobolevDecay

## 2026-07-16: covariant-rank generic eigensection bound

Added `ccEigen_norm_sq` and `eigen_toHs_le` for every covariant rank `(0,s)`.
The proof deliberately does not compare `wtwokTwoNorm` with the intrinsic
partition-of-unity Hilbert norm: those norms differentiate different weighted
chart expressions, so that comparison would require a genuine overlap/POU
norm-equivalence theorem.

Instead, the proof reuses the generic spectral embedding `ccTensorToHs`, the
generic covariant jet estimate `hsJet_le`, and the reverse Hebey bridge.  The
orthonormal eigenbasis evaluates the generic spectral norm exactly, giving the
uniform bound by `(1 + lambda_i)^(2*k)`.

Focused verification passed without warnings or new `sorry`.  The generic
producer is complete (theorem 100%, dedicated machinery 100%).  The older
rank-`(0,2)` theorem remains unchanged as a compatibility interface.

