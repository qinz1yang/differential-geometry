# Finite spectral pairing

## 2026-07-14 finite-core Parseval bridge

The rank-generic finite spectral pairing bridge is complete.  The public chain
is `cc_iter_coeff`, `cc_l2_pair_tsum`, `cc_pair_tsum`, and `finite_cc_pair`.
The final theorem identifies the finite weighted coefficient pairing of a
finitely supported `tensorHs` element with the intrinsic `L²` pairing of its
canonical smooth representative against `(1 - Δ)^n`.

The constant-free identity is independent of the size and location of the
spectral support.  It reuses `tensorHsSmoothRepr` and does not introduce a
second finite-combination representation.  Focused verification and the named
module build passed, with no new `sorry`.

This bridge itself is complete (100%).  It is machinery for the scalar
critical-tame/Galerkin route, not a conjugate-heat or noncollapsing endpoint.

## 2026-07-14 finite representative energy

`finite_repr_norm` factors the repeatedly used identification between the
spectral Sobolev norm of `tensorHsSmoothRepr` and the finite weighted
coefficient energy.  It is a projection lemma in this rank-generic finite-core
layer, rather than a consumer-local rewrite.

Focused verification now passes.  The initial named-module refresh exposed a
local rewrite-normal-form failure at the whole summation; scalarizing it to a
`tsum_congr` proof closed the issue without changing the statement.  The
`finite_repr_norm` theorem and its dedicated projection machinery are complete
(100%); downstream critical-tame and Galerkin endpoint theorems are accounted
for separately.
