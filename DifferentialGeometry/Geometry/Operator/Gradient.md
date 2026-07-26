# Gradient

## 2026-07-17 chart norm identity

`grad_norm_sq_chart` records the squared metric norm of `gradFun` at a
manifold differentiability point as the inverse-Gram quadratic form in the
fully evaluated chart partial derivatives.  It is the representation-level
bridge needed to prove measurability of the norm of a nonsmooth Lipschitz
gradient without treating a varying tangent fiber as one global normed-space
codomain.

The proof reuses `gradChartLocal_eq_gradFun` and
`mfderiv_chartBasisVecFiber_of_mdifferentiableAt`; it does not duplicate the
long linear-algebra estimate in the following norm-bound theorem and adds no
new assumptions to consumers.

Focused verification and the targeted module build passed.  This producer is
complete.  The remaining work belongs in the intrinsic Sobolev layer: build a
chartwise measurable scalar representative, identify it almost everywhere by
this theorem, and assemble over the finite partition-of-unity measure
decomposition.
