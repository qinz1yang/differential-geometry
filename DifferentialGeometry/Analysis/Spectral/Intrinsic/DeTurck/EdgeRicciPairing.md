# EdgeRicciPairing

## Current source state

`EdgeRicciPairing.lean` is a new closed-edge Ricci algebra layer.  It uses
only public definitions and reproves, locally, the expansion which was
previously available only as the private
`order0KernelField_eq_arm_combination` theorem.

The source currently defines:

- `permCoeff`, the smooth covariant-slot permutation operator field;
- `ricciAAKer`, the sum of the six terms quadratic in the connection
  difference;
- `ricciDAKer`, the signed sum of the two terms linear in its covariant
  derivative;
- `ricciKer_split`, the exact kernel identity
  `linearizedRicciConnDiffOrder0KernelField = ricciAAKer + ricciDAKer`;
- `ricciAAArm` and `ricciDAArm`, their contractions by the genuine Ricci
  four-trace; and
- `ricciCoeff_split`, the corresponding split of
  `linearizedRicciConnDiffOrder0CoeffField`;
- `ricciDAFlux`, the surviving two-term single-moving-trace flux;
- `ricciFlux_rfns` and `ricciPart_rfns`, the public bound-facing fibre-norm
  interfaces which keep the internal alignment permutations hidden;
- `ricciDAG`, the covariant derivative of the lowered connection difference
  with slots ordered as `[r,p,u,v]`; and
- `ricciDAPart`, the same flux permuted into that slot order, together with
  component formulas for both carriers;
- `connRaise_eq`, reproved locally from public definitions, and
  `covConnRaise_eq`, which identifies the derivative tensor consumed by the
  Ricci kernel with the first-slot raise of `ricciDAG`; and
- `ricciDAG_pair`, the exact component bridge from the reconstructed
  `rs13ContrVec` to `ricciDAG`.
- `ricciDAOut_eval`, the complete signed eight-term component expansion of
  the derivative arm before cancellation;
- `ricciDAOut_red`, the symmetry reduction from eight scalar terms to three;
- `ricciDAOut_fin`, the final fully contracted two-arm formula;
- `ricciDA_pair`, the exact global pairing with the single-relative-trace
  partner; and
- `ricciDABase`, `ricciDAAdj`, and `ricciDA_green`, which move the covariant
  derivative from the lowered connection difference to that explicit partner
  by the closed-manifold Green identity.

The local algebra layer also records the two structural facts needed for the
remaining cancellation: the relative inverse-metric endomorphism is
`g`-self-adjoint, and `ricDAVec`, the reconstructed derivative of the
connection difference, is symmetric in its last two inputs.  A canonical orthonormal
expansion lemma converts evaluation of `W` on that reconstructed vector into
the rank-four `ricciDAG` component sum.  `ricSwap_l2` supplies the exact
rank-four first-slot-swap adjoint needed to feed that pairing into Green's
identity.

There is no `sorry`, `admit`, axiom, opaque replacement, or assumed pairing
bound in this file.  These declarations remain **source-level and
unverified**.  A first lock-aware focused check was started after the
coordinated `HarmonicPrincipal` build exited and its Lean process later exited
naturally, but the command wrapper timed out before completion and did not
return the final stdout/stderr.  It would be dishonest to classify that run
as green or failed.  Further verification is being serialized by the parent
lane; no overlapping Lean/Lake command was started.

## Corrected trace accounting

An earlier plan proposed lowering the derivative part to eight existing
`edgePairMono` terms.  That is false.  The mismatch is structural:

- `edgePairMono` uses `mvPairTraceOp`, a composition of two moving-metric
  double traces; its formal partner therefore contains `edgeRaise2 W` and
  scales as `m^-2` when `g = 1` and `gm = m` in dimension one;
- every monomial in `ricciCometricFourTraceCLM` contains exactly one
  moving-metric double trace, and therefore scales as `m^-1` in the same
  test.

Permutations and signs cannot change this homogeneity.  Consequently the
existing `edgePair_l2` theorem is not the outer formal adjoint of the Ricci
derivative arm.  The raw expansion is still `2 x 4 = 8` terms, but it needs a
mixed single-moving-trace/base-trace partner, not the two-moving-trace
partner.

## Signed cancellation and the intended partner

Write, in a `g`-orthonormal frame,

`D[p,u,v,r] = g((nabla_p A)(u,v), r)`

and let `L = g^-1 gm` denote the relative inverse-metric endomorphism in the
conventions of `fullRaisedEndoField`.  If `W` is symmetric, expansion of the
two derivative kernel terms through the four Ricci traces cancels four of the
eight scalar contributions pairwise.  The surviving expression is

`sum W[u,v] * W(L p,r) * (D[u,v,p,r] - D[p,u,v,r])`.

Thus the natural rank-four flux in raw `[p,u,v,r]` order is

`P[p,u,v,r] = W[p,u] * W(L v,r) - W[u,v] * W(L p,r)`.

This has exactly one relative inverse-metric insertion.  It is assembled from
the acyclic `pairProd4`, `pairSlot2` core and one fixed slot permutation.  The desired
Green-compatible carrier uses `[r,p,u,v]` order:

```text
ricciDAG[r,p,u,v] = D[p,u,v,r]
ricciDAPart[r,p,u,v] = W[p,u] W(L v,r) - W[u,v] W(L p,r).
```

In source this is implemented as the first-two-slot swap of
`covGrad (domDomCongrSection (finRotate 3) connDiffLoweredCc)` and the
`![1,2,3,0]` permutation of `ricciDAFlux`.  The concrete,
non-hypothetical identity is now present as

```lean
theorem ricciDA_pair ... (hWsymm : ...) :
  tensorL2Inner g 0 2 W
      (appCc g 2 2 (ricciDAArm g gm) W) =
    tensorL2Inner g 0 4 (ricciDAPart g gm W) (ricciDAG g gm)
```

The source theorem `ricciDA_green` then moves the outer slot swap to the
partner, swaps the global pairing, and applies
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence` directly to the
rotated lowered tensor.  The required lowering
bridge was private upstream, so this new, claimed file reproves it from the
public definitions as `connRaise_eq`; `covConnRaise_eq` then follows from the
public covariant-parallelism theorem for first-slot raising.  All these proofs
are currently source-level and still need a conclusive coordinated focused
Lean check.

## Honest progress

- Exact `ricci_flow_forward_unique`: **0%** until its existing theorem is
  proved and axiom-checked.
- Concrete Ricci order-zero kernel split: **source-complete, 0% Lean
  verified** pending a conclusive coordinated focused check.
- Ricci closed-edge pairing machinery: the true algebraic split, correct
  single-trace flux, exact component/global pairing, and Green step are all
  source-complete.  `EdgeRicciBound.lean` now contains the source-level
  uniform partner/divergence estimate.  The remaining adjacent analytic
  children are the quadratic arms, the Riemann-half refold contribution, and
  the signed Ricci order-one arm.
- `extends_of_rmBounded` and the Hamilton positive-Ricci endpoint are
  unchanged at theorem level.
