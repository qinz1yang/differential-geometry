# EdgeDifferenceEnergy

## Proved source facts

- `edgeCoeff_rfns` identifies the differentiated inverse-metric coefficient in
  the order-zero principal-arm integration-by-parts identity and bounds it by
  the pointwise first covariant derivative of the metric difference.  No
  moving-endpoint high-jet radius occurs.
- `edgeArm_resid_le` converts that coefficient estimate and the operator-norm
  `C⁰` radius into the cubic residual estimate `O(δ) ‖∇T‖²`.
- `edgeArm_energy_le` combines the exact integration-by-parts identity with the
  inverse-cometric slot bound.
- `edgePrincipal_half` absorbs the complete variable-cometric principal arm
  into the fixed connection Laplacian once
  `δ / (1 - δ) + C δ ≤ 1/2`.

These are source-complete implementations with no `sorry`, `admit`, axiom, or
opaque replacement.  A short-build-path focused check reached the source and
exposed only local normalization defects: explicit nonnegativity of the
assembled constant, pointwise evaluation of a negated section, and the
definitional identification of one `iteratedCovGrad` with `covGrad`.  Those
repairs are source-written.  The short-build-path focused check is proof-green;
the final warning-clean recheck also passed with exit code zero and no local
warnings after removing the redundant `change` tactic reported by the earlier
green run.

The first repair check cleared the constant and covariant-derivative goals and
left one dependent-function presentation issue: Lean did not simplify
`(-section) x` to the pointwise negation needed by the fibre-norm lemma.  The
proof now makes that pointwise form explicit with `change`; its focused recheck
closed every proof goal.  The final focused check is therefore exact GREEN,
with no remaining source diagnostics in this file.

The ordinary focused-check route cannot read the deepest exported import on
Windows because its canonical path is 263 characters.  The artifact itself is
present and readable through the repository's checked short-build junction;
this is a verification-path issue, not a missing theorem or analytic gap.

## Remaining boundary uniqueness work

The highest-order obstruction is now isolated and absorbed.  The next lemma is
the lower-order Ricci--DeTurck difference pairing estimate on the same fixed
carrier, using the checked Palatini and low-jet coefficient refolds.  It must
bound the remaining pairing by

`C ‖T‖² + (1/4) ‖∇T‖²`

without assuming a uniform high-Sobolev ball for an arbitrary smooth boundary
solution.  After this, Gronwall gives equality on a right-hand window and the
existing interior continuation handles the rest of the common interval.

## Honest completion accounting

- Exact endpoint `ricci_flow_forward_unique`: **0%** until its existing theorem
  is proved and checked.
- Boundary energy machinery: **about 70% source-complete**.  Principal
  absorption is implemented; the lower-order refold pairing and its insertion
  into the boundary continuation theorem remain.
