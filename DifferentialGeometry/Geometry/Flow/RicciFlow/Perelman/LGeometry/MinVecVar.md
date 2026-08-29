# MinVecVar

## Purpose

This file is the varying-terminal compactness producer for regularized
L-geodesic initial vectors. It turns a common action bound for canonical rays
ending at square-root times `B n` in one positive compact interval into
boundedness of `Set.range Z` in the fixed tangent space at the initial point.

## Mathematical content

The public theorem `lRegInit_var` assumes

- `0 < eps`, `eps <= B n`, and `B n <= R` for every `n`;
- regularity of the backward-time slab `[T - R^2, T]`;
- `B n` belongs to the regularized domain for the initial tangent `Z n`;
- the full regularized action up to `B n` is at most one common number `A`.

Compactness supplies common scalar-gradient and Ricci quadratic bounds on the
slab and a common lower bound `Cp` for the scalar part of the regularized
Lagrangian. For each ray, the action estimate gives the common kinetic budget

`integral speed^2 <= 2 * (A + |Cp| * R)`.

The single-ray Gronwall estimate then bounds
`4 * eps * g_T(Z n, Z n)` by one expression independent of `n`. Pointwise
metric coercivity at `(T, x)` converts that bound into a norm ball containing
the whole range.

The proof is split into three private declarations so elaboration does not have
to process the entire analytic chain in one large theorem:

- raywise integrability of kinetic and Lagrangian terms;
- action-to-kinetic conversion followed by the initial metric estimate;
- metric coercivity followed by bornological boundedness.

Only the moving-metric scalar helpers locally disable the alternate tangent
norm instances. The coercivity helper and the public bounded-range theorem keep
the canonical model norm instances; disabling them around `IsBounded (range Z)`
causes typeclass search to diverge.

## Native APIs reused

- `lGrad_bound` and `lRicci_bound` provide compact-slab constants;
- `lScalar_lower` provides the scalar-potential lower bound;
- `lRegKinetic_le` converts action to kinetic energy;
- `lRegInit_bdd` supplies the raywise Gronwall estimate;
- `gpCoerciveConst_le` and `gpCoerciveConst_pos` compare the terminal metric
  quadratic form with the ambient tangent norm.

No new geometric class, generalized flow object, or reference-tree dependency
is introduced.

## Verification

Focused verification is GREEN. Static hygiene is clean: there are no
`sorry`/`admit` placeholders or reference-tree imports, and the only public
name, `lRegInit_var`, is within the twenty-character limit.

## Frontier and progress

After this producer is GREEN, the next exact consumer is the minimizing-vector
subsequence step used in the cut-alternative compactness argument. This file
does not itself prove stability of minimizers or the cut alternative.

- `redVolume_anti`: 0% (not stated or proved here).
- `lCut_alt`: 0% (not stated or proved here).
- Varying-terminal initial-vector boundedness producer: 100% and verified.
- Dedicated fixed-manifold L-geometry machinery: about 94%; the remaining cut
  and reduced-volume endpoints are separate mathematical frontiers.
- Generic reused compactness, metric, integration, and ODE infrastructure:
  100% for this producer.
- Whole P2/Perelman program: below 1%; this is one compactness input, not an
  endpoint theorem.
