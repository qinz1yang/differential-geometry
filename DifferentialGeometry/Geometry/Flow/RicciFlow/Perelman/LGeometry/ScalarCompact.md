# ScalarCompact

## Scope

This module isolates the scalar-curvature part of the regularized L-action.
It uses the existing spacetime scalar continuity predicate and compactness of
the time-manifold product; it does not add a path structure or any
Ricci-flow-specific regularity assumption beyond scalar continuity.

## Results

- `lScalar_cont`: continuity along a continuous curve.
- `lScalar_int`: interval integrability obtained from that continuity.
- `lScalar_lower_cpt`: a uniform lower bound on a supplied compact target;
  ambient compactness is not required.
- `lScalar_tendsto_cpt`: convergence of scalar-potential integrals when the
  approximating curves share a supplied compact target; ambient compactness is
  not required.
- `lScalar_tendsto`: convergence of the scalar-potential interval integrals
  under uniform convergence of continuous curves.

The convergence proof obtains one common absolute bound from continuity on the
compact product and then applies interval dominated convergence. Thus
measurability and integrability are producers, not consumer hypotheses.

The convergence theorem needs only a `UniformSpace` on the target manifold;
neither a pseudometric nor a separate `T2Space` instance is used. Compactness is
needed only for the common scalar-potential bound and is omitted from the two
single-curve continuity/integrability declarations.

## Verification

Focused verification of the compact-target producers and the existing
declarations passes without warnings or placeholders. A shifted
producer was deliberately moved to the narrow `ScalarShift` module: keeping it
here pulled the unrelated top-level `NeZero (finrank E)` section context into
the declaration and caused a deterministic elaboration timeout.
