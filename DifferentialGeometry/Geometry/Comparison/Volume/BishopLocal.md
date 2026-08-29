# BishopLocal

## 2026-08-27: small-ball pole-density normalization

### Status

`exists_ball_ratio` states the honest generic small-ball comparison.  For each
positive relative error it exposes the positive constant

```text
c = paramDensity g (framedExpDiffeo g p) 0
```

and, below some positive radius, bounds intrinsic ball volume between the
`(1 - epsilon)c` and `(1 + epsilon)c` multiples of the scaled model-Haar unit
ball volume.  The statement has no Ricci-curvature assumption and uses only the
complete connected Riemannian hypotheses already needed to identify a small
intrinsic ball with its framed-normal image.

The proof uses positivity and continuity of `paramDensity`, a small model ball
inside the framed exponential source, parametrized change of variables, and
`modelHaar_ball`.  The lower bound is allowed to become trivial when
`epsilon >= 1`; this keeps the theorem valid for every positive error without
adding an unnecessary upper bound on `epsilon`.

The official lock-wrapper focused check passes without warnings after the
upstream framed-density/Haar identity was refreshed.  A direct axiom audit of
both new theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

### Scope and remaining endpoint

The value-one claim for the framed density is false for a generic model space:
`chartModelBasis` is not generally orthonormal.  This theorem therefore does
not claim Euclidean normalization.

`exists_euclid_ratio` is the downstream Euclidean endpoint.  It assumes
`0 < epsilon < 1`, applies `exists_ball_ratio`, and uses `framedDens_haar` to
cancel the pole density together with model Haar measure.  Its conclusion
squeezes intrinsic ball volume between the `(1 - epsilon)` and
`(1 + epsilon)` multiples of the Euclidean unit-ball volume scaled by `r^n`.
It is intentionally an epsilon endpoint rather than a new abstract limit API.
For the Morgan--Tian 9.66 use, choosing `epsilon < 1 / 2` supplies the one
small radius whose normalized volume is above half the Euclidean constant;
radius continuity then supplies the equality radius.  Morgan--Tian 9.56 uses
the already separate Euclidean upper bound and equality rigidity, so neither
consumer requires a public `Tendsto` adapter here.

Progress accounting: `exists_ball_ratio` and `exists_euclid_ratio` are each
100% complete, and their dedicated small-ball normalization machinery is 100%.
The broader P1a project-used endpoint set is approximately 60% complete: local
compact-closure comparison, radius continuity integration, and equality
rigidity remain separate work.  Full P0--P9 infrastructure remains
approximately 15--25%.
