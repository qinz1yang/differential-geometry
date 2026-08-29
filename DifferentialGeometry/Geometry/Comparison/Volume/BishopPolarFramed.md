# BishopPolarFramed

## Origin normalization

`framedDens_zero` gives the exact origin value of the framed-coordinate
density: the square root of the determinant of the Gram matrix of
`chartModelBasis E`. This is a fixed positive model-space constant,
independent of the metric and base point.

The tempting value-one statement is false for the present API.
`framedMetric_zero` identifies the pulled-back metric with the given inner
product on `E`, but `chartModelBasis` is transported through `toEuclidean`,
which is a continuous linear equivalence rather than an isometry. Thus this
basis is not generally orthonormal. The failed value-one proof reduced
exactly to the unsupported identity

```lean
inner Real (chartModelBasis E i) (chartModelBasis E j) =
  (1 : Matrix _ _ Real) i j.
```

The nonunit constant cancels canonically against `modelHaar`. If `b` is
`chartModelBasis E` and `e` is `stdOrthonormalBasis Real E`, the Gram
determinant calculation identifies the density constant with `|e.det b|`.
`Module.Basis.det_smul_addHaar e b` then gives the measure identity directly:

```lean
ENNReal.ofReal (paramDensity g (framedExpDiffeo g p) 0) • modelHaar = volume.
```

This is `framedDens_haar`. Evaluating the measure identity on the unit ball
gives the small-ball normalization without any inverse-det algebra. It is the
same native change-of-basis mechanism used by `expJac_normal_int` in
`SegmentMeasure`; no compatibility hypothesis or consumer wrapper is needed.

Focused verification passed, and the explicitly named module refresh completed
successfully. The exported normalization is ready for downstream use.

## Normal-frame Haar bridge

`normalHaar_eq` is the measure-level bridge needed to remove the
chart-dependent angular factor from segment-polar comparison. It states that
the pole value of `normalChartDensity`, multiplying `modelHaar`, is exactly the
pushforward of canonical volume by `normalFrame`.

The proof deliberately reuses the existing normalization route. The
origin-density comparison from `frame_gram_change` identifies the framed pole
density with the normal pole density times the absolute basis determinant.
`Module.Basis.det_smul_addHaar` cancels that determinant, while
`Module.Basis.map_addHaar` identifies the normal-frame pushforward. Finally,
`framedDens_haar` supplies the already verified framed normalization. This is
the same basis-change mechanism used by `expJac_normal_int`; no curvature,
completeness, or metric-norm hypothesis is added.

The initial source inherited an unnecessarily strong analytic
`IsManifold I ω M` section binder. The file-level binder was weakened to the
smooth, notation-free
`IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M` assumption used by the imported
normal-chart machinery. Both bare `∞` and `(∞ : WithTop ℕ∞)` were intercepted
by the open ENNReal infinity notation before the expected grade type could
disambiguate them; each generalized check therefore stopped at the file-level
binder and all later diagnostics were cascades. The notation-free nested-top
form avoids that parser ambiguity. The corrected smooth-binder producer is now
warning-free focused green, and its explicitly named module refresh completed
successfully. A direct axiom audit of `normalHaar_eq` is still pending.

## Progress

The origin-normalization proof bodies, framed measure cancellation, and
`normalHaar_eq` are 100% source-written and focused-checked under the intended
smooth assumption; the named producer artifact is current. Direct axiom
confirmation for `normalHaar_eq` remains a separate pending item. This
normal-frame bridge completes the first missing normalization producer; the
separate Euclidean model-ball integral is now warning-free focused green with a
current named artifact, while its direct axiom audit remains pending. The
strict segment-ball consumer is not counted here. The origin-normalization
brick is roughly 5% of the dedicated
local Bishop--Gromov machinery; this normal-frame bridge is roughly 2% of that
machinery, and each remains well below 1% of the broader
Morgan--Tian/Poincare program. The P1a theorem-endpoint count remains 6/8;
this producer does not increment it.
