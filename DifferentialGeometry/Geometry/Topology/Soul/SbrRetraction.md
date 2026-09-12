# SbrRetraction.lean

Verified 2026-09-08 in the dev checkout. Actual maximal ascents define the Sharafutdinov level map, with exact image/fixed points, nonexpansiveness, continuous time orbits and actual normalized-gradient right derivatives. The map is produced from the standing geometric data.

Empty focused output: 18.2s. Lint-clean named build: 20.7s.
Fresh external public axiom audit: 13.1s; all 11 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrRetraction-result3.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

Source-ready and frozen, 2026-09-08. No Lean, Lake, REPL, focused check,
artifact refresh or axiom audit was run for this leaf. Chapter23 owns
verification; the parent owns the pending dependency checks, registration,
artifacts and integration.

- Claim: `b159a2c4-e762-4f27-b3a4-9ce09c334e98`.
- Source: `DifferentialGeometry/Geometry/Topology/Soul/SbrRetraction.lean`.
- SHA256: `DD8F74B7C9ACEDEA859C54E00E011C809A68E10941354417EA7E230A278816FC`.
- Sole direct import: the frozen, source-ready `SbrMaximalFlow`.
- Public declarations: two definitions and nine theorems; two additional
  comparison helpers are private.

## Scope and inputs

This implements the actual level map and the first assertion of the
Sharafutdinov contraction theorem in the untracked root `master05a.tex`,
lines 7950–8088. Orbit continuity and the normalized right derivative are
retained for subsequent joint-continuity and semigroup arguments.

The natural inputs remain those of the actual maximal-ascent producer:
a complete boundaryless finite-dimensional Riemannian manifold of positive
dimension, an explicit smooth metric `g` and `IsMetricNorm g`, an actual
`LipschitzWith L F`, concavity along every native complete intrinsic
geodesic, compactness of the actual set `C = {z | 0 <= F z}`, and an
attained global maximum `m` of `F`. The upstream tangent-bundle Hausdorff
hypothesis remains explicit. No curve, local flow, derivative, support
field, contraction property or compatibility of choices is assumed.

## Actual definitions and public specifications

`selectedMaximalAscent` chooses the curve produced by
`exists_maximal_normalized_ascent_curve` from each point satisfying
`0 <= F x < m`, and uses the constant curve at every other point. Its
public `selectedMaximalAscent_spec` retains the complete producer output:
continuity on `[F x,m]`, the initial point, membership in `C`, exact
function levels, the actual nonzero generalized gradient and normalized
right derivative before `m`, and the quantitative Lipschitz estimates on
smaller closed intervals.

`sharafutdinovLevelMap s x` fixes `x` if `s <= F x`; otherwise it evaluates
that selected actual ascent at `s`. The public theorems are:

- `sharafutdinovLevelMap_of_le`: the target superlevel is fixed.
- `sharafutdinovLevelMap_eq_ascent`: on and above a submaximal point's
  initial level, the map agrees with its selected curve, including the
  joining time.
- `sharafutdinovLevelMap_level`: for `0 <= s <= m` and `x` in `C`,
  `F (R s x) = max (F x) s`.
- `sharafutdinovLevelMap_image`: `R s '' C = {z | s <= F z}`.
- `sharafutdinovLevelMap_mapsTo`: `R s` preserves `C`.
- `sharafutdinovLevelMap_lipschitzOnWith`: `LipschitzOnWith 1 (R s) C`.
- `sharafutdinovLevelMap_continuousOn_orbit`: each point of `C` has a
  continuous orbit on `[0,m]`, including the terminal level.
- `sharafutdinovLevelMap_hasMFDerivWithinAt_orbit`: whenever
  `F x <= t < m`, the actual generalized gradient at `R t x` is nonzero
  and the orbit has native right manifold derivative on `Ici t` equal to
  `toSpanSingleton` of that gradient divided by its metric squared length.

The functions are ambient total functions. Their geometric guarantees are
the stated interval and set restrictions; no geometric assertion is made
about the arbitrary curve values outside the produced intervals.

## Contraction argument and orbit regularity

Order the initial values as `F x <= F y` and use the book's three cases.
Both points are fixed when `s <= F x`. When `F x < s <= F y`, the actual
fixed-point comparison in `SbrFlowUniqueness` applies to the ascent from
`x` and the fixed point `y`. When `F y < s`, restrict the original
selected curves from `x` and `y` to the common interval `[F y,s]` and use
the actual two-curve comparison. The fixed-point comparison on
`[F x,F y]` then bounds their initial separation on that common interval.
This proof includes `F x = F y` and `s = m`; it requires only continuity
at the upper endpoint and right derivatives below it. It never replaces
the original curve by a separately selected restarted curve, so no
tail-compatibility assumption is hidden in the construction.

For a submaximal point, the time orbit equals
`selectedMaximalAscent x (max (F x) s)` on `[0,m]`; continuity follows by
composition. A maximum point has a constant orbit. At a time
`F x <= t < m`, equality with the selected ascent holds throughout
`Ici t`, including its center. Native manifold derivative congruence
therefore transfers the actual right derivative, even at `t = F x`.

## Review and remaining verification

A separate read-only static review checked the actual maximal-flow and
comparison signatures, endpoint restrictions, continuous composition and
congruence, and derivative congruence. It identified no concrete API or
proof-shape issue. This is not successful Lean elaboration. The source
contains no `sorry` or new axioms, but neither this leaf nor its full
current dependency chain has been verified in this source-only task.

The parent must check and refresh the frozen upstream chain before the
focused check and public axiom audit of this leaf. Joint continuity,
semigroup laws, strong deformation retraction, and surjectivity of maps
between distinct level sets remain outside this bounded leaf. The exact
image theorem here is the retraction onto a superlevel, not surjectivity
from one level set onto another.
