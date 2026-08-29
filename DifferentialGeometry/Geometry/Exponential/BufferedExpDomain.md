# `BufferedExpDomain`

## Rejected intended producer

The requested public result was the following incomplete-ambient statement.

```lean
theorem frame_mem_expDom
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p x : M) {A r : Real}
    (hA : 0 <= A) (hr : 0 < r)
    (hx : edist p x <= ENNReal.ofReal A)
    (hcpt : IsCompact
      (Metric.closedEBall p (ENNReal.ofReal (A + r))))
    {z : E} (hz : ‖z‖ < r) :
    (normalFrame (I := I) g x z : TangentSpace I x) in
      expDomain (I := I) g x
```

This statement is **not valid for the live definition of `expDomain`**.  Compact
containment controls the intrinsic base geodesic but does not imply containment
in the source of the single chart centered at `x`.

## Reusable route already present

- `exists_isGeodesicOn_Ioo_at_velocity` supplies the local seed with the
  prescribed initial velocity.
- `isGeodesicOn_contMDiffOn_one` and `isGeodesicOn_speedSq_const` propagate the
  initial speed along every candidate extension.
- `curve_edist_le_speed_mul_time`, the triangle inequality, `normalFrame_sqrt`,
  and `hEnorm` put every candidate with endpoint below `B` in the compact
  buffered eball.
- `endpointCont_compact` / `geo_Ioo_extend_cpt` then continue such a base
  geodesic past every finite endpoint below `B`.
- A capped version of the existing Zorn proof for
  `isGeodesicOn_Ioi_of_endpointContinuation` would therefore produce an
  `IsGeodesicOn` curve on an open interval containing `0` and `1`.

For the base-geodesic continuation alone, the fixed radius `A + r` is
sufficient; a separate larger radius `R` is not required because the speed
inequality is strict.  That observation does not repair the raw `expDomain`
conclusion.

## Decisive fixed-chart obstruction

`expDomain` is defined through `MaximalGeodesicWitness`.  Its witness requires
`IsGeodesicOnWithInitial`, whose phase lift must solve the *fixed-chart* vector
field `geodesicVectorFieldChart g x` over the whole witness interval.  The live
source proves two decisive facts:

- `geodesicVectorFieldChart_eq_geodesicVectorField` identifies this vector
  field with the intrinsic geodesic vector field only while the lift's foot
  lies in `(chartAt H x).source`;
- `geodesicVectorFieldChart_eq_zero_of_notMem_source` makes the fixed-chart
  vector field zero once that foot lies outside the initial chart source.

A compact metric eball need not lie in `(chartAt H x).source`.  Consequently,
compact-eball containment alone cannot produce the fixed-chart integral lift
required by `MaximalGeodesicWitness`; for a nonzero geodesic that exits the
initial chart, the raw witness equation changes to the zero vector field.  The
requested `frame_mem_expDom` is therefore under-hypothesized and generally
false for the current representation, not merely blocked by a missing adapter.

Thus a capped base-geodesic Zorn proof would stop at the exact goal

```lean
IsGeodesicOnWithInitial (I := I) g gamma (Set.Ioo a0 B) x
  (normalFrame (I := I) g x z)
```

with only `IsGeodesicOn`, `ContinuousOn`, `gamma 0 = x`, and the prescribed
`mfderiv` available.  Even a general equation-to-phase-lift bridge cannot close
this goal without the extra hypothesis

```lean
forall t in Set.Ioo a0 B, gamma t in (chartAt H x).source
```

Adding that hypothesis would make the raw bridge plausible, but compact-ball
properness does not supply it and the resulting theorem would not cover the
Morgan--Tian local comparison consumer.  No theorem-shaped `sorry` and no
`.lean` source have been created.

## Smallest next design choice

There is no assumption-free `geoInit_of_eqn` producer to add: such a theorem is
false for the fixed-chart target.  A source-contained compatibility lemma could
honestly be stated next to `IsGeodesicOnWithInitial`, but it would have to expose
the chart-source hypothesis:

```lean
theorem geoInit_of_eqn
    (g : SmoothRiemannianMetric I M)
    {gamma : Real -> M} {J : Set Real} {p : M}
    {v : TangentSpace I p}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J) (h0 : 0 in J)
    (hgeo : IsGeodesicOn (I := I) g gamma J)
    (hcont : ContinuousOn gamma J)
    (hgamma0 : gamma 0 = p)
    (hvel : (mfderiv ... gamma 0 1 : E) = (v : E))
    (hsrc : forall t in J, gamma t in (chartAt H p).source) :
    IsGeodesicOnWithInitial (I := I) g gamma J p v
```

That local compatibility result does not advance the exact MT endpoint.  To
serve MT, the smallest mathematically honest next action is a design decision:
replace or generalize `MaximalGeodesicWitness`/`expDomain` so witnesses use the
global `geodesicVectorField` (with a chart-independent phase lift), then migrate
the raw exponential API.  This is a substantial foundational change touching
more than the exclusively claimed new file, so it requires explicit approval
and a dependency audit before implementation.

## Routes assessed

1. **Source-contained raw theorem.**  Add the explicit hypothesis that the
   whole relevant curve stays in `(chartAt H x).source`, then build the
   fixed-chart phase lift.  This is compatible with the live definition but
   does not follow from compact eball closure and therefore does not cover MT.
2. **Global witness/domain redesign.**  Make the canonical raw witness use the
   intrinsic global geodesic vector field, prove its chart-local realization,
   and redefine or generalize `expDomain` accordingly.  This is the smallest
   route that is mathematically faithful to the requested MT statement, but it
   is a substantial foundational API migration.
3. **Base-geodesic domain plus downstream migration.**  Introduce a domain
   defined by an open preconnected base curve satisfying `IsGeodesicOn` and the
   correct initial data, prove compact-buffer coverage there, and migrate every
   downstream raw exponential consumer.  This avoids the fixed-chart phase
   field but creates a second domain notion and a larger migration than route 2.

## Verification and project accounting

Verification has not started because the proposed public theorem is false for
the live raw domain.  There is no `sorry`, no new assumption, and no `.lean`
source.  P1b E1 remains unstated/unproved (0%); its checked CGT denominator and
compact-tail infrastructure are separate supporting machinery.  The requested
local raw-exp-domain producer remains 0%, and its honest replacement is now a
foundational design decision rather than a routine local proof.  P1b still has
0/2 exact Morgan--Tian endpoints; the broader P0--P9 program remains in the low
twenties percent range.
