# Actual cone antipodes, coordinates and angular arcs

Nine public theorems and one actual path definition in three new leaves give exact metric consumers for the antipodal endpoint route. They preserve the existing cone, the original two angular points, the signed path, and any supplied cone arc. No geometric structure is replaced.

## Exact signed cone line

`Metric.ConeAntipodalLine` defines `twoRayPath a b`: the nonnegative ray is `mk(t,a)` and the negative ray is `mk(-t,b)`. Both branches meet at the existing tip at zero. The entire two rays are retained for all nonnegative radii. Its five theorems include the exact sum formula `dist(mk(r,a),mk(s,b))=r+s` when `pi<=dist(a,b)`, and the exact equivalence

`Isometry (twoRayPath a b) <-> pi <= dist a b`.

The generic base is an arbitrary metric space; no diameter, completeness, properness, curvature, or angular segment premise is needed. The greater-than-pi case is intentional because the existing cone metric caps angular distances at pi. In an actual completed direction space, its already proved diameter bound specializes the criterion to equality pi. The reverse implication recovers the capped angle from the actual path values at1 and-1; it is not a merely sufficient line construction.

## Canonical coordinate and equator

`Comparison.ConeLineCoordinate` proves, for the SAME actual signed path and every nonnegative radius r,

`lineCoordinate(twoRayPath a b)(mk(r,u)) = r*cos(min(pi,dist(a,u)))`.

This uses exactly its original values at0 and1 and the accepted squared-distance coordinate definition. The sign is oriented toward the original positive pole a. The formula legitimately does not need an antipodality premise: that squared-distance coordinate is defined for any such path; the separate line criterion supplies the isometry when needed. For strictly positive r, its zero locus is equivalent to the ORIGINAL uncapped angular distance `dist(a,u)=pi/2`. No diameter bound is needed for this equivalence, because a capped value pi cannot have cosine zero. At radius0 the coordinate always vanishes, so positivity is explicit and tested.

## Supplied cone arc to angular segment

`Metric.ConeArcDirections` first recovers an angle theta in[0,pi] from a fixed-positive-radius exact squared chord equation when the actual base distance is at mostpi. Its second theorem takes ONE supplied curve f:[0,1]->Cone(Y), its actual endpoints mk(r,a),mk(r,b), constant radius r>0, and its exact pair-distance law

`dist(f(s),f(t))^2 = 2*r^2*(1-cos(dist(a,b)*dist(s,t)))`.

Under the explicit base diameter bound pi, it returns a continuous exact-speed segment g in Y with the SAME endpoints and `f(t)=mk(r,g(t))` for EVERY original parameter. The positive-radius cone representation supplies each direction uniquely, cosine injectivity on[0,pi] supplies its distance formula, and that formula proves continuity. No prior continuity of f, base geodesicity, properness, completeness or curvature is required. The theorem does not construct its input arc.

## Sources, normalization and remaining implication

KLP archived v1 July14 2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`: cone definition/Exercise3.2 printed36/PDF38 and semisolution129/PDF131; Exercise5.8 printed54/PDF56 and full semisolution133-134/PDF135-136; Exercise6.20(c) printed69/PDF71 and full semisolution138/PDF140. Root and independent reviewers read the actual passages as recorded. The existing cone conventions, actual direction definitions, and retained author/source corrections remain unchanged. No new external errata retrieval is claimed.

The source's cone/base curvature equivalence assumes a complete geodesic base and retains diameter<=pi; these elementary metric leaves do not claim that equivalence. The source's full antipodal angular-segment argument additionally produces a meridian through a NONEMPTY transverse suspension factor after splitting. These leaves establish exact prerequisites and an arc consumer, not that missing existence step. A dimension upper bound with n>=2 cannot by itself supply the source's actual dimension>1 nondegeneracy: the real line also satisfies that upper bound. This milestone does not assert all-pairs angular geodesicity, a produced transverse factor, a dimension equality, or a full spherical-suspension theorem.

Mathlib revision remains c55e6e786f49471c72fbddbec5415808896aec1e. Blueprint207 and migration interfaces remain unchanged. No changing PC interface is inspected or bound.

## Concrete checks and evidence scope

Ten NEW tests cover: an unbounded angular-base cap retaining both rays; a strict-below-pi nonline; actual real tangent antipodes with their entire original rays; actual translated-plane representatives with unequal domain lengths; exact equator/cap/intermediate-cosine/zero-radius coordinates; the original oblique-plane coordinate at every radius; a radius2 arc spanning[0,pi] with pointwise recovery of the original parameterized direction; coincident endpoints; zero-radius failure of angle recovery; and above-cap failure of uncapped distance recovery.

The four earlier real/plane fixture bodies are retained once and are not counted as new tests. Twenty explicit canonical-import reports cover all ten public production declarations (nine theorems and the one definition) and these ten new tests. Frozen implementation, root and independent peer records distinguish actual compiler evidence from read-only review.

The 443-module shared gate checks 2,125 owned declarations in 3,281 jobs. Its observed increment is 12 owned declarations, comprising 10 declared public declarations (nine theorems and one definition) and 2 compiler-generated declarations. Ten new concrete regressions and twenty canonical-import standard-axiom reports pass, with silent selected lint. The separate unchanged blueprint static audit remains pending due to historical iCloud input downloads; no static pass is claimed. Compiler-generated increments are calculated from the actual owned-declaration delta over verified milestone124 minus the ten parsed source declarations. The definition is counted as a definition, not as a theorem. Earlier mathematical leaves remain unchanged.

No full meridian-existence theorem, antipodal direction geodesicity, sharp packing, automatic Euclidean recognition, or completion of Chapters3-4 is claimed here.
