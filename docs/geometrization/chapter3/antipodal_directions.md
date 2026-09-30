# Antipodal direction segments through the prescribed third direction

Five public theorems in three new leaves prove exact cone-tip angles and produce an actual antipodal angular segment through the SAME supplied third direction. Both original-geometry headlines retain the original point, actual completed directions, actual tangent cone, resulting segment and its two isometric pieces.

## Exact cone-tip angles and additivity

`Comparison.ConeComparisonAngle` first proves that the Euclidean comparison angle at the existing cone tip between `mk(r,a)` and `mk(s,b)` is exactly `min(pi,dist(a,b))`, for arbitrary strictly positive radii r and s. There is no equal-radius or diameter restriction. Positive radii are essential because the total Lean comparison-angle convention at a zero arm does not recover the source angle.

Its second theorem assumes actual diameter at most pi and actual global four-point comparison0 on the literal EuclideanCone(Y). For original poles a,b with dist(a,b)=pi and EVERY original c, it proves `dist(a,c)+dist(c,b)=pi`. The unit cone-tip quadruple supplies the upper bound, while the ordinary angular triangle inequality supplies the reverse. Endpoint choices c=a or c=b are allowed here. No direction, geodesic, splitting or dimension conclusion is assumed or produced by this helper.

## The same antipodal segment and its original pieces

`Comparison.ConeAntipodalGeodesic` takes that actual cone geometry, the diameter bound, actual constant-speed segments for all pairs at distance STRICTLY below pi, and an ORIGINAL third direction c distinct from the antipodal poles a,b. It returns one continuous `f:[0,1]->Y` with endpoints a,b and exact distance law `dist(f(s),f(t))=pi*dist(s,t)`, passing through c at `dist(a,c)/pi`.

The result retains the SAME two actual isometric maps `alpha:[0,dist(a,c)]->Y` and `beta:[0,dist(c,b)]->Y`, all four endpoints a,c,c,b, and pointwise identities `f(s/pi)=alpha(s)` and `f((dist(a,c)+t)/pi)=beta(t)` throughout both intervals. Exact additivity and distinctness force both lengths to be positive and below pi; the strict-pi premise is used only for these two pairs. Accepted metric concatenation preserves the pieces. There is no properness, compactness or completeness assumption on the generic base and no antipodal segment hidden in the hypotheses.

## Full original ambient and intrinsic geometric inputs

`Comparison.FiniteDimensionalAntipodalDirections` has two original-input producers. The ambient theorem takes a complete source metric space, global arbitrarily short continuous curves, open U, 1<=n, dimH(U)<=n, original local four-point comparison parameter1 on U, and q in U. Parameter1 here is the curvature -1 convention. The intrinsic version takes the corresponding original comparison on B(p,8R), with R>0 and EVERY q in that original open ball; q need not lie in its half-ball.

They derive actual HasAnglesAt q, strict-pi completed-direction segments and actual cone comparison0 on the SAME TangentCone(q), using the accepted original finite-dimensional producers. For the SAME original a,b,c in SpaceOfDirections(q), with dist(a,b)=pi and c distinct from both poles, they return the same full package above. Their pointwise piece identities are expressed directly on the original f domain: `pi*t=s -> f(t)=alpha(s)` and `pi*t=dist(a,c)+u -> f(t)=beta(u)` for every admissible original parameter. No clamped extension, replacement segment or target isometry is exposed.

Source properness, a complete open ball, a supplied compact direction package, a supplied tangent-CBB premise, or a desired angular-segment conclusion is not assumed. The source dimension upper bound is used through the established compactness and blowup producers; no dimension equality is inferred. The retained n>=1 hypothesis is the accepted strict-pi producer's contract, not a claim about the n=0 case.

## Source benchmark, alternative proof and remaining condition

KLP, archived v1 July14 2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`: actual cone formula, tangent definition and Exercise3.2 printed36/PDF38, its semisolution printed129/PDF131; Proposition3.3 and full proof printed36-37/PDF38-39; Exercise6.20(a)-(c) printed69/PDF71 and complete semisolution printed138/PDF140. The full splitting5.5 and cone5.8 passages were checked in the preceding cone-line audit. The frozen author and independent records distinguish the actual readings and compiler runs. Earlier compactness, actual-tangent blowup and strict-pi source checks are reused unchanged. Existing source/version and errata qualifications remain; no new external errata retrieval is claimed.

The source uses strict-pi geodesics followed by splitting and a spherical suspension over a NONEMPTY transverse space. This package instead proves a direct cone-tip four-point additivity statement and then concatenates actual short segments through an explicitly supplied third direction. This is a documented alternative argument, not a claim to implement the source suspension proof.

Existence of the required third direction remains separate. A Hausdorff upper bound, even n>=2, does not imply it: a real source also satisfies that bound but has just two completed directions. These theorems do not claim the source's LinDim>1 condition follows from the supplied upper bound, do not identify source/tangent/direction dimensions, and do not prove CBB1 or a full spherical-suspension theorem. They establish antipodal geodesicity for the supplied actual nondegenerate triple, not unconditional all-pairs geodesicity in every direction space.

Mathlib remains pinned to `c55e6e786f49471c72fbddbec5415808896aec1e`. Blueprint207 and migration interfaces remain unchanged. No changing PC interface is inspected or bound.

## Concrete checks and acceptance scope

Six new regressions cover arbitrary positive unequal cone radii, pi-capping and coincident directions; an actual zero-arm negative control; the actual translated plane's opposite/oblique original directions and unequal radii2,5; generic antipodal concatenation through the original oblique direction at the nonmidpoint arccos(-3/5)/pi with all piece values; the full ambient original-input headline; and the full intrinsic headline at dist(q,p)=3R outside the half-ball, retaining its entire output. The two earlier plane fixture bodies are included once and are not counted as new tests.

Eleven explicit canonical-import reports cover all five public production theorems and all six new tests. All checks distinguish temporary source elaboration, independent proof reading, canonical leaf checks, the shared owned-axiom gate and the separate blueprint static audit.

The 446-module shared gate checks 2,137 owned declarations in 3,284 jobs. Its observed increment is 12 owned declarations, comprising 5 declared public theorems and 7 compiler-generated declarations. Six new concrete regressions and eleven canonical-import standard-axiom reports pass, with silent selected lint. The separate blueprint static audit remains pending; no static pass is claimed. Its recorded status and latest completed failure are retained in the receipt. Compiler-generated increments are calculated from the actual owned-declaration delta over verified milestone125 minus the five parsed source declarations. A separately pending blueprint audit is recorded as pending and never upgraded to a pass without its actual completed success evidence. Earlier mathematical leaves remain unchanged.

No full KLP6.20(c), automatic third-direction existence, dimension equality, angular CBB1, unconditional all-pairs direction geodesicity, or completion of Chapters3-4 is claimed.
