# AC32: first-hit finite packing transport

Seven public theorems and one definition in three leaves prove AC32 with
its exact non-strict packing convention. Assume actual almost-short curves,
one curvature-minus-one comparison domain Omega, q in Omega, B(q,rho)
contained in Omega, and W contained in Omega with all q-distances in [a,D],
where 0<a<=D. For 0<t<1 and tD<rho, every epsilon-separated finite set in
W has an actual image finite set in B(q,rho), with the SAME cardinality and
separation at least ((tD/sinh D)/2)*epsilon.

The map uses the accepted first-hit point on an almost-short curve to each
source point, with the one uniform defect tolerance supplied by AC31. Its
radial distance is exactly t times the original radial distance. The lower
estimate is proved only for pairs at least epsilon apart. In fact, classical
choice defines this map on the whole W; this slightly stronger intermediate
statement does not assert continuity, a global Lipschitz bound, or a lower
bound for closer pairs. The finite-set conclusion follows by restriction.
The curve may leave Omega after its first-hit point; only the five actual
comparison points must belong to Omega. No completeness, compactness or
minimizing-geodesic premise is inserted.

`Metric.finitePackingNumber epsilon W` is the ENat supremum of cardinalities
of finite subsets with epsilon<=dist on distinct pairs, exactly the blueprint
AC16 convention. The new general finite-image theorem transfers this
supremum without a finiteness assumption on its value, giving the literal
AC32 packing inequality. Mathlib's `Metric.IsSeparated` instead uses strict
separation epsilon<edist (MetricSeparated.lean44), and its packingNumber
(CoveringNumbers.lean83–84) uses that predicate. The project definition keeps
the required non-strict convention explicit; no equality to Mathlib's
strict packing number is claimed.

Blueprint207A AC32 full statement/proof, lines3681–3720, and AC33's consumer
were reread. BGP6.3 and BBI10.8.20/correction checks from AC30–31 are reused.
The accepted AlmostRadialPoint.lean first-hit and variation proof was read
in full and reused unchanged. The new geometric construction supplies the
finite almost-short-path step requested by BBI, at the project's actual
curvature-minus-one constants. The strict/non-strict Mathlib comparison was
checked against c55e6e786f49471c72fbddbec5415808896aec1e source bodies.

AC33's polynomial packing and compactness at prescribed points, the
intrinsic AC29 adapter, global one-dimensional recognition and
curvature-to-covering production remain unfinished. Chapters3–4 are not
complete and no PC migration interface changed.
