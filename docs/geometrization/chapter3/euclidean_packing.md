# Euclidean packing and the compact-target bridge for AC33

Four public theorems in three new leaves supply AC33's quantitative grid
step and a separate compactness transfer helper. If m>0, B>=0, epsilon>0,
and a finite family in PiLp2(Fin m) has norm at most B and distinct points
at distance at least epsilon, its cardinality is at most
(1+4B*sqrt(m)/epsilon)^m. This is slightly stronger than the blueprint's
2+constant grid estimate; weakening to that estimate is immediate.

Each coordinate is labeled by Nat.floor((x_i+B)/h), h=epsilon/(2sqrt(m)).
It lies in Fin(floor(2B/h)+1). Equal labels force each coordinate difference
strictly below h, hence squared Euclidean distance at most epsilon^2/4,
contradicting separation. The proof treats endpoints of the coordinate
interval by their actual floor values, without discarding boundary points.
It allows an empty family and B=0; positive m and epsilon stay explicit.

A generic map with bounded norm B and lower distance constant K>0 gives
the finite-set bound (1+4B*sqrt(m)/(K*epsilon))^m. Its non-strict
finitePackingNumber is bounded by the natural floor of that real bound,
viewed in ENat, so finiteness is a proved conclusion. This theorem uses the
actual supplied map, with no open-image or manifold premise.

Separately, if every finite epsilon-separated source set transports to a
compact target with at least its cardinality and separation K*epsilon,
then the source is totally bounded. Accepted MC02 compact nets bound target
cardinalities and its finite maximal-net theorem supplies source nets.
No source completeness is assumed; local completeness will be used only
when a later consumer needs a compact closed ball.

Blueprint207A AC33 full proof3730–3768 and compactness consumer3769–3779
were reread. The BGP6.3/BBI10.8.20 readings and corrections from AC30–32
are reused. Mathlib c55e6e786f49471c72fbddbec5415808896aec1e: natural-floor
bounds and monotonicity in Algebra/Order/Floor/Semiring.lean35–98;
PiLp norm/metric square identities in Analysis/Normed/Lp/PiLp.lean787–806.
The accepted FiniteNets.lean compact-cover and separated-net cardinality
proofs were read and reused unchanged.

These are AC33's pure quantitative and compact-target ingredients. Their
geometric application at each prescribed point, rough-volume asymptotics,
the intrinsic adapter, global one-dimensional recognition and
curvature-to-covering production remain open. No full Chapters3–4 or
migration completion is claimed. The non-strict packing convention stays
unchanged; it is not silently replaced by Mathlib's strict packing number.
