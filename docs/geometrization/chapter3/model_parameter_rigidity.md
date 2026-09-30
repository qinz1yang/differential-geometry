# Endpoint invariance and pointed model parameter rigidity

Ten public theorems and one definition in three leaves establish the actual
metric invariants and pointed parameter conventions used in AC47. No curvature,
length-space or recognition input is needed for these explicit metric models.

Metric.IsEndpoint p abbreviates the previously used geometric condition:
if d(x,p)+d(p,y)=d(x,y), then x=p or y=p. This is a public predicate on the
original metric, not a supplied classification certificate. Its equivalence
under every onto isometry is proved. The real line and every positive-period
AddCircle have no such endpoints; Ici0 has precisely zero; Icc0L for L>=0
has precisely the points with coordinate0 or L. The degenerate L=0 case is
retained, while model classification itself uses L>0. On the circle, actual
quarter-period points give a minimizing segment through zero; translation
handles every basepoint. Its distances come from the existing quotient metric.

Every self-isometry of the closed ray is the identity. Consequently two ray
charts on the same source give exactly the same basepoint height. For an
onto isometry Icc0L -> Icc0M with L,M>0, L=M and its coordinates are EITHER
all t OR all L-t. A single orientation works for every point. Thus two segment
charts on the same source retain the basepoint coordinate up to precisely
that reflection. Finally, onto isometric positive-period circles have equal
circumferences. The proof compares actual antipodal distances in both
directions using the half-period norm bound.

Sources checked: blueprint207A AC47 full4445-4501, especially pointed/reflection
conventions and interval-isometry proof step; AC48 qualifications4532-4540;
the accepted SegmentConcatenation.lean endpoint equivalence and
HalfIntervalEndpoint.lean full bodies. The new predicate is exactly their
explicit endpoint hypothesis, with no retrospective changes. Mathlib
Analysis/Normed/Group/AddCircle.lean66-137 was read, including the norm bound,
actual antipodal norm and exact short-representative norm. Translation
isometries in Topology/MetricSpace/IsometricSMul.lean145-173 retain the earlier
source check at pinned revision c55e6e786f49471c72fbddbec5415808896aec1e.

These results prove parameter rigidity and the endpoint invariants. They do
not yet package the pairwise exclusion of all five types or the exactly-one
classification theorem; boundedness/noncompactness separation remains to be
joined. They make no smooth or approximate-map claim. Earlier leaves,
blueprint207 and migration interfaces are unchanged.
