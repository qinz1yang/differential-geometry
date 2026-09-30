# Recognition from open segment interiors

This layer proves four theorems in `SegmentConcatenation.lean` and
`IntervalRecognition.lean`, both under `Topology/MetricSpace`.
It finishes the metric endpoint adapter and the interior/endpoint
dichotomy for ALR05 under the explicit open-segment-interior premise.
It does not prove that premise from Alexandrov comparison and dimension.

* Any supplied constant-speed minimizing segment on [0,1] admits an
  isometric parameterization on [0,d(x,y)], with the same endpoints.
  Coincident endpoints are included. Continuity is not an extra input
  because it follows from the distance identity.
* Two actual isometric segments of lengths A,B>=0 concatenate to an
  isometric segment of length A+B when their shared endpoint agrees
  and the outer endpoints have distance A+B. The conclusion preserves
  EVERY point of both supplied segments, including their junction.
  Both zero-length cases are allowed.
* In a geodesic metric space, metric endpoint betweenness
  (d(x,p)+d(p,y)=d(x,y) implies x=p or y=p) is equivalent to p lying
  in the interior of no isometric minimizing segment. The reverse
  implication constructs the concatenated segment; it is not assumed.
* In any nontrivial geodesic metric space whose isometric segment
  interiors are open, every p has some r>0 and an actual pointed
  isometry (-r,r) or [0,r) onto the ambient ball B(p,r), with its
  restricted metric. The radius and model are chosen for each p.

No completeness, properness, dimension or curvature hypothesis is
required for these metric implications. Nontriviality in the fourth
theorem is essential: the singleton case is treated separately in
AC46. There is no uniform recognition radius or global classification.

## Source and proof

The source body and versions are those checked for
[the preceding segment-neighborhood layer](segment_neighborhood.md):
AKP archived Theorem15.18 (printed/PDF238), pinned `dim.tex` lines874–951,
and blueprint207A ALR02–ALR05. The source's no-interior endpoint condition
is now related by a proved equivalence to the earlier metric condition.
The elementary rescaling and concatenation adapters are direct triangle-
inequality arguments, not claimed imports of an uninspected source result.
The concatenation proof bounds cross-piece distances above through the
junction and below through the outer endpoints. This forces equality.
The final theorem makes the literal interior/noninterior case split
and invokes the previously proved pointed charts on the same space.

The general source claim still needs the rank/dimension and local
distance-coordinate producer (ALR01 and AC19–AC27), or another proved
route supplying open segment interiors. AC46 from curvature/dimension,
AC47 complete-model classification, and their full geometric consumers
remain open. No Riemannian/PC migration interface is changed.

## Checks

The combined manifest gate, silent source-copy declaration linters,
degenerate-segment and junction-preservation consumers, and all public
axiom closures are recorded in the accompanying evidence and review.
Only scoped builds are asserted; the migrated PC root is not built.
Blueprint207 is unchanged and its separate historical-path audit
remains unsuccessful.
