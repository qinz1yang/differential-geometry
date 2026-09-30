# AC07 and AC29: local structure from original local comparison and dimension

Six public theorems in three leaves assemble the two AC07 producers. In a
complete metric space with actual length curves, an OPEN region U with
finite ambient Hausdorff-dimension bound and local curvature-1 four-point
neighborhoods is locally compact at every point. Each local comparison
neighborhood is intersected with U, preserving its dimension bound. The
accepted local rough-dimension/compact-ball theorem supplies a compact
closed ball contained in that neighborhood. Pulling such balls into the
subtype gives compact neighborhoods; the metric topology then gives the
actual LocallyCompactSpace U instance. No local compactness, global source
properness, chart radius or noncollapse is assumed. This also retains the
n=0 and singleton branches of the accepted rough-dimension theorem.

For a NONTRIVIAL complete length space, at any p in U and ANY prescribed
epsilon>0, local comparison at p and dimH U<=n, n>=1, produce q in
U intersect B(p,epsilon), a positive chart radius r with B(q,r) in that
same set, and a chart dimension1<=m<=n. The map is the ACTUAL centered
ambient distance-coordinate map with anchors in U. Its value at q is zero,
and its two Lipschitz bounds use the same explicit pairedChartDistortion n
from AC28. The new bound1<=pairedChartDistortion n supplies AC07's stated
normalization. Neither the chart radius nor the neighborhood size is made
uniform; only distortion depends on n.

Both producers have explicit actual-intrinsic-metric consumers. Local
comparison in the constructed intrinsic metric of B(o,L) is transferred
back to ambient neighborhoods using the proved local metric equivalence.
The local compactness result then applies at every point. The nearby chart
consumer uses that transfer at the center only and retains all ambient
anchors and coordinate identities. Taking L=8R and epsilon=R/2 yields AC29's
stated nearby chart; no local Toponogov safeguard is used for this chart
step. Taking L=256R supplies the local-compactness and nearby-chart inputs
needed by the written ALG06/AC04 route.

Proof-route simplification: once local comparison is transferred to ambient
neighborhoods, global ambient completeness supplies every closed completeness
buffer required by AC28/AC33. Applying those already proved local theorems
in X avoids a further chart transport from a separate intrinsic carrier.
This uses the ORIGINAL ambient completeness assumption and keeps the same
ambient metric, anchors and dimension. It does not weaken the hypotheses or
assume whole-open-ball completeness. The intrinsic hypotheses and their
metric/topology parents are explicit in the consumer statements.

Sources checked: blueprint207A AC07 full2357-2377, AC29 full3508-3535 with
remarks3537-3544, and the retained AC13/AC28/AC33/AC17 source checks. Accepted
CenteredPairedChart, PairedChartDistortion, LocalRoughDimension and
RoughLocalCompactness bodies were reread. The relevant Mathlib compact-preimage,
weak-local-compactness and metric-neighborhood definitions/proofs were read.
Exact source hashes and locators accompany the update. The BBI/BGP curvature-zero
qualifications and pinned-source/errata distinctions remain those of the
existing proof records; no new general-curvature source formula is imported.

The remaining assembly is to pass from chart dimension m<=n to the fixed-n
net bound, then bind growing-region tails and the existing SAME-limit
extraction/comparison/dimension consumers. Full original-input MC18/AC41/ALG07
is not claimed yet. Global one-dimensional recognition and PC migration
bindings remain separate. Blueprint207 and previous mathematical leaves
are unchanged.
