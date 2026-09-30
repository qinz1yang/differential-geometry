# Local comparison transfers to the actual intrinsic metric

Four public theorems in three leaves provide the ambient-to-intrinsic
local comparison input for ALG07. A continuous map that preserves all pairwise
distances on some neighborhood of the specified point pulls local four-point
comparison back to that point. Global injectivity and global isometry are
unnecessary. An open embedding with the same local metric property gives
an equivalence, using the already proved forward image theorem.

For the ACTUAL intrinsic metric of an open ball in an ambient length space,
local four-point comparison at each point is equivalent to local ambient
four-point comparison at its image. The proof uses radius(L-d(p,o))/8.
The inclusion is the proved open embedding; its nonexpansive bound puts the
intrinsic small ball inside the corresponding ambient closed ball, where
AC13 proves exact pairwise equality. Every intrinsic topology and metric
parent is explicit. No ambient completeness, local compactness, minimizing
segments or global curvature hypothesis is used in this equivalence.

For a complete ambient length space with locally compact B(o,256R), local
AMBIENT comparison near every point of that ball now yields actual ambient
four-point comparison on B(o,2R), by transferring to the actual intrinsic
metric and applying the preceding ALG06 result. This is an adapter for the
original local hypotheses; it does not assume local intrinsic comparison or
any auxiliary realization. Curvature is -kappa, kappa>=0 in this consumer.
The local metric equivalence itself is algebraic and does not need a sign
restriction. Local neighborhoods can vary from point to point.

Source bodies checked: blueprint207A AC13 lines2713-2755, ALG06 lines7536-7580,
ALG07 lines7582-7617, especially the explicit local metric/curvature transfer;
the accepted MetricTransfer, IntrinsicBallGeometry, IntrinsicBallTopology and
IntrinsicBufferComparison proof bodies. The existing pinned source and errata
records are reused for unchanged claims. No source convention identifies an
intrinsic metric merely from subspace topology: exact local distances are
proved. The precise source manifest distinguishes these proof-derived adapters
from source theorem statements.

ALG07's uniform covering producer and full original-hypothesis extraction
remain unfinished; this closes the local comparison-transfer input only.
Blueprint207 and previous mathematical leaves remain unchanged; no PC
migration-dependent interface is changed.
