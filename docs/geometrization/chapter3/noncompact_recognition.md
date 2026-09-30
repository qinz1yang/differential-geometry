# Noncompact one-dimensional recognition from original metric geometry

Four public theorems in three leaves close AC47's noncompact branch.
For ANY proper metric space with actual minimizing segments and noncompact
whole space, an isometric ray[0,infinity)->X is produced from every given
point. No curvature, dimension, uniqueness or nonbranching premise is used.
Noncompactness gives endpoints at distance>n+1. Their actual arclength
segments are clamped at their endpoints. For each t their values lie in the
compact closed t-ball. ONE ultrafilter extending the natural-number tail
filter is used for ALL parameters; compactness supplies pointwise limits.
For each pair s,t the clamped parameters eventually equal s,t exactly, so
the limit distances equal|s-t| and the origin is the specified point.

A separate properness theorem starts with a complete metric space, actual
arbitrarily short curves, a finite natural Hausdorff-dimension bound, and
local four-point comparison at ANY fixed parameter kappa>=0. The accepted
local compactness producer and Hopf-Rinow proof give properness. The
whole-space subtype is transported by its actual homeomorphism; no extra
properness, local compactness or minimizing-segment input is assumed.

The principal recognition theorem assumes completeness, the length condition,
global nonnegative four-point comparison, Hausdorff dimension<=1 and
noncompactness. It derives properness, actual minimizing segments, an
actual ray at the requested basepoint, segment openness and the signed
coordinate, and returns an ONTO pointed line or ray isometry. The ray
basepoint is a>=0 and is retained. An equivalent consumer accepts actual
minimizing segments instead of the length-curve condition. No ray or
endpoint is supplied by the caller. No singleton or compact case is
incorrectly forced into these alternatives.

Source reading: blueprint207A AC47 full4445-4501, and BBI(AMS2001) printed
46-53/PDF61-68. In particular Proposition2.5.17 printed48/PDF63, the full
Proposition2.5.22 proof printed49-50/PDF64-65, and Theorem2.5.28 with its
entire proof printed51-53/PDF66-68 were checked. BBI's diagonal compactness
argument is the mathematical reference; the Lean proof uses an explicit
single ultrafilter and exact distances instead. We do not attribute this
exact noncompact-ray formulation or ultrafilter implementation verbatim to
BBI. Its July6,2024 errata PDF1-3 were reread: finite metric qualifiers,
Arzela-Ascoli corrections, and the requirement that paths in2.5.28 be
naturally parametrized are retained. The construction uses actual isometric
arclength segments and finite-valued MetricSpace distances throughout.
Accepted CalibratedRay, SegmentConcatenation, VaryingLocalGeometry and
HopfRinow proof bodies were checked; their earlier source evidence remains.

The compact circle branch is still open; full AC47/AC48 and Chapters3-4 are
not complete. No migrated PC interface or earlier mathematical leaf changes.
Blueprint207 is unchanged.
