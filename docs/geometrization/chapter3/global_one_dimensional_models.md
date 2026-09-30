# Global pointed one-dimensional model existence

Two public theorems in two leaves assemble the EXISTENCE part of AC47 for
original complete length geometry, with all actual metric models and
pointed conventions. The compact nontrivial theorem assumes actual
minimizing segments, nonnegative four-point comparison and Hausdorff
dimension<=1. It derives open segment interiors through AC46, chooses an
actual positive diameter segment, and checks its surjectivity. If it is
onto, its inverse is the interval isometry. Otherwise an actual exterior
point produces the opposite arc and genuine quotient-circle isometry.
Subtraction in AddCircle recenters the requested basepoint to zero.

The global theorem assumes ONLY a complete metric space, actual arbitrarily
short continuous curves in the original metric, global nonnegative
four-point comparison, dimH<=1 and a requested basepoint p. It returns an
ONTO isometry to one of:

* a singleton, represented canonically by EuclideanSpace R(Fin0), at0;
* the usual real line, with p at0;
* the closed ray[0,infinity), with p at a>=0;
* the closed interval[0,L], L>0, with p at a in[0,L];
* the actual normed quotient AddCircle L, L>0, with p at0.

The singleton is treated directly. In the compact nontrivial branch,
minimizing segments are produced from the length condition; in the
noncompact branch, properness and a ray are produced internally. No
properness, chart packet, endpoint, ray, splitting, model, parameter or
classification alternative is supplied by the caller. The interval and
ray heights are retained; circle and line recentering uses actual metric
isometries. The result is metric, with no inferred smooth structure.

Source reading: blueprint207A AC47 full4445-4501 and its pointed conventions;
accepted compact-diameter/circle and noncompact recognition proof bodies
and source records. Mathlib's actual translation isometries in Topology/
MetricSpace/IsometricSMul.lean145-173 were checked, especially divRight and
its generated additive subRight counterpart, before using circle recentering.
The archived/pinned AKP local recognition and BBI compactness/errata records
are retained unchanged. The explicit diameter construction is the alternative
proof decomposition recorded in the preceding milestones.

This closes existence of the five global pointed metric model types.
AC47's wording 'exactly one' also entails model-class exclusivity; uniqueness
of lengths and the pointed reflection convention require separate explicit
formal statements. Those are NOT claimed by this disjunction. Full AC48
product assembly is also still separate. Chapters3-4 and Geometrization are
not complete. Earlier leaves, blueprint207 and PC migration interfaces stay
unchanged.
