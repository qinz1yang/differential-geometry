# WitnessNormalizedTimeJets

Chapter25, book `lem:scn-model-witness-stability`. Source claim
`a5c81d0c-bd1c-451b-b864-201782ddf4fe`; SOURCE-WRITTEN, not yet checked.
Compiler/artifact ownership is recorded only in WORKING_STATUS.md.

Use one genuine unnormalized tensor tower and the exact coefficients
`Q * (Q inverse)^q` under `s -> t + s/Q`. The same fixed partial embedding
and cutoff remain in use. A separate comparison identity identifies its
actual error tower with any old metric-comparison recursion on the same
closed time set. Neither strict bounds nor their continuity are premises
of the tower construction. They remain the next openness obligation.

Reuse the native tensor section operations, endpoint chain rule and
`derivWithin_tower_eq_of_genuine`; do not change the foreign time-jet file.
The general affine chain has the same proof mechanism as the checked
Chapter23 backward-to-forward change, with its sign and translation removed.
No initial-endpoint regularity or arbitrary-interval smoothness is inferred.

Iteration finding: `simpa only` on the scalar affine derivative and the
fiber-valued derivative produced incompatible-looking module/topology paths.
Binding the genuine derivative and using `exact hd` checks the original
native proposition directly; no topology instance or mathematical assumption
was changed. Check2 had no proof errors, only three unused-section warnings;
those unnecessary hypotheses are removed before final acceptance.

The zeroth intrinsic error norm also supplies both quadratic metric bounds
via native `abs_apply_le_norm0S` with two equal slots. This avoids assuming
metric equivalence independently when the perturbed comparison is assembled.

Accepted receipts: E:/lean-tools/chapter25-book-20260910/witness-normalized-openness-completion.json and the separate landing receipt. The13-public audit is standard-only; original Chapter25 slots closed by this support batch:0.
