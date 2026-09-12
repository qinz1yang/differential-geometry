# SbrRetractionLaws.lean

Verified 2026-09-08 in the dev checkout. The actual level maps are jointly continuous, compose by taking the maximum level, and construct the native strong deformation retraction with explicit homotopy R_(t*s). This closes the compact-superlevel Sharafutdinov retraction theorem.

Empty focused output: 16.4s. Lint-clean named build: 18.7s.
Fresh external public axiom audit: 13s; all 5 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrRetractionLaws-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source work. Claim
`6460bac0-aaa9-4ddc-bfde-61f5a272cabc` retained. Source-written and
unverified; SbrRetraction and its actual ascent dependencies must be
checked and refreshed first. No verification of this leaf has run.

This finishes the structural assertions of the book's Sharafutdinov
retraction theorem, master05a.tex around lines 7950-8088, from the actual
maps constructed by SbrRetraction. The assumptions are exactly the
existing compact superlevel, global maximum, Lipschitz and intrinsic
geodesic-concavity data. No regularity of a pointwise selector is assumed.

Joint continuity follows from continuity of the fixed starting point's
time orbit and the uniform spatial one-Lipschitz bound. The metric
triangle inequality separates the two variations; this includes the
maximum level and the time at which a point starts moving.

For ordered levels s<=t, applying s after t fixes the already higher
point. Applying t after s agrees with the original ascent by actual
normalized-gradient curve uniqueness on [s,m]. Both original and
restarted time orbits have the required derivatives before m, equal
levels, and the same value at s. This includes s=m by the closed-interval
uniqueness theorem. The two orders give the public maximum-level law.

The final definition uses the existing native StrongDeformationRetract,
on the subtype of the actual nonnegative set with target its s-superlevel.
The actual retraction is R_s and the homotopy is R_(t*s). Its joint
continuity, endpoint values and fixed target points are proved from
the produced maps. Two public evaluation lemmas expose these formulas.

Five public declarations and one private ordered-composition helper.
Neither this source nor its still-pending dependency chain is a verified
retraction endpoint until empty focused, linted named-build and fresh
public axiom checks pass. Distinct Busemann-level surjectivity remains
the separate coray/uniqueness step.
