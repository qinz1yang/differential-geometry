# WindowedWitnessTransport

Chapter25 claim df8e0f7e-95a1-4784-a691-52faf1f927d3. Source-only during
Chapter23's exclusive window through 2026-09-11 01:21UTC or explicit handback.
Initially unverified. This is the first step of the book's good-point derivative
proof for the actual WindowedModelWitness; earlier model bounds remain external.

Reuse WitnessTransport's actual open pullback metric, metric compatibility,
quantitative curvature difference and operator norm estimates. Do not convert
the windowed record to the stronger old ModelComparison: its all-domain
pullback identity and unrestricted time recursion are not supplied by the book
witness. Work on the same original embedding source instead.

On that open submanifold, the actual pullback metric tensor and the restricted
comparison field agree on the open model ball. The accepted closure-of-ball
and norm-on-closure lemmas identify all spatial covariant norms on the full
closed ball. Restriction naturality and metric compatibility then supply the
native metric jet bounds used by riemannDiff_gJet_le. No source time regularity,
assumed norm limit, new geometric hierarchy, or assumed source capture is needed
for this purely spatial curvature-transport step.

## Verified 2026-09-11

Final saved check 5 EMPTY (23.7s), named build 1 passed (33.8s), SHA256 48cfd9a5927a70b5e7fa0848f56208f9f980d5e251679bce8c82a328f57daa71. The fresh WindowedGoodPointAxioms1 audit covers all23 publics in20.8s:22 standard-only; only book_good_point_derivatives inherits the named earlier Chapter23 model-curvature obligation. Frozen completion receipt: E:/lean-tools/chapter25-book-20260910/windowed-good-point-completion.json. This supersedes the initial unverified status above.


For closure transport, give the actual subtype map explicitly and use a typed
calc equality with congrArg. A bare rewrite printed identical-looking closure
expressions but failed to align the open-submanifold coercions. Reuse the checked
OpenTensorJets declaration from the KappaSolutions namespace; do not duplicate
its restriction naturality proof. The source SigmaCompactSpace assumption was
unnecessary and removed from this transport file's public declarations.
