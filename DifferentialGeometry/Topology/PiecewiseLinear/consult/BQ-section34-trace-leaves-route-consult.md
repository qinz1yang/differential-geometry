# BQ — route consult for the Section 34 trace leaves (for the owner's Codex)

Written by the lead on 2026-09-23. Codex may read the checkout directly and compile probes on its
own lease; the answer goes to `consult/BQ-section34-trace-leaves-codex-answer.md` (new file; no git
writes; no frozen statement edited). Use the six checks of `consult/REVIEW-TEMPLATE.md`,
concentrating on checks 4 and 6, and end with a reduction into named sub-leaves marked
SMALL / MEDIUM / NEW_THEORY with the tree modules each would use. About 1500 words plus Lean.

Objects (twins; do the compact one first, then say what changes in the manifold version):

1. `compactTrace_of_noOperation` in `Skeleton/Section34Compact.lean` (line 285): under the compact
   cut frame, graph frame and face-ball invariants `hinv`, if no face admits a compression
   (`Section34CompactCompression`) and no face admits a bigon slide (`Section34CompactBigonSlide`),
   then the family satisfies `Section34CompactTrace` (`Section34CompactVocabulary.lean` line 608:
   the trace of each face ball on its face torus is a finite family of circles, each crossing every
   incident splitting circle exactly once, the count `r σ` positive, the face-torus trace equality).
2. `section34Trace_of_noOperation` in `Skeleton/Section34Normalization.lean` (line 388) with
   `Section34Trace` (`Section34Frame.lean` line 791) and the neighbouring bridge leaf
   `section34TraceCircle_homologyMap_ne_zero` (line 404; not consumed by P6 any more — say whether
   it is still consumed by anything, checking the assemblies of `Section34Normalization`,
   `Section34Terminal` and the compact skeleton).

Prior analysis (the previous worker, `Skeleton/OPUS_FILL_LOG_C.md` lines 899–912): four missing
producers — (a) the trace `∂C_σ ∩ ∂N''` is a finite disjoint union of PL circles: now REAL,
`CrossingTraceCircles.lean` (accepted 2026-09-23; also `Section34FaceTorusCycle`: in a chart the
face torus is a combinatorial solid torus with PL torus frontier); (b) a trace circle that is zero
in `H₁` of the face torus bounds an innermost disk on the torus boundary off the other circles,
which would be an Operation 1 disk (PL Schoenflies on a PL torus; Moise 28.8 is not stated in the
tree — but `SphereInnermostDisk.lean`, `TorusCircleHomology.lean`, `TorusSubsurfaceCarrier.lean`,
`SeparatingPolygonDisk.lean`, `NonseparatingPolygonCarrier.lean`, `SolidTorusInteriorHomology.lean`
and `MaximalPolygonHomologyImage.lean` now exist: say exactly which part of 28.8 is still missing);
(c) with no bigon, a circle essential in the solid torus meets every incident splitting circle
exactly once (intersection numbers with meridian disks; `Section34CompactSplitDiskIntersection`,
`Section34CompactTraceArcs`, `Section34TraceArcs`, `Section34CompactIncidentEdges` may help: the
compact and non-compact P6 proofs already show that each trace circle meets each incident vertex
ball in one arc between consecutive marked points); (d) `0 < r σ` from the nonempty trace, which
the generator clause gives.

Questions: the exact remaining sub-leaves for (b) and (c) and their routes; whether the bigon
absence must be used through an intersection-number argument or through the innermost-bigon
disk (a circle meeting a splitting circle twice in the same direction bounds a bigon with it on
the torus — which `Section34CompactBigonSlide` then supplies, contradicting `hnb`); which parts
transfer verbatim between the compact and manifold versions; and whether
`section34TraceCircle_homologyMap_ne_zero` is dead (then the lead retires it) or still needed.
What is the single most likely surprise? Verdicts are evidence, not rulings; the lead verifies
against Lean.
