# PointedRiemannian

Source used: MSM135 Chapter 3, especially Theorem 3.9 and the complete pointed Riemannian manifold hypotheses.

Introduced definitions: `PointedRiemannianManifold`, `PointedRiemannianSeq`, `PointedRiemannianSeq.basepoint`, `PointedRiemannianSeq.subseq`, `MetricComplete`, and `SeqMetricComplete`.

Design note: `MetricComplete` is no longer an axiom. It uses Mathlib's `EMetricSpace.ofRiemannianMetric` for the stored smooth Riemannian metric, then states `CompleteSpace` for that induced uniform structure.

Reason for the file split: the concrete Riemannian-emetric completeness predicate elaborates cleanly below the Ricci-flow and curvature imports. `Basic.lean` imports this file and then defines the flow-level data.

Verification: passed.

## 2026-06-30

Added `MetricComplete.complete`, the direct projection from the pointed
Riemannian completeness predicate to the active `CompleteSpace` field used by
Step-C `CenterInput` packages.  This avoids re-unfolding `MetricComplete` at
each center-of-mass consumer.

Attempted but did not keep a stored-metric `enorm` projection here.  Importing
the tangent norm comparison layer into this foundational pointed file perturbed
instance synthesis in the existing `MetricComplete` definition, so that norm
bridge should live in a higher Step-C/Hopf--Rinow consumer file that already
imports the Riemannian norm comparison API.

Verification status: focused check and targeted module build passed; axiom
check for the new projection uses only the usual project axioms.

## 2026-07-08

Added `SeqMetricComplete.subseq`, the D6-facing reindexing wrapper for
sequence completeness after Step A/D diagonal subsequences.  This is endpoint
input threading only; it does not prove the conditional Theorem 3.9 endpoint.

Verification passed.

## 2026-07-10

Added `PointedRiemannianManifold.repoint` and
`PointedRiemannianSeq.repoint`.  They change only the stored basepoint while
preserving the carrier, topology, smooth structure, metric, and bundle data
definitionally.  This is the D6-facing representation for comparison-map
sequences whose transported centers agree propositionally with the original
member basepoints.

Focused verification and the targeted module refresh passed.
