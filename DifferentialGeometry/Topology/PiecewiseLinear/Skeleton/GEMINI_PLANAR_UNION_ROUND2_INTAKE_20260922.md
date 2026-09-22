# Gemini planar union, round two: worker report intake

Date: 2026-09-22. **Worker evidence only; independent acceptance DEFERRED.**
The owner asked to split and record the supplied materials without interrupting processes.
This intake neither changes the active batch nor requests another worker pass. The lead did
not compile, audit, edit Lean source, register imports or replace any skeleton proof for it.
`../FREE_INPUTS.md` remains the sole acceptance ledger and is unchanged.

Source attachment:
`C:\Users\liao9\.codex\attachments\3921167a-ca9b-46d7-89b2-7dd99038e29a\Pasted text.txt`.
SHA256: `3A48750D1F847D5875A358A3AEE85679114C6A25B9939084053B39BB79ABA5FF`.
The transcript follows
[the second-round handoff](HANDOFF_GEMINI_PLANAR_UNION_ROUND2_20260922.md).
The later [continuous batch](GEMINI_BATCH.md) remains the active operating instruction.

## Reported source delivery

The hashes below identify the worker's reported delivery, not a lead-verified current
checkout or an immutable acceptance checkpoint. The active worker may since have edited
these files. Preserve the distinction when recovering receipts for a later batch review.

| Reported file, relative to `DifferentialGeometry/Topology/` | Reported SHA256 |
|---|---|
| `PlanarJordan/DiskUnion.lean` | `9CDC178458F7389057739B6A321042CEAB4CEB38907108CC19C0E5E7865047B5` |
| `PiecewiseLinear/PlanarCellUnion.lean` | `26A6E34F99CE1700FB21BDF241B63F00CBBD3B494C7E77DB1D3343D0736A525E` |

The worker reports these new `DiskUnion` results:

- `isJordanCurve_frontier_of_homeomorphClosedBall`;
- `interior_eq_inside_frontier_of_homeomorphClosedBall`;
- `closure_inside_frontier_eq_of_homeomorphClosedBall`;
- `isTopologicalCell_union_of_subset`;
- `isTopologicalCell_union_of_subset_right`;
- `subset_of_inter_subset_interior`.

The last is described in the report as a containment result when a nonempty intersection
lies in an interior. Its full Lean signature, including which interior and all hypotheses,
must be inspected at acceptance; the prose paraphrase is not a replacement for that type.

The `PlanarCellUnion` addition is reported with this complete interface:

```lean
theorem exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion
    (hdiskUnion : ∀ {A B : Set (EuclideanSpace ℝ (Fin 2))},
      IsTopologicalCell 2 A → IsTopologicalCell 2 B → IsTopologicalCell 2 (A ∩ B) →
      IsTopologicalCell 2 (A ∪ B))
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)}
    {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsPlanarCellChain P D Dint) (j : Fin 2) :
    ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧
        Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint
```

The report says its proof consumes `hc.overlap` through exact intersection projection,
transports the union cell back to three dimensions, and applies the accepted intrinsic
interior monotonicity theorem. This is a **conditional consumer** of `hdiskUnion`. The
report's phrase "complete Producer architecture" does not establish a producer for that
input or close the frozen endpoint, whose type does not receive it. This classification
follows from the displayed input; no full source audit or rejection of the helper proof
has been performed in this intake. Entry 10 / G001 remains OPEN pending an actual producer.

## Reported self-checks

The worker used private lane d, token `claude-agent-d-20260919`, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`, through the shared preparer/checker.
The transcript includes iterative module checks (tasks 303, 313, 319, 325, 331 and 343)
and a three-module audit (task 351). It reports:

- `DiskUnion` and `PlanarCellUnion`: exit code 0, zero diagnostic lines;
- `AuditGeminiPlanarCellUnion.lean`: exit code 0, zero diagnostic lines;
- all non-automatic declarations of `TopologicalCellInterior`, `PlanarCellUnion` and
  `DiskUnion` audited with `Lean.collectAxioms`, allowing only `propext`, `Classical.choice`
  and `Quot.sound`, with no `sorryAx`;
- thirteen standard linters passing and source lines at most 100 characters;
- a round-two receipt appended to `GEMINI_PLANAR_UNION_LOG.md`.

These are transcribed worker claims. This lead intake does not certify the audit program,
source/olean freshness, module coverage or the actual receipts. A foundational axiom
closure of the conditional consumer alone would still not supply its missing input.
The active worker logs and checkpoint script are left untouched.

## Exact remaining theorem and suggested continuation

The worker explicitly leaves the following general plane theorem unproved:

```lean
theorem isTopologicalCell_union_of_isTopologicalCell_inter
    {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : Nonempty (A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (hB : Nonempty (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (hAB : Nonempty ((A ∩ B) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    Nonempty ((A ∪ B) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
```

Containment cases and standard rectangle fixtures do not prove this statement for arbitrary
topological disks with possibly infinite common boundaries. The proposed relative matching
route, split into five deferred work packages, is recorded separately in
[consult BE](../consult/BE-planar-disk-union-relative-boundary-design-digest.md).
That advice was given for mirror `3b6b29fb`; it is not a review of the worker hashes above.

Later batch acceptance should recover exact source snapshots and receipts, compare the
already accepted APIs and frozen endpoint, and inspect the new proofs and their complete
dependency closure. New imports and any proof/ledger integration follow that gate.
Nothing in this record grants completion, new interface assumptions or a queue change.
