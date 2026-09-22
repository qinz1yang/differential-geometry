# Gemini continuation: prove the planar disk union

The later [GEMINI_BATCH.md](GEMINI_BATCH.md) authorizes continuous work across 101 frozen
proof candidates. Follow its scope and continuation rules rather than the stop-after-this-
round restriction below. This file remains the mathematical context for the current
planar-union attempt; do not reset that work.

The owner returned the first Gemini report. It supplies useful auxiliary mathematics but
does not prove entry 10. Continue the already authorized assignment; another plan approval
is unnecessary. Read this update before resuming the original
[handoff](HANDOFF_GEMINI_PLANAR_UNION_20260922.md). Acceptance belongs only to
`../FREE_INPUTS.md`; the Gemini log contains worker evidence, not acceptance counts.

## Workspace and ownership

Work only in `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.
`E:\differential-geometry-dev` and all its outputs are read-only. Follow root and PL
AGENTS.md, NAMING.md and STRUCTURE.md. Preserve unrelated dirty files. F remains on entry
15 and lease a; do not inspect or change its active crossing implementation for this task.

You may add `DifferentialGeometry/Topology/PlanarJordan/DiskUnion.lean`, extend
`DifferentialGeometry/Topology/PiecewiseLinear/PlanarCellUnion.lean` with the real producer,
and append to `Skeleton/GEMINI_PLANAR_UNION_LOG.md`. Preserve the accepted declarations in
`PlanarCellUnion` and `TopologicalCellInterior`; do not restore the discarded conditional
adapter or overwrite the lead's cleanup with the first delivery. Changes to other existing
mathematics need coordination. Do not edit skeletons, the aggregate, FREE_INPUTS, FILL_LOG,
compiler leases or Git state. The lead handles integration.

## Current supporting API

The lead removed
`exists_isTopologicalCellWithInterior_union_consecutive_of_isTopologicalCell_union`.
It assumed the main union-cell conclusion and did not consume `hc.overlap`. Its legitimate
interior argument has been replaced by the following reusable theorem, proved by
transporting the inclusion into the larger cell's standard ball and applying invariance
of domain:

```lean
theorem IsTopologicalCellWithInterior.interior_mono
    {n : ℕ} {X : Type*} [TopologicalSpace X] {C I D J : Set X}
    (hC : IsTopologicalCellWithInterior n C I)
    (hD : IsTopologicalCellWithInterior n D J) (hCD : C ⊆ D) : I ⊆ J
```

This theorem has no ambient-dimension, planarity, Hausdorff or PL hypothesis. The existing
matching-dimensional `IsTopologicalCellWithInterior.interior_eq` now reuses
`Topology/ClosedBallImage.lean` rather than repeating its proof.

`PlanarCellUnion` retains the projection/section identities and cell transports. It also
now provides the two bridges omitted from the first report's claimed complete reduction:

```lean
theorem planarProjection_image_inter {A B : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : ∀ p ∈ A, p 2 = 0) (hB : ∀ p ∈ B, p 2 = 0) :
    planarProjection '' (A ∩ B) = planarProjection '' A ∩ planarProjection '' B

theorem isTopologicalCell_of_planarProjection {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ p ∈ D, p 2 = 0) (h : IsTopologicalCell 2 D) :
    IsTopologicalCell 2 (planarProjection '' D)
```

The standard rectangular union theorem is proved for both adjacent pairs and now consumes
the general interior-monotonicity theorem. It remains a special-case theorem. It does not
test or prove the missing arbitrary-disk producer.

Current source hashes, after the lead's cleanup:

- `TopologicalCellInterior.lean`:
  `C6633D5E27180A45BE09F75E104377CD579D540F5826814E5FBF0EA6F3A1C75E`.
- `PlanarCellUnion.lean`:
  `6469D45653D06A5798DF38EFE97DA85FF1C918491C4219EDB3E93D0B8961E112`.
- Frozen `Skeleton/Section31CanonicalConfiguration.lean` remains
  `E59DA9335DD520F9372A479DB5A5A1445FC7F878B9380E2B93E53D641524F79D`.

## This round's mathematical task

Prove the general planar disk-union theorem. In a general topology module, use actual
closed-ball homeomorphisms and avoid importing `MoiseChain` merely for its predicate:

```lean
{A B : Set (EuclideanSpace ℝ (Fin 2))}
(hA : Nonempty (A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1))
(hB : Nonempty (B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1))
(hAB : Nonempty ((A ∩ B) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
Nonempty ((A ∪ B) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
```

This is the missing theorem to implement, not an extra input to a wrapper. Search by
mathematical content and inspect actual signatures before adding helpers. First develop a
checkable mathematical argument for the union's Jordan frontier or an equivalent disk
parameterization, then implement its essential lemmas. Merely reporting again that
Schoenflies is deep or that a ready-made disk-union API is absent does not advance this task.

These inputs are arbitrary topological closed disks. Do not add convexity, PL structure,
finite boundary intersections, transverse crossings, boundary intersection nonemptiness,
or a supplied union parameterization. Strict containment and equal disks must remain
covered. The intersection is a two-cell; the existing PL union theorem for intersection
along one boundary arc does not apply directly. Infinite boundary behavior must be handled
by the actual argument, not silently replaced by a finite boundary-arc list.

Useful existing downstream APIs are listed in the original handoff, notably
`PlanarJordan/ClosedInterior`, `CompactRegion`, `RegionRecognition`, `AmbientExtension`,
and `Topology/ClosedBallImage`. They require their actual frontier or embedding inputs;
none may be cited as already supplying the missing union frontier.

Once the core is proved, in `PlanarCellUnion`:

1. Obtain the two projected cells from `hc.cell` and `hc.halfPlane`.
2. Use the exact image-intersection formula and the bare-cell projection theorem to
   transport `hc.overlap`. Both bridges have already been checked with the frozen inputs.
3. Apply the new planar producer and transport its cell back with `planarPoint`.
4. Choose the interior from its disk parameterization. Apply `interior_mono` to each
   inclusion to obtain the two original `Dint` containments.
5. Prove `exists_isTopologicalCellWithInterior_union_consecutive` with exactly the frozen
   name, signature and existing public predicates from the original handoff. Never import
   a skeleton. Exercise the final producer itself on the standard chain.

If you find an obstruction to the statement, check a proposed counterexample against all
three disk hypotheses and then every frozen chain field before claiming FALSE. A failed
proof route or missing library theorem is not a counterexample. If this round remains
partial, deliver genuinely proved supporting results and the exact remaining mathematical
obligation, without an endpoint-shaped assumption or new sorry.

## Checking and delivery

Use PowerShell and existing lease d only, with token `claude-agent-d-20260919` and private
root `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`. Read its current JSON before
compiling; only the owner may modify it. The original handoff supplies the exact preparation
and checker commands. Prepare immediately before checking each named module, in dependency
order. Keep shared outputs unchanged.

There is no twelve-call or other arbitrary call-count cap. Continue useful implementation
and normal compiler repair within the actual concurrency and expiry limits. Do not repeat
unproductive searches or treat tool termination from a quoting error as a Lean result.

Deliver zero-diagnostic module receipts, stable source hashes, and an external audit of
all nonautomatic declarations in every changed/new module. Allow only `propext`,
`Classical.choice`, and `Quot.sound`; run the full standard thirteen linters excluding only
`docBlame` and `docBlameThm`. Extend the audit module list for a new `PlanarJordan.DiskUnion`
module and retain its nonempty-declaration guard. No new sorry, axioms, linter suppressions,
resource-budget overrides, declaration docstrings or inline source comments.

Append the result to the Gemini log. Stop after this scoped round; do not select an
unrelated leaf automatically. The lead will independently verify, register imports,
update the sole ledger, commit explicit paths, and synchronize the mirror.
