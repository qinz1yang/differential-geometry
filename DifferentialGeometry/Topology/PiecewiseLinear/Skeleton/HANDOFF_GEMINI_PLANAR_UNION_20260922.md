# Gemini handoff: unions of overlapping planar topological disks

The owner has now authorized the broader continuous [Gemini batch](GEMINI_BATCH.md).
Its scope and continuation rules supersede the single-target restrictions below; keep
this file as mathematical context for the planar target.

The first delivery has returned. Before resuming, read the
[round-two update](HANDOFF_GEMINI_PLANAR_UNION_ROUND2_20260922.md); it supersedes the old
candidate status and records the lead's API cleanup. The original frozen target below is
unchanged.

This is a self-contained assignment for a new Gemini CLI session with no previous context.
The owner requested an independent proof lane parallel to task F. The lead reserved entry
10 for this lane. F owns entry 15, stable crossing normal forms and chart transport; neither
its mathematics nor its files are needed for this assignment.

## Workspace and initial reading

- Work only in `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.
  `E:\differential-geometry-dev`, including all shared build outputs, is read-only.
- The source checkpoint used for this packet is local
  `af62ad68a759f9b4f7d234d957ba558c6b85ea56`, mirrored as
  `5cf1b3cb18cc93ea180873af867d8ecb10e8bb68` on GitHub branch `moise-integration`.
  Check live HEAD and dirty state; do not reset or clean the shared checkout to this snapshot.
- Lean and Mathlib are v4.33.1. Before edits, read the root `AGENTS.md`, `NAMING.md`,
  `STRUCTURE.md`, `DifferentialGeometry/Topology/PiecewiseLinear/AGENTS.md`, and
  `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/README.md` completely.
- All paths below are relative to the D: checkout unless absolute. The only progress ledger
  is `DifferentialGeometry/Topology/PiecewiseLinear/FREE_INPUTS.md`, row B1.g. This packet is
  an assignment, not evidence that any theorem has been proved. Do not reread historical
  handoffs or unrelated consult summaries. The relevant statement review is
  `DifferentialGeometry/Topology/PiecewiseLinear/consult/AP-section31-first-review-digest.md`.

## Deliverable: the unchanged frozen theorem

Prove the following theorem in a real module, using the existing public definitions and
namespace `DifferentialGeometry.Topology.PiecewiseLinear`:

```lean
theorem exists_isTopologicalCellWithInterior_union_consecutive
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsPlanarCellChain P D Dint) (j : Fin 2) :
    ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧
        Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint := by
```

The canonical frozen source is
`DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/Section31CanonicalConfiguration.lean:376`.
That skeleton's SHA256 at assignment is
`E59DA9335DD520F9372A479DB5A5A1445FC7F878B9380E2B93E53D641524F79D`.
The whole explicit signature, name and ambient lexical scopes must be preserved. The leaf
is reviewed OK and frozen, but its proof is OPEN. Its callers are the two consecutive-pair
uses in the proof of `moise314` near lines 776 and 793; do not edit those callers.

This is a theorem about arbitrary topological disks. Do not add PL, polygonality, convexity,
finite boundary intersection, transversality or boundary-arc hypotheses. Do not replace
the actual union by a larger disk or weaken the two interior inclusions. A stronger natural
general theorem is welcome, provided the frozen theorem is proved as a corollary.

## Exact public vocabulary

Read `DifferentialGeometry/Topology/PiecewiseLinear/CanonicalConfiguration.lean`, especially
the planar embedding at lines 88-126, the cell definitions at 235-242 and the chain at 312-321.
The definitions are reproduced here for orientation; import them, never make private copies.

```lean
def IsTopologicalCell (n : ℕ) {E : Type u} [TopologicalSpace E] (C : Set E) : Prop :=
  Nonempty (C ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

def IsTopologicalCellWithInterior (n : ℕ) {X : Type*} [TopologicalSpace X] (C I : Set X) :
    Prop :=
  ∃ φ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ C,
    I = Subtype.val '' (φ '' {q | ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1})

structure IsPlanarCellChain (P : Fin 4 → EuclideanSpace ℝ (Fin 3))
    (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  halfPlane : ∀ j, ∀ p ∈ D j, p 2 = 0 ∧ 0 < p 0
  cell : ∀ j, IsTopologicalCellWithInterior 2 (D j) (Dint j)
  interiorSubset : ∀ j, Dint j ⊆ D j
  segmentSubset : ∀ j : Fin 3, segment ℝ (P j.castSucc) (P j.succ) ⊆ Dint j
  consecutiveNe : ∀ j : Fin 3, P j.castSucc ≠ P j.succ
  overlap : ∀ j : Fin 2, IsTopologicalCell 2 (D j.castSucc ∩ D j.succ)
  apart : D 0 ∩ D 2 = ∅
```

`IsTopologicalCell` is originally in `PiecewiseLinear/MoiseChain.lean:82` and is imported
by `CanonicalConfiguration`. The latter's source SHA256 is
`E26CC35F7E14835347F096F1F01FBACFAD2450A2B1BA6A74AA4A3916285C1155`.

The intended geometry is two closed disks in the same plane, with intersection itself a
closed two-disk. The specified interiors come from the same parametrizations as the disks.
Both adjacent disks contain their shared chain point in their specified interiors. The
entire chain has an independent nondegenerate instance; no empty-disk shortcut is available.

## Existing work and the actual gap

F previously investigated entry 10 and stopped at the planar union theorem. Its old file
`PiecewiseLinear/ExistsIsTopologicalCellWithInteriorUnionConsecutive.lean.wip` only unpacks
the three disk homeomorphisms and ends in a failing `aesop`. Read it only if useful; do not
modify or count it as a proof. A tactic search alone does not supply the missing topology.

F also supplied the candidate real module
`DifferentialGeometry/Topology/PiecewiseLinear/TopologicalCellInterior.lean`. Its theorem is:

```lean
theorem IsTopologicalCellWithInterior.interior_eq
    {n : ℕ} {C I : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsTopologicalCellWithInterior n C I) : interior C = I
```

Its SHA256 is `CF4529B964071B01615A406FFF0DB00A9471644EFC9432274A31E56A1F717C34`.
F reported zero-diagnostic compilation, foundational axioms and 13 clean linters. It is
not yet independently accepted or registered by the lead. You may read, independently
check and import this exact source as a candidate dependency; do not modify it or duplicate
its theorem. Its proof uses the real
`DifferentialGeometry.Topology.interior_range_eq_image_preimage_interior` from
`Topology/OpenEmbeddingFrontier.lean`.

Crucial: that theorem applies when the cell dimension equals the Euclidean ambient
dimension. The planar disks in the frozen theorem are subsets of R3, so their ambient
interior is empty. First transport to R2, or work in the intrinsic plane. Do not claim
`interior (D j) = Dint j` in R3.

Useful source map; inspect signatures and axiom closures before use:

| Source under `DifferentialGeometry/Topology/` | Available ingredient and limit |
|---|---|
| `PiecewiseLinear/CanonicalConfiguration.lean` | `planarPoint`, `planarPoint_mem_iff`, `isometry_planarPoint`, `continuous_planarPoint`, `IsTopologicalCellWithInterior.isTopologicalCell`; convex planar-image theorems cover only convex inputs. |
| `ClosedBallImage.lean` | `isCompact_of_homeomorphClosedBall`, `interior_eq_image_of_homeomorphClosedBall`, `frontier_eq_image_sphere_of_homeomorphClosedBall`, `interior_nonempty_of_homeomorphClosedBall`; these are same-dimensional closed-ball image tools. |
| `PlanarJordan/AmbientExtension.lean` | `isJordanCurve_range_of_isEmbedding_circle`, `exists_homeomorph_extending_circle_embedding`; these start from an actual embedded circle. |
| `PlanarJordan/ClosedInterior.lean` | `nonempty_homeomorph_closedBall_closure` constructs a disk from an open connected bounded region with a supplied injective boundary loop; it does not produce that loop. |
| `PlanarJordan/RegionRecognition.lean` | `eq_inside_of_isOpen_isBounded_frontier_subset` identifies a region once the Jordan boundary data are available. |
| `PlanarJordan/CompactRegion.lean` | `interior_eq_inside_frontier_of_isCompact`, `closure_inside_frontier_eq_of_isCompact`; both still require a supplied Jordan frontier. |
| `PlanarJordan/Transport.lean` | Transport of Jordan curves, arcs and the inside region under plane homeomorphisms. |
| `PiecewiseLinear/PlanarDiskUnion.lean` | `isPLBall_union_and_finite_frontier_inter` requires PL disks meeting in a ONE-dimensional boundary arc. It cannot directly discharge this TWO-dimensional overlap problem. |

A possible development is: transport the two cells to the plane; prove a natural general
union theorem for two topological closed disks with disk intersection; obtain the actual
union parametrization; use invariance of domain in dimension two and monotonicity of
interior for the two inclusions; transport back. This is a suggested decomposition, not
a supplied proof. In particular, connectedness or contractibility of the union alone is
not a disk parametrization, and citing Schoenflies without producing its required boundary
data leaves the main gap open. Do not assume the boundaries intersect only finitely often.
The natural general core can use just three homeomorphism assumptions in R2:
`Nonempty (A ≃ₜ B2)`, `Nonempty (B ≃ₜ B2)` and `Nonempty ((A ∩ B) ≃ₜ B2)`, concluding
`Nonempty ((A ∪ B) ≃ₜ B2)`, where `B2` is the closed unit ball in R2. This is a suggested
proof target, not a pre-existing theorem. This formulation keeps general planar topology
independent of the higher-level `MoiseChain` definitions; the cell-chain adapter imports them.
Containment cases are legal: one disk may lie strictly inside the other and their boundaries
may be disjoint. Any proof that begins by choosing a boundary intersection must first handle
this case. Shared interior points follow from `segmentSubset`, rather than being new inputs.
For a paper test satisfying the entire chain, take in the plane
`D0 = [1,3] × [-1,1]`, `D1 = [1/2,15/2] × [-2,2]`,
`D2 = [5,7] × [-1,1]`, with the four points on the horizontal axis at
`3/2, 5/2, 11/2, 13/2`, and then embed at z = 0. Both outer disks lie strictly inside D1
and are disjoint from each other. This paper check is not a compiled Lean fixture.

Start by checking the mathematical statement against all actual fields. If a purported
counterexample appears, verify it jointly against `cell`, the two-dimensional `overlap`,
`segmentSubset`, `halfPlane` and the rest; give explicit maps or certificates and report it
to the lead. A failure of one proposed proof route is not a FALSE verdict.

## File ownership and delivery scope

Reserved new output files, absent when assigned:

- `DifferentialGeometry/Topology/PlanarJordan/DiskUnion.lean`, if a general plane theorem
  belongs naturally there. Keep purely topological mathematics in the topic home.
- `DifferentialGeometry/Topology/PiecewiseLinear/PlanarCellUnion.lean`, for the frozen
  endpoint and its interface with the existing cell-chain predicates.
- `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/GEMINI_PLANAR_UNION_LOG.md`,
  an append-only worker report. It is evidence, not a second progress ledger.

Creating another genuinely necessary module in these two topic homes is authorized after
checking name collisions and existing APIs; list every new file in your report. Prefer
proved reusable intermediate lemmas over a monolithic opaque attempt. Do not modify existing
library files without coordinating the exact scope with the lead. In particular preserve
`CanonicalConfiguration`, the candidate `TopologicalCellInterior`, all old WIPs, all
`LoopTheorem` files and F's `NormalCrossingTransport`/stable-crossing work.

Do not edit skeleton Lean files, `FREE_INPUTS.md`, the flat aggregate, this assignment or
`FILL_LOG.md`. Do not stage, commit, push, reset, clean, merge or edit any lease JSON. The lead
will independently verify, register imports, replace the frozen skeleton leaf and commit
the completed dependency layer. Never import ANY skeleton, including another skeleton.

No new `sorry`, `admit`, `axiom`, `trustMe`, diagnostic commands, resource-budget overrides
or linter suppressions in deliverable Lean source. No declaration docstrings or inline
comments. Keep the required copyright header, imports, then a concise mathematical module
docstring. Follow the actual local AGENTS rules, not any conflicting CLI default.

## Private compilation: reserved lane d

The lead checked that the old d worker had stopped and reserves its existing lane for this
Gemini assignment. The token's historic `claude` name is only its existing lease identifier;
do not rename it or create another lease. No arbitrary Lean-call limit applies. Continue
productive proof work and normal elaboration repairs; stop for delivery or a substantiated
blocker. The owner's actual resource and expiry controls still apply.

Use PowerShell only, one Lean process in this lane, through these existing wrappers:

```powershell
Set-Location -LiteralPath 'D:\differential-geometry-moise-int'
$geminiOutput = 'C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d'
$geminiShared = 'C:\Users\liao9\AppData\Local\Temp\claude-moise-shared'
$geminiToken = 'claude-agent-d-20260919'
Get-Content -LiteralPath '.lake\round-compiler-leases\claude-agent-d.json' -Raw

$geminiModule = 'DifferentialGeometry.Topology.PiecewiseLinear.PlanarCellUnion'
python (Join-Path $geminiShared 'prepare-private-root.py') $geminiOutput $geminiModule
if ($LASTEXITCODE -ne 0) { throw 'Private dependency preparation failed' }
& (Join-Path $geminiShared 'checker.ps1') `
  -Checkout 'D:\differential-geometry-moise-int' -Token $geminiToken `
  -OutputRoot $geminiOutput -Module $geminiModule
```

Run preparation immediately before every named-module check. If it lists missing necessary
prerequisites, check them individually in dependency order in your private root. Do not
compile another active lane's changing source; report that dependency and coordinate.
The target file must exist before preparation. To check the existing interior candidate,
replace the module name by `DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInterior`.
Preparation of `CanonicalConfiguration` was checked by the lead without running Lean:
all 14 required private objects were available, with no missing prerequisite at assignment.

For an external audit or API probe, put its source under the private output directory,
never in the project tree, and use `-Audit`, not `-Module`:

```powershell
& (Join-Path $geminiShared 'checker.ps1') `
  -Checkout 'D:\differential-geometry-moise-int' -Token $geminiToken `
  -OutputRoot $geminiOutput `
  -Audit (Join-Path $geminiOutput 'AuditGeminiPlanarCellUnion.lean')
```

The live lease, not this document, controls expiry. At assignment it is `granted`, permits
`DifferentialGeometry.Topology.*`, has `maxLeanProcesses = 1`, and expires at
`2026-09-24T04:17:07.7791223Z`. Only the owner may extend it. F uses a; the lead uses c.
Never bypass `checker.ps1` with bare Lean, `lake env lean`, a broad `lake build`, Bash/WSL,
another lane's token, or a write to shared E: objects. Do not call `lake build DifferentialGeometry`
under this restricted lease. Receipt and log paths are the private module path plus `.json`
and `.log`; external audits use `external-audit.json` and `.log`, so archive each result
under a distinct name before the next audit overwrites it.

## Acceptance evidence

Before reporting CLOSED, provide:

1. The actual real `.lean` files, exact public names/imports and SHA256 of each final source.
   Compare the entire frozen endpoint header and scope against the original skeleton.
2. Named-module checks with `exitCode = 0`, `diagnosticLines = 0`, stable source hashes and
   unchanged shared outputs. No warnings or avoidable info output are acceptable.
3. A namespace-aware, all-declaration axiom audit of each new module and any reused candidate
   dependency. Check every module-owned non-automatic declaration, including private helpers;
   only `propext`, `Classical.choice`, `Quot.sound` are allowed, never `sorryAx`.
4. The complete standard environment linter set except `docBlame`/`docBlameThm` (13 checks
   in the current environment). Exclude those two in the external audit, not with source
   suppression. The ready external-audit template is
   `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-planar-union\audit-template.txt`.
   Copy it to the external `.lean` audit path only after the imported modules exist; add any
   new general module to both its imports and audited module-name list. It is a template,
   not an already-run audit of the future deliverable.
5. A nondegenerate smoke test using the existing `isPlanarCellChain_standard`, with both
   `j = 0` and `j = 1`, without importing the skeleton. Its three rectangles are
   `[j+3/5,j+12/5] × [-1,1] × {0}`, with `P j = (j+1,0,0)`; their adjacent overlaps are
   two-dimensional rectangles. This is a check on an already proved general theorem,
   not a substitute proving only the rectangular case.
6. A concise entry in `GEMINI_PLANAR_UNION_LOG.md`: CLOSED/PARTIAL/STUCK, exact checks and
   timings, proof mechanism, remaining goals, and any counterexample checked field by field.
   A supporting lemma alone is PARTIAL; a compiling conditional assembly is not closure.

After finishing this assignment, report to the owner/lead rather than automatically moving
to another leaf. The lead remains responsible for independent acceptance and integration.
