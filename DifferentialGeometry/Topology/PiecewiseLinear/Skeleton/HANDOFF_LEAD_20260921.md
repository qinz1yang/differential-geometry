# Lead handoff — Moise integration, evening of 2026-09-21

Written by the outgoing lead session for its successor. Read this, then `FREE_INPUTS.md`
(the only progress yardstick) and `Skeleton/README.md` (rules 1–8). Do not reread the whole
history; the digests in `consult/` are indexed by letter (latest: AP).

## 1. Where things stand (HEAD `c492e7fff`, mirror `liao9yuan/differential-geometry-dev:moise-integration` in sync)

Ten skeletons, every leaf statement frozen by external review except where noted (§31's relative leaf is the one unreviewed statement):

| Skeleton | Leaves | State |
|---|---|---|
| `GeneralPositionInDouble` (A1) | 14 | frozen |
| `DescentStepOrientable` + `ClosedBranchCaseOne` (A2) | 7 + 1 | frozen |
| `ControlledGraphNeighborhood` (35.1) | 7 | frozen |
| `Section34Control` (P0) | 3 | frozen; two leaves proved by the owner's lane and wired in |
| `Section34Normalization` (P2–P5) | 8 | frozen; P3 now takes `Moise305Tame` (consult AO) |
| `Section34Terminal` | 5 | frozen |
| `Section33Approximation` (33.1) | 12 | frozen |
| `Section32PseudoCell` (§32) | 13 | frozen |
| `Section31CanonicalConfiguration` (§31) | 9 | frozen + 1 unreviewed relative leaf (repair landed, `5ec76cf74`) |
| `PLSmoothingCompact` (C1) | 11 | frozen |

Structural finding of the day (consult AL/AO): `Moise341` (34.1) had no producer and the only tree
route was circular through 35.2. Adopted: a separate compact-ball skeleton `Section34Compact`
(**in flight**, see §2) with entry `Moise341OnNeighborhood` + the proved inward push; P2–P5's face
balls now come from the tame 30.5, as in the book.

## 2. Two worker deliveries in flight (they write into the tree; accept from the files)

Both were dispatched by the outgoing session as background agents; their reports will not reach
you. Judge by the files and `git status`.

**(a) `Skeleton/Section34Compact.lean`** (new, lease b). Spec: `consult/AO-moise341-design-answer-digest.md`
§1 (leaf table) and the dispatch rules in `Skeleton/README.md`. Accept iff:
1. `prepare` + `checker` on a free lease (b, c, d or e): every `warning|error` line in the log is
   `declaration uses 'sorry'` at a leaf; no `sorry` inside `moise341OnNeighborhood`-type assemblies
   (grep `sorry` and read the assembly bodies);
2. the two endpoints are proved theorems: the local `def Moise341OnNeighborhood` and
   `theorem … : Moise341` from it via the inward push (check the push is the tree's proved one or an
   honest named leaf);
3. the finite cut records **outer faces of boundary vertices and outer arcs of boundary edges**
   (the design's first fixture check) — if absent, send it back;
4. finite P5 is a proved descent (no limit leaf); the extension order is as in AO §1;
5. every new public name unique tree-wide (grep); no edit to any other file.
Then: ledger row under B1.b (new ID B1.b.8), commit by explicit path, sync, and give the owner
the review prompt (template below).

**(b) DONE before the handoff took effect** — the §31 repair landed and was accepted (`5ec76cf74`):
`Fits`, `PairGP`, the relative leaf, L6 proved from it, 9 `sorry`. What remains for you is only the
review prompt for the relative leaf (mirror `9db13f30`), template in §4. Original spec kept for
reference:
`consult/AP-section31-first-review-digest.md` §"§31 → §32 interface": add `Fits`, `PairGP`, the leaf
`exists_generalPosition_solidTorus_relative` (old tori `F : Fin m → Set E3` as fixed parameters),
derive `exists_generalPosition_solidTorus_triple` from it (leaf → proved), docstring items (a)–(c).
Accept iff: 9 `sorry` diagnostics (8 old + the relative leaf) unless the worker had to expose the
single-torus producer as a leaf (then 10, explained); the eight untouched leaves byte-identical to
`git show HEAD:<file>` (script pattern: extract each `theorem … sorry` block and compare); four
endpoint assemblies still compile. Then ledger B1.g update, commit, sync, review prompt for the
relative leaf only.

If a delivery never lands (no file change after ~2 h), re-dispatch with the same spec.

## 3. The owner's overnight proving lane (lease a)

Prompt and queue: `Skeleton/FILL_QUEUE.md`; it logs to `Skeleton/FILL_LOG.md` (its own file). In
the morning, for each CLOSED entry: re-run `prepare` + `checker` on the module (zero
diagnostics), run the axiom audit, compare the statement byte-for-byte with the skeleton leaf,
grep the new public names, register the import in `DifferentialGeometry.lean` (insert before the
first `/-!`, check duplicates), replace the skeleton's leaf by the import (delete the `theorem …
sorry` block, add the import line, update the docstring count and the leaf's paragraph), re-check
the skeleton, ledger, commit by explicit path, sync. For FALSE entries: verify the counterexample
against the actual hypotheses before believing it (external-review rule applies to lanes too); a
verified refutation of a frozen leaf reopens it — record in the ledger and repair the statement.
STUCK entries: leave the `.wip` files alone; note them in the ledger as partial.

## 4. Tooling (all paths absolute; PowerShell for Lean, never Bash)

* Focused check: `python C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\prepare-private-root.py <ROOT> <Module>` then
  `powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1 -Checkout D:\differential-geometry-moise-int -Token <TOKEN> -OutputRoot <ROOT> -Module <Module>`; success line
  `Verified … with no diagnostics; shared outputs unchanged.`; skeletons exit non-zero — read
  `<ROOT>\DifferentialGeometry\Topology\PiecewiseLinear\Skeleton\<Name>.log` and count `warning|error`
  vs `declaration uses .sorry.`; compare the log's LastWriteTime with the clock.
* Leases: `claude-agent-<x>-20260919`, roots `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-<x>`,
  x ∈ {a (owner's lane), b, c, d, e}. Lease JSON files are owner-only (the auto-mode classifier
  blocks edits; ask the owner).
* Axiom audit generator: `C:\Users\liao9\AppData\Local\Temp\claude\E--differential-geometry-dev\b50ff675-c992-4e49-aaf7-d27640f013ea\scratchpad\mkaudit.py <lease-letter> <Name> <Module…>` →
  `Audit<Name>.lean` in the lease root + `accept-<Name>.ps1` next to the script; run the `.ps1`
  from PowerShell; log `.lake\scratch\Accept<Name>.log`. Worker rules for dispatches:
  `…\scratchpad\WORKER_RULES.md` (same directory).
* Commits: message file + `git commit -F`, `git add -- <explicit paths>`; never `git add -A`; the
  root aggregate `DifferentialGeometry.lean` only gets import lines. Mirror:
  `bash /c/Users/liao9/AppData/Local/Temp/claude-moise-integration-private/sync-mirror.sh` (no force).
* Review prompt template (Chinese, ≤ 1500 chars, only non-OK leaves get detail):
  "按 `…/consult/REVIEW-TEMPLATE.md` 审查 `moise-integration@<mirror-sha>` 的 `Skeleton/<File>.lean`（<n> 个叶子；上轮摘要 `consult/<X>-…`），请裁定：① … ② …". Digest every answer
  as `consult/<next letter>-…-digest.md` with [V]/[–] marks; verify counterexamples against the Lean
  text before repairing; record disagreements.

## 5. Owed items (none blocking; in rough priority)

1. Hoist skeleton-local vocabulary into real modules once stable: `CarriesFirstHomologyOnto`,
   `HasPLCurveCrossingOnAt`, the two counts and the homology bridge (P2–P5 → needed by P6);
   `Moise303/286/267` (§32) and the relative general-position statement (§31 → §32 tower) into
   `MoiseChain.lean`; C1's `PLSmoothingModelCompact`, `PLSmoothingCompact`, `IsSmoothHandleStage`,
   `IsPLCellAttachmentWith` into `Smoothing.lean` / `CellAttachment.lean`; `Section34Normalization`'s
   named endpoint into `Section34Statements.lean`.
2. Producers still missing (book theorems as `Prop`s): `Moise306` (30.6), `Moise307` (30.7; +
   bridge cylindrical diagram → cyclic chain), `Moise264` (needs an orientable restricted version
   from `Moise252`, re-point §30.7 and §33), `Moise303`, `Moise286`, `Moise267`, `Moise341` (the
   compact skeleton, once its leaves are proved).
3. `IsTube` Lean inhabitant (a finite complex of `ℝ³` with a verified with-boundary certificate);
   `Section34VertexPreparation`, `IsCommonWallSystem` chart fields, `IsSmoothHandleStage`
   non-empty stage: all UNTESTED.
4. 35.1: the single-cap lemma (`A \ Int B` a PL ball, one transverse circle) as its own leaf; rim
   containment proved out of the matching leaf.
5. Compose P0 with the controlled 35.1 endpoint: split on `isEmpty_or_nonempty M₁`.
6. Codex lane F is paused (usage); lane H holds A1.5b/A1.8/A1.8a until told; lane S untouched.

## 6. Rules the owner set today (memory: `external-review-due-diligence.md`)
External verdicts are evidence: verify before acting, record [V]/[–], report disagreements; when
a review finds a defect *class*, sweep every skeleton for it (the `M₁ = ∅` defect hit a thrice-OK'd
leaf); ask "is this clause satisfiable in OUR ambient object" and "does any consumer need this
leaf" before sending a skeleton out; Opus workers may hit HTTP 529 — the owner allowed Fable
workers as a temporary substitute; write skeletons in parallel, review afterwards.
