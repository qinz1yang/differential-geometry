# Smooth-Schoenflies dependency integration: isolated-worktree plan

Written by the lead on 2026-09-23/24 after the owner chose option 1: verify the batch in an isolated
worktree, scoped to the two entry theorems and their real dependency closure; nothing enters the
shared checkout `D:\differential-geometry-moise-int` (branch `codex/moise-integration`) before the
lead accepts it. Paths below are absolute or relative to the checkout root.

## 0. Background and records

- Lane c (uniqueness of the smooth structure on `S²`, lease `claude-agent-c`, log
  `Skeleton/OPUS_FILL_LOG_C.md`) needs two theorems for the single-face replacement in surface charts:
  `PlanarJordan.smooth_schoenflies` (`DifferentialGeometry/Topology/PlanarJordan/SmoothSchoenflies.lean`)
  and `PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_jordan_curve`
  (`DifferentialGeometry/Topology/PlanarJordan/BoundaryGermExtension.lean`).
- Source of the batch: `origin/codex/pc-sorry-free@54ad4d8ec` (merge base with dev `806b541e9`; that
  branch is 1181 commits ahead of it, dev 9). Its 88 new modules do not exist on dev, so the shared
  baseline `E:\differential-geometry-dev\.lake\build` has no objects for them; the 30 updated modules
  differ from both dev and `codex/moise-integration`.
- Records of the misrouted task (read-only): `C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\`
  — `apply-plan.json` (135 paths with before/after hashes), `prepared\` (byte-exact copies),
  `before\` (originals of the 31 updated files), `after\` (the versions that had been applied),
  `build-plan.json` (order 334, compile 144, sharedBaseline 190), `compile-order.txt` (the 144 modules
  to compile, in dependency order), `integration-manifest.json` (199 same, 93 missing, 30 changed).
  Lead check: the import closure of the two entry modules over prepared ∪ moise-integration is 314
  modules; 230 have an object in the shared baseline, 84 do not; all 118 batch modules are in the
  144 and in the lease's 334.
- Shared checkout: the 31 overwritten tracked files were restored from `before\` (content = HEAD) on
  2026-09-23; the batch's new files were moved out of the shared checkout into
  `codex-smooth-integration\removed-from-shared\` once the worktree held them. Every lead acceptance
  check of 2026-09-23 predates the misrouted copy.

## 1. Worktree and branch (lead; DONE)

- Worktree `D:\differential-geometry-smooth-int`, branch `codex/moise-smooth-integration`, base
  `2dcb704e8` (moise-integration head after the PR #11 cherry-picks), pushed to origin.
- Commit `69f2be6e4`: 114 Lean modules (84 new, 30 updated) and the tracked
  `External/ClassificationOfSurfaces/VENDOR.md`; commit `4b898b95f`: the batch's four
  `External/ClassificationOfSurfaces/*.lean` modules (force-added like the twenty tracked External
  files). All 118 batch modules are in the tree; the 16 new vendor records under `External/` stay
  untracked (gitignored). Every commit is marked UNVERIFIED.
- The worktree needs no `.lake` of its own: the checker takes the toolchain, the packages and the
  shared baseline from `E:\differential-geometry-dev` and reads leases from
  `D:\differential-geometry-moise-int\.lake\round-compiler-leases`.

## 2. Lease and checker (lead; DONE, owner to confirm)

- `codex-smooth-integration.json`: `checkout` = `D:\differential-geometry-smooth-int`,
  `validUntilUtc` = 2026-09-26T04:17Z, token `codex-smooth-integration-20260923`, outputRoot
  `C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration`, 334 explicit modules,
  `maxLeanProcesses` 1. The checker rejects any other `-Checkout` or `-OutputRoot` for this token.
- `prepare-private-root.py` hard-codes the shared checkout; the worktree uses the variant
  `C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\prepare-private-root-worktree.py`
  (same logic; the checkout comes from `MOISE_CHECKOUT`). It seeds nothing from other private roots,
  since their receipts name the shared checkout's source paths; that is expected.
- One module:

  ```powershell
  $env:MOISE_CHECKOUT = 'D:\differential-geometry-smooth-int'
  python C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\prepare-private-root-worktree.py `
    C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration <Module.Name>
  powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1 `
    -Checkout D:\differential-geometry-smooth-int -Token codex-smooth-integration-20260923 `
    -OutputRoot C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration -Module <Module.Name>
  ```

  Success line: `Verified <Module.Name> with no diagnostics; shared outputs unchanged.`
- Host budget: at most four `lean.exe` on the host, this lease one; count the other lanes before
  starting. A ten-minute admission wait is contention, not an error: rerun.

## 3. Cone verification (lane c under the smooth lease; no git writes, no frozen statement edits)

1. Compile `compile-order.txt` top to bottom (144 modules). If the prepare script's
   `MUST COMPILE YOURSELF` for `DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies` or
   `…PlanarJordan.BoundaryGermExtension` names a module outside the 144, compile it too and report it.
2. Known obstacle: the pc-sorry-free `Analysis/Calculus/Cutoff/Basic.lean` failed the header /
   module-docstring lint in lane c's earlier refresh attempt (`-Dlinter.style.header=true`). Fix such
   files in the worktree by adding the required copyright header and module docstring, never by
   suppressing a linter; record each edit in the log with its diff; the lead commits them on the
   isolated branch. Any real proof error means the batch does not reproduce and stops here: report
   the module and the first error.
3. Zero diagnostics for every module. Then the audit: the lead generates an audit probe outside the
   tree (`AuditSmoothCone.lean`, importing the two entry modules; the `mkaudit` pattern) and runs it
   with `-Audit` under the same lease: every declaration of the 118 batch modules closes under
   `propext`, `Classical.choice`, `Quot.sound`, and the thirteen environment linters pass.
4. Log in the worktree's `Skeleton/OPUS_FILL_LOG_C.md` (append-only): per-module receipt lines,
   timings (they give the cost estimate for step 5), the edits of item 2.

## 4. Single-face replacement (lane c, in the worktree)

- Copy your two delivered modules (`SmoothDiskExtension`, `RelativeDiffeomorphPasting`) into the
  worktree; they are yours until acceptance. New files only; connect the pasting lemma to the two
  entry theorems and prove the chart-level single-face replacement of log C Batch 9's route; verify
  with the same lease and add its declarations to the audit.

## 5. Acceptance and entry into the shared tree (lead)

- First acceptance batch = "dependency cone passes + single-face replacement passes": the lead
  checks every receipt in the private root (exitCode 0, diagnosticLines 0, sourceStable, sourceSha256
  = the worktree source), reruns the audit itself under the smooth lease while lane c pauses, and
  commits lane c's files and the item-2 edits on the isolated branch.
- Entry: the lead merges `codex/moise-smooth-integration` into `codex/moise-integration` in an
  exclusive window (all lanes paused: the 30 updated upstream modules sit in the import cone of 399
  PL modules including every active skeleton), registers the new modules in `DifferentialGeometry.lean`,
  and recompiles the 144-module cone once in a shared-checkout private root, because receipts and
  import artefacts are bound to the checkout path (checker line 99), so the worktree's objects
  cannot be reused in `D:\differential-geometry-moise-int`. Cost: 144 modules on one process; take
  the estimate from step 3's timings.
- Until then no module of the shared tree imports anything from the batch.

## 6. Open for the owner

- The 16 new vendor records under `External/` (untracked, gitignored): keep ignored, or force-track
  like the existing twenty External files.
- Whether lane c or a dedicated Codex lane runs step 3.

## 7. Owners (owner's clarification 2026-09-24 09:50)

- Lane c is now the English-speaking collaborator, working in a cloud Codex sandbox WITHOUT host
  access: it cannot run the checker or the cone compile. It works source-only on the isolated branch
  `codex/moise-smooth-integration` (new files only, PRs against that branch): first its intake review
  (`consult/smooth-intake-review.md`: the seven additional prerequisites of the chart-level route with
  their `pc-sorry-free@54ad4d8ec` paths, the 341 hashes), then the single-face replacement (§4), then the
  sphere subdivision and skeleton induction of the `S²` uniqueness leaf.
- Step 3 (the 144-module cone compile, the header fixes, the two-entry audit) and the verification of
  every collaborator PR on that branch run on the Windows host under the `codex-smooth-integration`
  lease, in the worktree, by the lead or a local Codex lane: cherry-pick the PR into the worktree, then
  `prepare-private-root-worktree.py` + `checker.ps1 -Checkout D:` + the worktree path per module, then the audit.
- The seven additional prerequisites are added to the worktree by the host side from the same source
  revision before the cone compile, and `compile-order.txt` is extended accordingly.

## 8. Host entry, 2026-09-24

The isolated branch passed corrected strict 741-module replay and 27 audits,
then entered `codex/moise-integration` as a real merge. The entry closure passed
732 fresh main-checkout module checks; 27 main-checkout audits passed 11,086
declarations. All 118 leaf modules and promoted `PLSmoothingCompact` are in the
flat aggregate. The scoped entry is accepted. The repository aggregate build
is not certified. The broader all-PL replay found an inherited unfinished
`FourSpokeCap.lean` outside this entry closure and outside current root imports. See
`consult/smooth-main-host-acceptance.md` and its source-bound receipt manifest.
