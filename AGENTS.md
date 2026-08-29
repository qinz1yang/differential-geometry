# DifferentialGeometry — Codex instructions

This is a Lean 4 / Mathlib library for differential geometry, geometric analysis, and the
topology and Lie theory used by Ricci flow, Hamilton's theorem, and Perelman's Poincaré theorem.
Reusable mathematics is the product; applications and flows are thin capstones.

## Authorities and evidence

- `NAMING.md` is the authority for declaration names. `STRUCTURE.md` is the authority for files,
  folders, granularity, variants, and placement. Read both in full before adding, renaming, moving,
  or reorganizing public mathematics.
- This file governs workflow, soundness, elaboration quality, and delivery gates.
- The exact on-disk Lean declaration, its proof body, the compiler, and its transitive axiom closure
  outrank comments, commit messages, plans, search summaries, remembered APIs, and agent reports.
- Inspect the current worktree before editing. Preserve unrelated and user-owned changes.

## Mathematical architecture

1. Promote every reusable result to its natural topic home. Keep only genuinely flow-specific glue
   under `Geometry/Flow/`.
2. Organize by reasoning nature: metric-free algebra in `Bundle/` or `Tensor/`, geometric reasoning
   in `Geometry/`, and dry analytic/PDE reasoning in `Analysis/`.
3. Treat geometric analysis as a first-class library pillar. Do not hide general PDE, integration,
   Sobolev, elliptic, parabolic, heat, or ODE results inside an application.
4. Maintain `External/` as vendored third-party mathematics. Preserve upstream provenance,
   licenses, attribution, original documentation, and citation metadata; record every local source
   modification in the vendor's modification log. Apply project soundness and build standards while
   respecting any explicitly documented vendor-specific source-style exceptions.
5. Create future Hamilton surgery, Perelman, or 3-manifold topology homes only when their first real
   theorem lands.

Placement is mathematical, not line-count driven:

- One coherent development, however long, is one file.
- A definition with an API and several separable developments is a concept folder, normally
  `Defs.lean`, `Basic.lean`, and mathematically named aspect files.
- Split only across genuine mathematical interfaces. Compile-time improvements may motivate a split
  only when those interfaces are real; never slice a proof by arbitrary line count.
- Use precise imports. Foundational geometry must not import Analysis back; high-level geometry may
  consume Analysis when no cycle results.
- `DifferentialGeometry.lean` is the single flat root aggregate. Do not create per-folder aggregators.
- Namespaces follow mathematical objects and remain decoupled from paths. Do not churn namespaces to
  mirror directories.

For variants, follow the conclusion:

- Different conclusions are coequal siblings sharing their common foundations.
- The same conclusion with stronger assumptions or a special object is a corollary of the natural
  general primary theorem.
- Development order may proceed from a special case to the general theorem, but the final public API
  must expose the mathematically natural direction.

## Public API design

- Use standard, widely recognized mathematical vocabulary. Theorem names are snake_case; definition,
  structure, class, and abbreviation roots are camelCase, following Mathlib.
- Name classical results by their accepted names. Otherwise describe the conclusion and only the
  essential disambiguating hypotheses.
- Never expose task history, effort words, node ids, arbitrary numbering, invented abbreviations, or
  implementation routes in public names.
- Search this library and Mathlib by mathematical content, type shape, and several standard name
  variants before creating anything. Read every plausible signature and inspect its axioms.
- Reuse and generalize an existing canonical declaration instead of cloning it. Re-export when only
  visibility is missing.
- State the weakest natural theorem, not merely the weakest theorem one current consumer needs. Remove
  accidental assumptions and prefer intrinsic formulations over chart artifacts.
- Minimize typeclass assumptions. Generalize `InnerProductSpace` to `NormedSpace`, `Fintype` to
  `Finite`, or analogous structures when the statement permits; construct stronger instances locally
  in the proof when only the implementation needs them.
- Preserve an established public signature when compatibility is material. Make API-breaking
  generalizations deliberately and update all consumers coherently.
- Use ordinary variable blocks for the standard manifold context. Do not introduce bespoke bundled
  context structures merely to shorten binders.

## Source discipline

- Write zero comments and zero docstrings in non-vendored Lean source. Preserve required existing
  Apache Copyright/Authors headers; add no new per-file copyright headers.
- New source files begin with imports. There is no module docstring after them.
- On-disk identifiers and code are English. User-facing discussion may be Chinese.
- Preserve exact `variable`, `open`, `omit`, `include`, `attribute`, `noncomputable`, and local-instance
  scopes when moving code. A wider or reconstructed scope can silently change an elaborated signature.
- Keep namespace openings minimal and lexical. Remove openings duplicated in an active scope and do
  not open the current namespace or one of its ancestors. Prefer qualified names, selective
  `open N (x y)`, or declaration-local `open N in` over a broad namespace opening when practical;
  retain `open scoped` only for notation used in its scope.
- Before making a private declaration public, verify its proposed full name is unique library-wide.
- Do not commit diagnostic commands or output: no exploratory `#check`, `#print`, `#eval`, `#reduce`,
  trace option, `logInfo`, or tactic suggestion output. A silent `run_cmd` assertion is allowed.
- Keep scratch probes outside the project tree and remove them after use.

## Soundness

A green build is necessary but not sufficient.

- Never package the conclusion as a hypothesis, or add an equivalent hypothesis and return it.
- Every predicate must genuinely constrain its advertised object. Check existential packages against
  zero, constant, empty, or otherwise degenerate witnesses.
- Do not turn an existentially produced object into a free universal input without the equation that
  ties it to its producer.
- Match domains and quantifiers to the hypotheses: no whole-line smoothness from interval data, no
  two-sided derivative at a one-sided endpoint, and no all-order constant when only finite-order or
  order-indexed control is available.
- Distinguish separate from joint continuity and pointwise from integrated estimates. Do not strengthen
  a summed cancellation into false componentwise claims.
- Raw moving chart coordinates are not intrinsic continuous fields. Never use
  `HasLocallyConstantChartAt` or an equivalent global-flatness hypothesis in a public theorem.
- New `sorry`, `admit`, `axiom`, `trustMe`, or proposition-valued hypothesis packaging is forbidden
  unless the owner or active goal explicitly authorizes a transient proof frontier. Pre-existing
  out-of-scope debt does not authorize new debt.
- For every completed in-scope headline, verify that its axiom closure contains no `sorryAx` and only
  owner-approved foundational axioms. Fewer axioms than the usual `propext`, `Classical.choice`, and
  `Quot.sound` are acceptable; do not require all three to appear.

## Linters, generality, and elaboration performance

- The Mathlib standard linter set, excluding the documentation-presence linters `docBlame` and
  `docBlameThm`, is a delivery gate. Those two linters are inapplicable because this repository
  requires zero docstrings in non-vendored Lean source; do not suppress them in source.
- Never add `@[nolint ...]`, `attribute [nolint ...]`, or any global, file-local, or
  declaration-scoped linter disable. Repair the declaration or proof instead.
- Resolve `unusedSectionVars` first with `omit`, a smaller variable block, or a more general statement.
  If only the proof needs an instance, build it locally.
- Treat unused instances and binders as API review findings. Remove or weaken them when compatible.
  When `unusedArguments` is a demonstrated proof-irrelevance false positive, the binder or instance is
  present in the intended elaborated statement, and removing it prevents that statement from
  elaborating, give it a name and use it explicitly in the body with `let _ := binder`; do not use a
  `nolint`, an underscore prefix, or a dummy public hypothesis as the repair.
- Keep `classical`, `DecidableEq`, and synthesized finite structures local when they are proof devices
  rather than mathematical hypotheses.
- Do not submit `maxHeartbeats`, `maxRecDepth`, or synthesis-heartbeat budget overrides. Refactor the
  proof, expose a real reusable lemma, make instances explicit, or improve genuine module boundaries.
- An elaborator-semantics option may remain only when it is genuinely required, narrowly scoped where
  practical, and not being used as a resource budget or diagnostic suppressor.

## Workflow and delivery gate

- During development, build the changed module by its Lean module name after each coherent edit. Run
  broader dependent builds when changing a public signature or module boundary.
- Git commits and pushes of in-scope work are owner-authorized. Make proactive checkpoint commits after
  each dependency-closed, compile-clean mathematical layer, before a risky refactor, after closing a
  headline, and after the final delivery gate. Prefer several coherent, bisectable mathematical commits
  over one accumulated end-of-task commit.
- Before every checkpoint, inspect the worktree and complete diff, stage only the intended files, and
  exclude scratch probes, diagnostics, generated noise, unrelated changes, and known broken states.
  Commit messages describe the durable mathematical or architectural result, not task history.
- Push the current feature branch to its configured remote after meaningful verified checkpoints and
  after final verification unless the owner says not to. Never force-push, rewrite published history,
  or move work onto a protected/default branch merely to publish it. A commit or push is archival
  evidence only; it never substitutes for compilation, statement review, or axiom closure.
- Before handoff, build every changed module and then run `lake build DifferentialGeometry` after the
  final edit.
- Final output must contain zero errors and zero warnings except owner-approved warnings from explicitly
  retained `sorry`s. It must contain zero `info`, trace output, `Try this` suggestions, or other avoidable
  diagnostics. Normal build progress and `Built DifferentialGeometry...` lines are expected.
- Run `git diff --check`. Review the complete diff for mathematical correctness, generality, duplicated
  APIs, naming, placement, import cycles, accidental imports, hidden assumptions, vacuity, diagnostic
  commands, comments, resource overrides, and dead code.
- Register every new leaf module in the flat root aggregate and verify that it is built. Zero current
  consumers means unwired, not mathematically dead; classify value by the theorem suite and natural API,
  not by a source-grep import count alone.
- Do not claim a theorem proven from reading, a compiling decomposition, or a clean grep. A proof attempt
  certifies the leaf; compiled glue certifies assembly; the axiom closure certifies transitive completion.

For a curated family of related classical results, use the `prove-theorem-suite` skill. Project
standards in this file remain binding; the skill supplies the optional theorem-forest workflow.
