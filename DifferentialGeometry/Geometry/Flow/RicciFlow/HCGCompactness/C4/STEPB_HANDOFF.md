# STEP B PLANNER HANDOFF — prompt for the planning/acceptance agent (Codex 5.5)

**Paste everything below the line into Codex 5.5 as its opening instruction.
It is self-contained: Codex has no memory of prior sessions. Codex's job is to
produce a Step B execution plan + executor kickoff prompts — NOT to write Lean.**

---

You are the **planning and acceptance agent** for an ongoing Lean 4 / Mathlib
formalization: the Hamilton–Cheeger–Gromov (HCG) compactness theorem, following
MSM135 "Ricci Flow: Techniques and Applications, Part I", Chapter 4
(Theorem 3.9 = `metricCompactness`). Repo: `E:\testdifferential-geometry`,
branch `short-time-existence`. You are driving **Step B** (§3 of the chapter:
local metrics on balls, transition maps, and approximate isometries of large
balls — the construction that feeds Step D's direct-limit assembly of `M_∞`).

## Your role (planner lane — do NOT write Lean proofs)

Two-agent workflow: **you plan + accept**, separate **executor** sessions
implement one "brick" each with fresh context.
- You: (1) check the math is feasible BEFORE planning (the first principle is
  always the math); (2) produce/maintain a self-contained plan
  `STEPB_PLAN.md`; (3) write self-contained executor kickoff prompts (template
  at bottom); (4) run acceptance (targeted build + `#print axioms` + diff
  review) and record verdicts in `STEPB_PLAN.md`.
- If you catch yourself writing a `theorem … := by …` body, stop — that is an
  executor's job. Write the kickoff prompt instead.

## Read these first, in order (they ARE the spec)

1. `CLAUDE.md` (repo root) — binding conventions. Non-negotiable:
   - **All Lake ops via `scripts/lake-locked.ps1`** (PowerShell): `claim`
     before editing, `check`/`build` to verify, `release` after. NEVER invoke
     `lake` directly. `status` before assuming a file is free (other sessions
     hold claims).
   - Honest nested %: a theorem is **0% until stated AND proved** in Lean,
     reported SEPARATELY from supporting machinery. NEVER push (the human
     pushes).
   - **Honest-input rule**: a `[~]` honest-input field is allowed ONLY where the
     book itself cites an external theorem. Everything the book proves, we prove.
2. `…/HCGCompactness/CHAPTER4_PLAN.md` — the master Ch4 plan. Read the DONE
   section, the §3 Step B section, and the "Critical path". Step A is now DONE
   (item 3 completed 2026-06-13); F7/F8 are DONE; F1–F6 are done/honest-input.
3. The book, `RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter4.tex`,
   **lines 1370–1882** (the whole of Step B). Anchor labels: `lbl394` (L1371,
   local metrics & transition limits), `lbl395` (L1416, the normal-coordinate
   metric bounds), `lbl396` (L1504, constructing `F_{kℓ;r}`), `lbl397` (L1515,
   the MAIN result — approximate isometry on a large ball), `lbl399` (L1554),
   `lbl402` (L1734), `lbl403` (L1749, `F_{kℓ;r}` is a local diffeo), `lbl404`
   (L1765, limit of almost-identity pullbacks), `lbl405` (L1835, final
   assembly).
4. The same-name notes for what Step B consumes (all under `…/HCGCompactness/`
   unless noted): `MapConvergence.md`, `IsometryCompactness.md` (F7/F8),
   `StepBInputs.md`, `B0NormalCoordBounds.md`, `ConvexBalls.md`,
   `ExpBallDiffeo.md`, `GoodCoveringItem3.md`, `ApproxIsometryCompHigher.md`,
   `Lemma45F4.md`, and the Step A memory in `CHAPTER4_PLAN.md`'s §2.
5. `convention.md` + `dictionary.md` (repo root area) for tensor/coordinate
   conventions before drafting any statement shape.

## Snapshot — what is already DONE and reusable (verify against `git log`)

These are the Step B inputs; they are green + axiom-clean unless noted.

- **F8 = `lbl374` "Compactness of a sequence of isometries"**:
  `IsometryCompactness.lean:isometry_seq_diffeo`. Given total smooth maps
  `Φ : ℕ→E→F`, `Ψ : ℕ→F→E`, the honest-input `IsometryDerivBounds` (all
  iterated derivatives uniformly bounded on every compact) for both, and
  `Φₖ∘Ψₖ = id = Ψₖ∘Φₖ`, it produces a subsequence converging **C^∞ on
  compacts** to a smooth diffeomorphism `Φ_∞` with smooth two-sided inverse
  `Ψ_∞` (the cocycle `Ψ_∞∘Φ_∞ = id`). **This IS the lbl394 transition-map limit
  engine.** Consume it; do NOT edit `MapConvergence.lean`/`IsometryCompactness.lean`.
- **F7 = AA-for-maps engine**: `MapConvergence.lean:exists_cInf_subseq` — smooth
  `Φₖ:E→F` with all `∇ʳΦₖ` uniformly bounded on compacts ⇒ a C^∞-on-compacts
  convergent subsequence to a smooth limit. The convergence vocabulary
  (`MapCPConvOn`, `MapCInfConvOnCompacts`, `IsometryDerivBounds`) lives here.
- **Item 3a = the `H_k^α = exp∘L` ball diffeomorphism**:
  `Comparison/ExpBallDiffeo.lean:exists_expBall_diffeo_of_lt` (UNCONDITIONAL: for
  `ofReal r < injRadius g p` and `r ≤ expMapC2Radius g p`, exp restricts to a
  `C^1` `PartialDiffeomorph` on `ball 0 r`). Net-level wiring:
  `GoodCoveringItem3.lean:exists_seqItem3Diffeo`.
- **S6 / `lbl418` honest-input (transition-map derivative bounds)**:
  `StepBInputs.lean` — `normalTransition X x y : E→E` (= the model-coordinate
  transition `normalChart_y ∘ exp_x`, i.e. the book's `J_k^{αβ}` in coordinates),
  `NormalTransitionDerivBound`, and the honest-input `ExpInverseDerivBoundInput`
  (uniform `C^p` bounds for the transition maps on chart overlaps; the book
  cites this to §5 / [H6]).
- **Step A net**: `GoodCoveringSeq.lean` — `seqCenter`/`seqRadius`, the
  `NetLimitData` with the diagonal subsequence, the `lbl383` items (centers
  `x_k^α`, radii `λ^α`, intersection stability item 6 = `lbl383(6)`, the
  `A(r)`/`K(r)` functions). `exists_stableNetData` is the capstone.
- **F1–F6 approx-isometry algebra**: `ApproxIsometryDefs.lean`,
  `ApproxIsometryComp.lean`, `ApproxIsometryCompHigher.lean` (`comp_cov_le`,
  `comp_cov_accum`), `Lemma45F4.lean:lemma45_corII` (Cor II, norms of covariant
  derivatives under approx-isometry equivalence). These are the `(ε,p)`-approx
  composition tools `lbl402`/`lbl405` consume.
- The Jacobi/Grönwall tower built for item-3a (`CovariantGronwall.lean`,
  `InnerExpansion.lean`, `ExpNonsingular.lean`, the ∞→finite parallel-transport
  refactor) is reusable analysis — it is the natural native route to **lbl395**
  if you choose NOT to take lbl395 as honest-input.

## The Step B math chain (what you are planning)

`lbl394` (transition + metric limits) → `lbl396`/`lbl397` (approximate isometry
`F_{kℓ;r}` on `B(O_k,r)`, MAIN result), via `lbl399`/`lbl402`/`lbl403`/`lbl404`/
`lbl405`. Concretely:

1. **lbl395** (normal-coord metric bounds `½δ≤g≤2δ`, `|∂^α g_{ij}|≤C̃_{|α|}` on
   `B(p,min(c₁/√C₀,r₀))`). The book PROVES nothing here — it cites [H6] Cor 4.12.
   ⇒ a legitimate **honest-input** (the book's own external boundary).
2. The pulled-back metrics `ḡ_k^β = (H̄_k^β)^* g_k` on Euclidean balls have
   uniformly bounded derivatives (from lbl395) ⇒ AA ⇒ **limit metrics `g_∞^β`**.
3. The transition maps `J_k^{αβ} = (H̄_k^β)^{-1}∘H_k^α` are Riemannian
   isometries between `ḡ_k^α` and `g⃗_k^β` with bounded derivatives ⇒ apply
   **F8 (`isometry_seq_diffeo`)** ⇒ **limit transition maps `J_∞^{αβ}`** with the
   cocycle `J_∞^{βα}∘J_∞^{αβ}=id`.
4. **lbl397**: assemble `F_{kℓ;r}` from the per-α maps `F_{kℓ}^α=H_ℓ^α∘(H_k^α)^{-1}`
   via the **center of mass (Step C, `lbl410`)** to glue overlaps ⇒ an
   `(ε,p)`-approximate isometry on `B(O_k,r)`. NOTE: lbl397 is **gated on Step C**;
   the transition/metric limits (1–3) are NOT.

## Design questions you must rule on BEFORE writing kickoff prompts

These are the genuine forks; decide each and record the ruling in `STEPB_PLAN.md`.

- **(Q1) lbl395 — honest-input or native?** The book cites [H6] Cor 4.12, so
  honest-input is legitimate and unblocks all of Step B immediately. Native
  (the Jacobi/Grönwall route, partly built) is more faithful but multi-session.
  RECOMMENDATION to weigh: take lbl395 as honest-input now (a `NormalCoordMetricBound`
  structure, sibling of `ExpInverseDerivBoundInput`), keep the native route as a
  later optional discharge. Decide and justify.
- **(Q2) The partial-domain gap — THE central Step B obstruction.**
  `isometry_seq_diffeo` and `exists_cInf_subseq` take **total** maps `E→F` with
  `IsometryDerivBounds` = bounds on **all** compacts and conclude convergence on
  `Set.univ`. But the transition maps `J_k^{αβ}` and pulled-back metrics live on
  **bounded Euclidean balls** `E^α` (junk outside; `normalTransition` already
  returns junk off the overlap). So F8 does NOT apply to the raw total
  `normalTransition`. You must choose the bridge:
  (a) commission a **localized F7/F8** (`exists_cInf_subseq_on K` /
      `isometry_seq_diffeo_on K`: bounds on a neighborhood of a fixed compact `K`
      ⇒ convergence on `K`) — a self-contained variant reusing the AA engine; or
  (b) **extend** the transition maps to total smooth bounded maps (a smooth
      cutoff to a fixed total map agreeing on the ball) and apply F8 as-is; or
  (c) restrict to a fixed inner ball `Ē^β ⊂ E^β` and carry the convergence only
      there (what the book actually uses — the `Ē`/`E⃗` nesting exists precisely
      so the limit lives on a slightly smaller ball).
  Decide (a/b/c). This single ruling determines the shape of every convergence
  brick. (My scouting leans (a) or (c): the book's `B⊂B̄⊂B⃗` nesting is exactly
  the "shrink the domain" device, so (c) is the most faithful and (a) is the
  reusable engine that realizes it.)
- **(Q3) Metric convergence engine.** The pulled-back metric `ḡ_k^β` is a map
  `E → (E →L[ℝ] E →L[ℝ] ℝ)` (Gram form, finite-dim target). Reuse
  `exists_cInf_subseq` (or its localized variant from Q2) on that map directly,
  vs. a dedicated metric-AA. RECOMMENDATION: reuse the map engine on the
  bilinear-form-valued map — no new engine. Confirm the target is a proper
  finite-dim normed space (`cmm_finiteDimensional`-style) so AA applies.
- **(Q4) How much of the `H_k^α`/`J_k^{αβ}`/`g_k^β` data to model explicitly.**
  The cleanest is to keep these at the model-coordinate level (`E→E` maps and
  `E→bilinear` metrics, as `normalTransition` already does) so F7/F8 apply
  directly, and only touch the manifold via the existing `PointedRiemannian`
  bridge (`GoodCoveringItem3.exists_expBall_diffeo`). Rule on the data layout
  and the file split (suggest: `StepBLocalMetrics.lean`, `StepBTransition.lean`,
  `StepBApproxIso.lean`, with honest-inputs extending `StepBInputs.lean`).

## Suggested brick decomposition (refine it; this is a starting skeleton)

- **B-input** — lbl395 honest-input `NormalCoordMetricBound` (per Q1) +
  the immediate corollary "the pulled-back metric `ḡ_k^β` has `IsometryDerivBounds`".
- **B-loc** — the localized F7/F8 (per Q2(a)), IF chosen: `exists_cInf_subseq_on`
  and `isometry_seq_diffeo_on` over a fixed compact. (Reuses the AA engine; the
  hardest analysis brick. Skip if Q2 picks (b)/(c).)
- **B-metric** — the lbl394 **metric limit** `g_∞^β` from B-input + B-loc/F7.
- **B-trans** — the lbl394 **transition limit** `J_∞^{αβ}` + cocycle, from
  `normalTransition` + S6 bounds + the isometry property + B-loc/F8. This is the
  flagship Step B brick (directly consumes your F8).
- **B-Fα** — `F_{kℓ}^α = H_ℓ^α∘(H_k^α)^{-1}` and its approx-isometry estimate
  `lbl399` (per-α, via F1/Lemma45 + the metric closeness).
- **B-glue** (`lbl397`/`lbl402`/`lbl405`) — the center-of-mass gluing into
  `F_{kℓ;r}`. **GATE on Step C (lbl410 center of mass).** Plan it but mark it
  blocked-on-C; sequence the unblocked bricks (B-input … B-Fα) first.

## Coordination — critical, multi-agent

- `./scripts/lake-locked.ps1 status` before assuming a file is free. A parallel
  session is active on the **P3/Lemma 3.11 track** (files like `MetricPreconv*`,
  `RicBound*`, `StarSum*`, `NablaTraceGen.lean`, `MetricCovDerivTimeDeriv.lean`,
  `AllTimesBounds.lean`) — those are OFF-LIMITS to Step B executors.
  **Consume-only (never edit):** `MapConvergence.lean`,
  `IsometryCompactness.lean`, `Lemma45*.lean`, `ApproxIsometry*.lean`,
  `GoodCoveringSeq.lean`, `GoodCoveringOrdered.lean`, `ExpBallDiffeo.lean`.
- The refactor that generalized the parallel-transport chain to finite order
  (`ParallelTransport.lean` etc.) cascaded olean rebuilds; expect targeted
  builds to be slow when they run after the parallel session — wait, don't
  force-release locks.
- NEVER push.

## Your immediate tasks (do these now, in order)

1. **Verify Step B feasibility against the book + the snapshot above** — confirm
   that lbl394's two limits (metric + transition) reduce to F7/F8 + lbl395 + S6
   with ONLY the Q2 partial-domain bridge as new analysis, and that lbl397 is
   the only Step-C-gated piece. If any link is missing infrastructure, say so
   loudly (that is a feasibility finding, not a brick).
2. **Make the four rulings (Q1–Q4)** and record them as dated "PLANNER RULING"s
   in a new `STEPB_PLAN.md` (model its structure on `P3_PLAN.md` /
   `CHAPTER4_PLAN.md`: a brick board, acceptance criteria incl. the
   constants-first STRICT rule, the off-limits list, a traps table).
3. **Write the first kickoff prompt** — the smallest unblocked brick. Strong
   candidates: **B-input** (lbl395 honest-input, pure definition + corollary,
   zero new analysis) or, if Q2 chose (a), **B-loc** (the localized AA — the
   reusable engine everything else needs). Present it to the human to dispatch.

## Kickoff prompt template

```
Work in DifferentialGeometry/ on branch short-time-existence. You are the
implementing agent for <BRICK ID> of MSM135 Chapter 4 Step B (HCG compactness).

1. Read in order: CLAUDE.md; HCGCompactness/STEPB_PLAN.md (<brick section> +
   the acceptance/coordination/traps sections — note the STRICT constants-first
   rule); chapter4.tex lines <the book range for this brick>; then <the exact
   same-name .md notes carrying your inputs, by name>.
2. Implement <BRICK> in <file>: <target Lean statement draft when shape matters>
   <route, citing the exact reuse lemmas by name — e.g. isometry_seq_diffeo,
   exists_cInf_subseq, lemma45_corII, ExpInverseDerivBoundInput>. Honest-input
   only where the book cites externally. STRICT constants-first on every new ∃.
3. Claim files via ./scripts/lake-locked.ps1; consume-only files per STEPB_PLAN;
   off-limits = the P3/Lemma-3.11 track.
4. Acceptance: focused check + targeted build green, #print axioms clean
   ([propext, Classical.choice, Quot.sound] only) on the endpoints, update the
   same-name .md, commit locally, NEVER push. 3-failures rule per CLAUDE.md;
   STOP and report to the planner if <the planner-reserved frontier for this
   brick — e.g. the Q2 partial-domain decision, or a missing F8 hypothesis shape>.
```
