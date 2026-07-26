# ThreeArmTopSeparated.lean — construction note (NOT built; blocked at Step 0's assembly premise)

## 2026-07-22/23 — data-weighted threeArm coefficient assembly: STEP 0 done, assembly BLOCKED

Dispatched as "the convergence point of the five constituent producers" (arm0Base, arm1Base,
connDiff, Lie/kernelField, traceHess): resolve №7's open question (STEP 0), then assemble the
data-weighted top-separated jet-L2 bound for the threeArm coefficient `C₀` (ideally `+C₁`) by
(a) the committed `C₀ = sum-of-fields` decomposition in the frozen
`DeTurckRemainderTameLipschitz.lean`, (b) triangle/Cauchy–Schwarz over the constituents, (c) the
five landed summed producers.

**Outcome: STEP 0 verdict = ABSORBED (recorded below).  The assembly TASK is blocked by a
structural mismatch discovered while reading the threeArm consumption shape: the five landed
producers are NOT the constituents of the committed reference `C₀`, and `C₀`'s genuine Lie
constituents have no data-weighted (top-separated) producer.  No Lean file was written — an
assembly of these five fields labelled as `C₀` would be mathematically wrong (mislabelled), and an
abstract N-ary triangle combinator would be orphan machinery.  The honest next step is a NEW
producer (deTurck-Lie top-separated), not the assembly.**

---

## STEP 0 — verdict: ABSORBED (traceHessian does NOT force a `Kc` upgrade)

Question (plan §"Planner acceptance №7"): does the assembled threeArm coefficient bound need TRUE
data-weighting from the traceHessian term, or is its constant `Kc·(1+low)` contribution absorbed?

**ABSORBED.**  The consumption shape (from `SobolevNonlinearityExistence.md`, the two orientations)
is, per coefficient field,
`∑_{i≤a}‖∇^i F‖² ≤ Ktop·(‖T‖²_{a+2}+‖T'‖²_{a+2}) + Kc·(1+‖T‖²_{a+1}+‖T'‖²_{a+1})`, combined into
`C₀`'s bound.  Orientation 2 (`max‖T‖_{a+2}‖T'‖_{a+2}·‖T−T'‖_{a+1}`) is fed ONLY by the
top-split `Ktop` parts; orientation 1 (`(1+low)·‖T−T'‖_{a+2}`) absorbs the `Kc·(1+low)` parts.
`traceHessianCoeff` has `Ktop = 0` **structurally** (it is a purely algebraic cometric `g₁⁻¹`
coefficient with no covariant-derivative gain — `TraceHessJetL2Summed.md`), so it contributes
nothing to orientation 2, and its `Kc·(1+low)` lands wholly in orientation 1's allowed low factor.
The ruling's stop-signal discipline protects only `Ktop` (must stay `(g₀,hδ₀)`-only); a constant /
ball-uniform `Kc` is the accepted house pattern (plan §№4).  Hence a traceHessian `Kc` upgrade is
NOT a prerequisite for the assembly — its current uniform-constant `Kc` is shape-compatible and
absorbed.  (This matches the "expected" branch the dispatch anticipated.)

---

## The blocker — the five producers are NOT `C₀`'s constituents (verified at HEAD `922dbc4ac`)

### What the committed reference `C₀` actually decomposes into

`deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm`
(`DeTurckRemainderTameLipschitz.lean:36054`) produces `C₀ : SmoothCcTensor g₀ 2 2` with
`C₀ = C₀_arm + K₀` (`:36143`), where:
- `K₀` = background curvature-fold (`exists_deTurckPhiMetTotal_background_curvatureFold_of_symm`),
  T-independent ⇒ constant jet-L2 ⇒ absorbed into `Kc`.
- `C₀_arm = pathIntegralCoeffField g₀ 2 2 Ψ₀` from
  `deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm` (`:34758`, `:34868`),
  with the **(2,2)** path integrand (`:34827`)
  `Ψ₀ s = (-2)•linearizedRicciArm0Field(s) + (deTurckLieCoeffField(realizedFam s, g_bg)
            + lieCorr0Field(realizedFam s, g_bg))`.

So `C₀`'s constituents are all **(2,2)**:
1. `linearizedRicciArm0Field = linearizedRicciArm0BaseCoeff + linearizedRicciArm0CorrField`
   (frozen `:2047–2050`).  Base part: my producer ✓.  Corr part: only ball-uniform
   (`linearizedRicciArm0CorrField_perOrder_rfns_ballUniform`); its data-weighted tame-envelope
   lives in `RicciThreeArmCorrectionFieldTameEnvelope.lean` (linearized-Ricci correction layer).
2. `deTurckLieCoeffField g₀ g₁ g_bg` — the **(2,2)** DeTurck-Lie order-0 coefficient `Δ_Lie`
   (`RicciDeTurckSectionDifference.lean:7716`, `g_bg`-DEPENDENT).  Only ball-uniform bound
   (`DeTurckLieCoeffL2JetBound.lean:429`).  **No top-separated producer anywhere.**
3. `lieCorr0Field g₀ g₁ g_bg` — **(2,2)**, `g_bg`-DEPENDENT (`DeTurckCoefficients/LieCorr0Core.lean:583`).
   Only ball-uniform.  **No top-separated producer.**

`C₁` (`:34833`): `Ψ₁ = (-2)•linearizedRicciArm1Field + deTurckLieArm1Coeff` — arm1Base ✓ (mine),
arm1Corr (ball-uniform), `deTurckLieArm1Coeff` (ball-uniform, no top-separated producer).
`C₂` = `deTurckPhiTotPathIntegral − deTurckPhiMetTotal(g₀)` (deviation; already R-independent via
`deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform` — do not redo).

### Why the five landed producers do not fit

The five topSeparated (data-weighted) producers that exist are for
`{linearizedRicciArm0BaseCoeff (2,2), linearizedRicciArm1BaseCoeff (3,2),
connDiffContrInsertionField (3,4), linearizedRicciConnDiffOrder1KernelField (3,4),
traceHessianCoeff (4,2)}`.  Against `C₀`'s **(2,2)** constituents:
- `arm0BaseCoeff` ✓ is the ONLY landed producer that is a genuine `C₀` constituent.
- `arm1BaseCoeff` is a `C₁` (3,2) constituent; `traceHessianCoeff` is a `C₂` (4,2) constituent —
  neither is a `C₀` constituent (valence mismatch, and different arm).
- `connDiffContrInsertionField`, `linearizedRicciConnDiffOrder1KernelField` are **(3,4)** and
  `g_bg`-INDEPENDENT.  They cannot be `C₀`'s (2,2), `g_bg`-dependent constituents.  In the frozen
  file they appear ONLY inside the `b3_`/`b4_` private engine helpers (`:40196–:42170`) — the deep
  per-slot rfns engines the connDiff/kernelField producers rest on — NOT in the `C₀` threeArm
  assembly (`:34758–:36180`).  They belong to the linearized-Ricci correction / LowReg / Edge
  family (`RicciConnDiffOrder1TameEnvelope`, `RicciThreeArmCorrectionFieldTameEnvelope`,
  `LowReg*`, `Edge*`), a different decomposition of a different operator.

### No bridge identity exists

- The ONLY file containing both `connDiffContrInsertionField` and `deTurckLieCoeffField` is the
  frozen `DeTurckRemainderTameLipschitz.lean`, and there they sit in disjoint regions with no
  connecting `_eq_` lemma.  `deTurckLieCoeffField`'s ball-uniform proof
  (`DeTurckLieCoeffL2JetBound.lean`) does NOT go through connDiff/kernelField (no mention).
- `deTurckLieCoeffField` is `g_bg`-dependent (3 metrics); `connDiffContrInsertionField` is
  `g_bg`-independent (2 metrics).  A difference-level `g_bg`-cancellation
  (`deTurckLieTerm(g₁,g_bg) − deTurckLieTerm(g₁',g_bg) = f(connDiff)`) is mathematically plausible
  (the DeTurck VF is built from the connection difference and the same `g_bg` on both sides) but is
  **NOT a committed identity** anywhere in the tree — it would be a NEW tensor-algebra derivation,
  not a copy-paste of an existing decomposition.
- There is NO `topSeparated` producer for `deTurckLieCoeffField`, `lieCorr0Field`, or
  `deTurckLieArm1Coeff` (grep confirms only the five listed above exist).

### Why `C₀`'s Lie constituents genuinely need data-weighting (cannot be absorbed like traceHess)

`SobolevNonlinearityExistence.md` (orientation 2) states the low arms `A₀,A₁` — the
"linearized Ricci arm0/arm1 + connection-difference/Lie fields" — genuinely carry `∂²(path)`
content, so their bounds scale like `‖T‖_{a+2}` (`Ktop ≠ 0`).  The DeTurck-Lie order-0 coefficient
multiplies `∇⁰(T−T')`, and its own order-`a` jet reaches `∇^{a+2}T` (the DeTurck VF `≈ g⁻¹·∂g`,
`L_W g ≈ ∂²g`), so `deTurckLieCoeffField` IS a top-window contributor.  Its ball-uniform bound
(R-opaque) cannot expose that `‖T‖_{a+2}` factor — exactly the reference's `ΛC ~ R` lumping the
route test flagged.  So absorbing it into `Kc` (as traceHess is legitimately absorbed) would be
mathematically wrong: it would drop the orientation-2 data weight the ruling's time integration
`‖A·B‖_{L²_t} ≤ ‖A‖_{L^∞_t H^{a+1}}‖B‖_{L²_t H^{a+2}}` requires.

---

## Smallest next step (the real frontier)

Build a data-weighted **top-separated** summed producer for `deTurckLieCoeffField` (and
`lieCorr0Field`, then `deTurckLieArm1Coeff` for `C₁`), mirroring the arm0Base shape
`∑_{i≤a}‖∇^i F‖² ≤ Ktop·(top) + Kc·(1+low)` with `Ktop` `(g₀,hδ₀)`-only.  This is a per-field
producer task of the same kind as the five already landed (each ~180–350 lines over its own
session), NOT a one-session assembly.  It must be derived from `deTurckLieCoeffField`'s own
structure (`RicciDeTurckSectionDifference.lean` / `DeTurckLieCoeffL2JetBound.lean` /
`DeTurckCoefficients/`), since it does not factor through the connDiff/kernelField engines.

Alternatively (planner decision): if a NEW `C₀ = f(connDiff/kernelField)` decomposition is
intended (difference-level `g_bg`-cancellation), that algebraic identity must be stated and proved
first (a genuine tensor-calculation frontier) — it is the missing "step (a)".  Only then do the
connDiff/kernelField producers become usable, and even then a contraction (appCcRS with a cometric,
to drop (3,4)→(2,2)) is needed.

**Recommendation for the planner:** confirm which `C₀` decomposition the assembly should target —
(i) the committed frozen reference (`:36054`, needs deTurck-Lie top-separated producers), or
(ii) a new connDiff-routed decomposition (needs a new algebraic identity + a contraction step) —
because the "five producers converge into `C₀`" model does not hold against the committed tree.

## Verification status

No Lean written (see rationale above; a compiling-but-mislabelled or orphan lemma was deliberately
not produced).  All claims above are `grep`/`Read` forensics against HEAD `922dbc4ac` in the
worktree `C:/Users/liao9/.codex/worktrees/e87b/...`.  Guardrails respected: nothing committed, no
dirty tracked file edited (elaboration never entered
`CurvatureCoefficientDifferenceJetTower.lean`), frozen file only read.  (N)
`ricci_flow_unif_existence` remains **0%**.
