# StepCProducers.lean — C3 producer join (design/audit note, 2026-07-02)

## PROGRESS 2026-07-09: fixed-source explicit-weight join landed

`stepCJoinDataFixed` is verified without `sorry`.  It mirrors `stepCJoinFixed`'s
geometry/transition inputs, but consumes `mu` together with
`centerAverage.WeightDataOn hatSourceBall hatBall mu` and calls
`NetLimitData.unifHatCageData`.  The existing `Item3GpScaleInput` and closed-set
limit bridge still discharge the radius and `Binf`-membership obligations; no new
abstract producer hypothesis was introduced.

Scope boundary: this endpoint is complete for weights active in the current
`4 * lamInf` `hatBall`s.  It is not the textbook `5 * lamInf` support-ball
instantiation; the support-set adapter needed to feed those book weights remains
open.  Consequently this local fixed-source endpoint is 100%, while the book
support instantiation and the unconditional `StepB1RawInput` producer remain 0%;
the rounded whole-project totals do not change.

**Status (2026-07-02, session 2): step 1 LANDED; join structure resolved; join not yet built.**

## PLANNER RULING #2 (2026-07-02) — uniform-`U γ` tension: parametric σ-shape; join in ONE session

The step-(2) tension (cage image bounded at the fixed index `L.φ n` vs `existsTransUniv`'s
`hUx` at every `k`) is resolved by a SHAPE choice, not new geometry. `Item3RadiusInput` already
quantifies over EVERY `k` at live centers (`ρ k α ≤ expMapC2Radius (X.obj k).metric c`), and
`L.lamInf γ` is k-independent — the book's cover radii are the k-independent λ-scale. So:

**Build the join PARAMETRIC over a k-independent per-hat radius family `σ : Fin (pb.A r) → ℝ`**
with honest containment hypotheses in the established Step-B style:
- `hσx : ∀ k γ (live centers c), σ γ ≤ expMapC2Radius (X.obj k).metric c` — literally
  `Item3RadiusInput` at a constant-in-k `ρ`, so `U γ := Metric.ball 0 (σ γ)` discharges
  `hUx`/`hVy` by projection;
- `hcage : normalChartAt (center γ) '' hatSourceCage γ ⊆ ball 0 (σ γ)` — the σ-refined cage
  bound (today's `hatCageImg` is the `expMapC2Radius (center γ)` version; the σ version is the
  tightened `4·lamInf/√coercive ≤ σ` variant);
- overlap/cocycle (`hovlJ/hovlJbar/hLeft/hRight`) likewise parametric (`existsTransUniv` style).

Do NOT block the join on discharging these quantitatively. The quantitative follow-up (the
coercive-tightened `hatCageImg'` + `σ` from the λ-window) is separable; if the `4λ/√c ≤ σ`
comparison proves opaque (same `Classical.choose`-radius reason as before), it is PRE-APPROVED
as another sibling field in the same `lbl383`/"D large enough" honest scale family
(`Item3GpScaleInput` precedent) — do not invent a different mechanism.

**Increment sizing (explicit): the next session's target is the COMPLETE parametric join** —
steps (2)+(3)+(4) in one pass: σ-parametric domain inputs, parametric overlap/cocycle, the
`existsTransUniv` call at `ι = Fin (pb.A r)` on `X∘L.φ`, `L.subseq` refinement, `hR` via
`Item3GpScaleInput`, `hstrict` threaded, endpoint = the averaged-map two-index `→id` statement
feeding `unifHatCageSelfComp`. Do not stop after one sub-lemma; stop only on the standard stop
conditions (3 failed routes on one theorem / missing API / ruling-book mismatch) or when the
join is green. A ~200-line mechanical threading is one session's work once parametric.

## PROGRESS 2026-07-03 (session 6): C3 JOIN COMPLETE — (A)+(B) green, axiom-clean, no sorry

`stepCJoin` (shape B) LANDED: `lake build` green (3841 jobs),
`#print axioms = [propext, Classical.choice, Quot.sound]`, no sorry. The full C3 producer
join is now done: `existsTransUniv` (on the reindexed `X.subseq L.φ`, `input.subseq L.φ`)
produces the subsequence `phi` + `C∞` limit maps `Jinf/Jbarinf` + two-sided cocycle; then
`stepCJoinFixed` averages them to the identity on the frozen source ball.

Endpoint: `∃ phi, StrictMono phi ∧ (∀ eps>0, ∃ N, ∀ a,b ≥ N, ∀ x ∈ hatSourceBall,
dist x (centerAverageOn … (decodedCompPts … (normalTransition-at-φ maps)) …) < eps)` — the
averaged concrete-Step-B-map → id statement B1 consumes.

Transcription facts that mattered (all resolved, no design change):
- Needed `import …C4.StepCTransitionRefine` (for `existsTransUniv`, `normalTransition`,
  `NormalOverlapOn`, `ExpInverseDerivBoundInput`) + `open …Riemannian.NormalCoordinates`
  and `.Exponential` (for `expMapDiffeo`/`expMap`). `maxHeartbeats 1600000`.
- Map-dependent hyps `hactive0/hstrict0/hmap0/hKV0` stated over ALL indices; specialised at
  `phi` by `fun a b => h (phi a) (phi b)`. `radSeq`/`hrad` likewise reindexed
  (`fun a b => radSeq (phi a) (phi b)`). The `decodedCompPts` reindexing defeq held exactly
  as predicted — `exact stepCJoinFixed …` closed with no `simp`/`show` bridging.
- `existsTransUniv` output 8-tuple projections: hB=`.2.2.2.2.1`, hA=`.2.2.2.2.2.1`,
  hBcont=`.2.2.1`, hAcont=`.2.2.2.1`, hid=`.2.2.2.2.2.2.1`. The `X.subseq L.φ` vs
  `X.obj (L.φ ·)` defeq let hB/hA pass directly.

**Remaining for the σ quantitative follow-up (separable, pre-approved):** the `existsTransUniv`
domain inputs `hUx/hVy` and the cage inputs `hKU/hKV0` are threaded parametrically (honest,
existsTransUniv's own style). A later lemma can discharge them from a k-independent `σ` family
(coercive-tightened `hatCageImg'` + `σ` from the λ-window; the `4λ/√c ≤ σ` comparison is
pre-approved as a sibling `lbl383` scale field if opaque — Ruling #2). Not needed for the join
theorem, which is complete.

## PROGRESS 2026-07-02 (session 5): shape (A) `stepCJoinFixed` LANDED — green, axiom-clean

`stepCJoinFixed` in StepCProducers.lean: `lake build` green (3838 jobs), no sorry,
`#print axioms = [propext, Classical.choice, Quot.sound]`. It IS
`NetLimitData.unifHatCageSelfComp` with the two producer-integration obligations discharged
in-body from the honest bridges:
- `hR := fun γ => hgp n γ (center γ) (hcenter γ)` (the `Item3GpScaleInput` field `hgp`);
- `hKV := fun γ v hv => hV'sub γ (binfMemClosed (hB γ) (hKU γ hv) (hV'closed γ) (hKV0 γ v hv))`
  — the closed sub-ball `V' γ ⊆ V γ` absorbs the `C∞`-limit of the two-index maps.
`B/A/Binf/Ainf` stay abstract (so the ~40-line conclusion copies from unifHatCageSelfComp
verbatim). Transcription gotcha found+fixed: `decodedCompPts` and `unifHatCageSelfComp` live in
`namespace NetLimitData` (StepCAveragePOU 251–3275) → must be `NetLimitData.`-qualified from
this file. Needed `set_option maxHeartbeats 800000`.

### Shape (B) outer wrapper — REMAINING (verified mechanical, ~150 lines)
Not written (second ~40-line conclusion copy + ~15 `existsTransUniv` params overran budget).
Recipe, with the one non-obvious point now VERIFIED:
- Params add `existsTransUniv`'s inputs on `X.subseq L.φ`: `x y : Fin (pb.A r) → ∀ k,
  ((X.subseq L.φ).obj k).M`, `U V`, `hU hV hovlJ hovlJbar hUx hVy hmapsJ hmapsJbar hLeft hRight`,
  plus the all-index (phi-free) `hactive0 hstrict0 hmap0 hKV0` (over `Bfull γ a :=
  normalTransition ((X.subseq L.φ).obj a) (x γ a) (y γ a)`).
- Body: `obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ := existsTransUniv (I:=I) (X := X.subseq L.φ)
  (input.subseq L.φ) x y U V hU hV hovlJ … hLeft hRight`; `refine ⟨phi, hphi, ?_⟩`;
  `exact stepCJoinFixed … (B := fun γ a => normalTransition ((X.subseq L.φ).obj (phi a))
  (x γ (phi a)) (y γ (phi a))) (Binf := Jinf) (A := …(y…)(x…)) (Ainf := Jbarinf)
  (hactive_mem := fun a b y hy => hactive0 (phi a) (phi b) y hy) (hstrict := similarly)
  (hmap := similarly) (hKV0 := fun γ v hv a => hKV0 γ v hv (phi a)) (hB := fun γ => (hspec γ).…) …`.
- **VERIFIED DEFEQ** (was the only worry): `NetLimitData.decodedCompPts center (fun γ a =>
  Bfull γ (phi a)) (fun γ b => Afull γ (phi b)) a b x γ` reduces to `… center Bfull Afull
  (phi a) (phi b) x γ` (both = `normalChartAt(center γ).symm (Afull γ (phi b) (Bfull γ (phi a)
  (chart x))))`). So `hactive0 (phi a) (phi b)` has EXACTLY the type stepCJoinFixed's
  `hactive_mem a b` needs at the concrete maps — no `simp`/`show` bridging required.
- (B)'s conclusion = `∃ phi, StrictMono phi ∧ <stepCJoinFixed's conclusion with the concrete
  phi-maps and `hactive0 (phi ·) (phi ·)` / `hstrict0 (phi ·) (phi ·)` substituted>` (these
  proof terms ARE referenced in the conclusion because `centerAverageOn` embeds the per-point
  `inputOfFillSelf` — but `phi` is ∃-bound and `hactive0/hstrict0` are params, so it is
  statable). `hUx/hVy` discharged from `hσx` (`U γ := ball 0 (σ γ)`), overlap/cocycle threaded.

## PROGRESS 2026-07-02 (session 4): ALL producer bridges LANDED; join = pure transcription

`binfMemClosed` added + verified (targeted build green, 3838 jobs). Every non-mechanical
obligation of the join now has a named, verified discharge lemma. The join theorem itself
(the `existsTransUniv → unifHatCageSelfComp` assembly) was NOT written this session: its
conclusion is the ~30-line `centerAverageOn`/`inputOfFillSelf` expression from
`unifHatCageSelfComp` (StepCAveragePOU:3223-3254) which must be restated verbatim with the
concrete maps, and the theorem carries ~25 hypotheses — a genuine 150-250-line transcription
that overran the safe single-session budget after the bridge work. It is now purely
mechanical (no design/API gaps remain). **Verified bridge inventory (all in StepCProducers.lean
unless noted):**
- `Item3GpScaleInput` (+ `.subseq`) — GoodCoveringItem3.lean — discharges `hR`.
- `properBallImgOfRad` / `hatCageImg` — cage image ⊆ `ball 0 (expMapC2Radius)`; discharges
  `hKU`/`hmap`-domain routing (with `hcage`).
- `binfMemClosed` — `MapCInfConvOnCompacts` + closed `V'` ⇒ limit ∈ `V'`; discharges `hKV`.
- `hatCageSrcOfRad` (existing) — cage ⊆ chart source (`hsource`).
- `StepCTransitionRefine.existsTransUniv` — produces `phi, Jinf, Jbarinf, hB, hA, hid,
  hBcont, hAcont` from parametric overlap/cocycle/domain inputs.

### MECHANICAL JOIN RECIPE (next session: transcribe, no design left)
Theorem `stepCAveragedIdJoin` (in StepCProducers.lean). Two viable shapes:
(A) **phi-as-parameter** (simpler, ~120 lines, no existential conclusion): take
`phi hphi Jinf Jbarinf` + the `existsTransUniv` convergence spec as parameters. Set
`B γ := fun a => normalTransition (X.obj (L.φ (phi a))) (x γ (phi a)) (y γ (phi a))`,
`A γ := fun b => normalTransition … (y…) (x…)`, `Binf γ := Jinf γ`, `Ainf γ := Jbarinf γ`.
`exact unifHatCageSelfComp …` with:
- `hcenter` (param, index n, orig L); `hR := fun γ => hgp n γ (center γ) (hcenter γ)`;
- `hB/hA/hBcont/hAcont/hid := ` the convergence-spec params (from `existsTransUniv`);
- `hKU γ := hcage γ` (`hatCageImg` gives `normalChartAt(center γ) '' cage ⊆ ball 0 σ` = `U γ`);
- `hKV γ v hv := binfMemClosed (hB γ) (hKU γ hv) hV'closed (hmem γ v)` where `hmem`/`V'` threaded
  (all-`a` `B γ a v ∈ V'` closed ⊆ `V γ` open);
- `hmap/hactive_mem/hstrict/hrad` threaded for the concrete maps (fixed phi ⇒ no specialization);
- `rho/hrho/join/radSeq/hconn/hX` threaded.
Then (B) an outer wrapper obtains `phi …` from `existsTransUniv (X.subseq L.φ) (input.subseq L.φ)
x y U V …` and applies (A); its conclusion is `∃ phi, StrictMono phi ∧ (A's conclusion)` — the
only place the big conclusion is restated. Overlap/cocycle (`hovlJ/hovlJbar/hLeft/hRight`) +
`hUx/hVy/hmapsJ` are `existsTransUniv`'s parametric inputs (`U γ := ball 0 (σ γ)`, `hUx/hVy` by
`hσx` projection). All names verified to exist.

## PROGRESS 2026-07-02 (session 3): step (1) cage↔chart-image bridge LANDED + verified

`StepCProducers.lean` created (targeted build green, 3838 jobs; `sorry`-warnings only in
unrelated pre-existing files). Two theorems:
- **`properBallImgOfRad`** (general, sibling of `properBallSrcOfRad`): for `R < expRadiusGp g c`,
  `normalChartAt g c '' Metric.closedBall c R ⊆ ball 0 (expMapC2Radius g c)`. Proof reuses
  `metricBall_subset_normalBall` (chart vector `v` with `√(g_c(v,v)) = dist c q`), the round-trip
  `normalChartAt g c q = v`, and `norm_lt_expMapC2Radius_of_sqrt_inner_lt` (g_p-coercivity). All
  ingredients were already public — "verify then compose", no re-derivation.
- **`hatCageImg`** (C4 wrapper): under `hR` (= `Item3GpScaleInput` field), `normalChartAt(center γ)
  '' hatSourceCage γ ⊆ ball 0 (expMapC2Radius (center γ))`. Composes `hatCageInClosed` +
  `properBallImgOfRad`. The membership form (cage ⊆ chart source) is the EXISTING
  `hatCageSrcOfRad` (reuse). **Step (1) complete.**

### Step (2) FINDING — the `U γ` uniform-radius reconciliation (real design question)
`hatCageImg` gives the cage image bound at the FIXED manifold `X.obj (L.φ n)`. But the capstone's
`hKU : coordK γ ⊆ U γ` (coordK = cage image) must fit `U γ` while `existsTransUniv`'s
`hUx : ∀ k, U γ ⊆ ball 0 (expMapC2Radius (X.obj (L.φ k)).metric (x γ (L.φ k)))` demands `U γ` sit
inside the C²-ball at EVERY sequence index k. So `U γ` must be a **uniform** ball
`ball 0 ρ_γ` with `cage-image-radius(n) ≤ ρ_γ ≤ inf_k expMapC2Radius(x γ k)`. This requires:
(a) a uniform lower bound on `expMapC2Radius` (equiv. `Item3RadiusInput`'s `ρ k γ ≤ expMapC2Radius`
with `ρ k γ` uniformly bounded below in k — the book's `D·λ^γ` item-3 radius via the λ-window),
and (b) the cage image radius (`≤ 4λ^γ/√coercive`, a *tighter* coercive bound than `hatCageImg`'s
`< expMapC2Radius`) below that uniform `ρ_γ`. **Neither the tighter cage-image bound nor the
uniform-`ρ` lower bound is threaded yet.** Options for next session:
- prove a coercive-tightened `hatCageImg'`: `cage image ⊆ ball 0 (4·lamInf γ / √(gpCoerciveConst))`
  (leaves `expMapC2Radius` headroom), then choose `U γ := ball 0 ρ_γ` for a uniform `ρ_γ` from
  `Item3RadiusInput` and discharge both inclusions; OR
- thread `U γ` (+ `hUx`/`hKU`) as parametric hypotheses of the join (existsTransUniv style),
  deferring the uniform-radius quantitative choice to a later Step-A wiring lemma.
This is the genuine remaining frontier of the join (same uniform-radius wiring flagged in Step B).

## PROGRESS 2026-07-02

**Step 1 DONE — `Item3GpScaleInput` landed** in `GoodCoveringItem3.lean` (targeted build
green, `sorry`-warnings only in unrelated files; recorded in `CHAPTER4_PLAN.md` honest-input
boundary). It is `L`-relative: `∀ n γ c, seqCenter hd D P (L.φ n) γ = some c →
4 * L.lamInf γ < expRadiusGp (X.obj (L.φ n)).metric c`, so the capstone's `hR` is the
one-liner `hgp n γ (center γ) (hcenter γ)`. Also added `Item3GpScaleInput.subseq` (reindex
along `L.subseq hψ`; `lamInf`/`φ` transport by `subseq_lamInf`/`subseq_phi`).

**Join indexing RESOLVED (structural).** The capstone `unifHatCageSelfComp` is single-index:
`B,A,center : Fin (pb.A r) → …`, POU `rho` subordinate to `hatBall γ`, and
`decodedCompPts … center B A a b x γ` decodes summand `γ` via `center γ`. So the C3 join must
call `existsTransUniv` at **`ι = Fin (pb.A r)` (single index), not pairs**, with **parametric
per-hat point families** `x y : Fin (pb.A r) → ∀ k, (X.obj k).M`. Then
`B γ = fun a => normalTransition (X.obj (φ a)) (x γ) (y γ)`, `A γ = fun b => normalTransition …
(y γ) (x γ)`, `Binf γ = Jinf γ`, `Ainf γ = Jbarinf γ`, and `existsTransUniv`'s output MATCHES
the capstone's `B/A/Binf/Ainf/hB/hA/hid/hVopen/hBcont/hAcont` verbatim. The book's "per (β,α)
pair" collapses to single-index because the caller (B1) picks `x γ, y γ` (which center, which
partner) — the join stays parametric over `x,y`, exactly as `existsTransUniv` already defers
them. **No pair-index existsTransUniv call is needed.** (The one residual book question — which
concrete points `x γ,y γ` realize `F^α_{kℓ}` decoded in the `center γ` chart — is a *caller*
choice, not a blocker for the parametric join.)

**Join build plan (StepCProducers.lean, next session — large, ~200+ lines):**
1. `X' := X.subseq L.φ` (reindexed seq); call `existsTransUniv (I:=I) (X:=X') input x y U V …`.
   Obtain `phi, Jinf, Jbarinf, hspec`. Set `L' := L.subseq hphi`.
2. Choose `coordK γ := normalChartAt(center γ) '' hatSourceCage … γ`; then `hKU/hKV/hmap` and
   `existsTransUniv`'s `hUx/hVy/hmapsJ/hmapsJbar` come from the cage↔chart-image + C²-ball
   geometry. **These are the remaining non-trivial bridges** (each likely its own lemma):
   - cage image ⊆ C²-ball: `normalChartAt(center γ) '' hatSourceCage ⊆ ball 0 (expMapC2Radius …)`
     — from `Item3GpScaleInput`/`Item3RadiusInput` pinning the radii (now unblocked).
   - `NormalOverlapOn` (`hovlJ/hovlJbar`) and the cocycle `normalTransition∘normalTransition=id`
     (`hLeft/hRight`) for the chosen `x γ,y γ` — from the Step-B normal-overlap API
     (`StepBTransition`), threaded as hypotheses if no producer.
3. `hR` from `Item3GpScaleInput.subseq`; `hstrict` = `StrictDistInput` (threaded);
   `hcenter` from the live-center facts; `hrad/hactive_mem` = averaging radius facts (threaded
   or from `hatSourceBall` geometry); `rho/hrho/join/radSeq` threaded.
4. Feed to `unifHatCageSelfComp` (or via `hatChartPtsOfComp` + `hatPOU_active_data` →
   `centerAverage.unifTwoIdDataOn`). Endpoint: averaged map → id on `hatSourceBall`.
   Keep in view the B1 obligations `F(O_k)=O_ℓ` + `|∇^p F|≤C̃` (ruling §"B1 layer").

Remaining risk: the overlap/cocycle/cage bridges (step 2) are real geometry; if the Step-B
`NormalOverlapOn`/cocycle facts have no producer for the book's `x γ,y γ`, thread them as
honest hypotheses of the join (matching `existsTransUniv`'s own parametric style) — do NOT
invent them.

---

**Status: NOT YET CREATED (superseded above). Original audit below (design wall now resolved).**
Goal was to instantiate `NetLimitData.unifHatCageSelfComp`
(`StepCAveragePOU.lean:3056`) with concrete Step-A/Step-B data. No `.lean` was
written (a half-instantiation would need `sorry`s / new fake assumptions, which
the honest-input discipline forbids).

## What `unifHatCageSelfComp` demands (25 inputs), and where each stands

Fixed data: `hd : InjRadiusDecayInput`, `P`, `L : NetLimitData`, `pb`, `r`, `n`,
`rho`+`hrho` (POU on `closedBall basepoint r`, subordinate to `hatBall`).
Per-hat `γ : Fin (pb.A r)`, all coords via `normalChartAt (X.obj (L.φ n)).metric (center γ)`.

- **`B,A,Binf,Ainf,hB,hA,hid,hVopen,hBcont,hAcont` (transition maps + C∞-conv +
  two-sided id)** — **PRODUCER EXISTS**: `StepCTransitionRefine.existsTransUniv`
  (`ι` finite, `[Finite ι]`). Its output, after a subsequence `phi`, is exactly
  `Binf=Jinf γ`, `B γ = fun k => normalTransition (X.obj (phi k)) (x γ (phi k)) (y γ (phi k))`,
  `A γ = fun k => normalTransition … (y…) (x…)`, `MapCInfConvOnCompacts (U γ) (B γ) (Binf γ)`,
  ditto `A`, and `Jbarinf γ (Jinf γ z) = z`. Shapes MATCH `unifHatCageSelfComp`.
  BUT it requires its OWN inputs (per hat, per k): `hovlJ/hovlJbar` (`NormalOverlapOn`),
  `hUx/hVy` (`U γ ⊆ ball 0 (expMapC2Radius (metric) (x γ k))`), `hmapsJ/hmapsJbar`
  (`expMapDiffeo` maps-to on the C²-ball), `hLeft/hRight` (cocycle
  `normalTransition∘normalTransition = id`). These come from Step-A cover + Step-B
  geometry and are NOT yet produced.
- **`hcenter` (`seqCenter hd D P (L.φ n) γ = some (center γ)`)** — needs the live-center
  producer from the good-cover (`seqCenter` def in `GoodCoveringSeq.lean:36`; live-center
  facts should come from the net data / `exists_stableNetData`). Threadable, not built.
- **`hstrict` (`StrictDistInput …`)** — honest input (lbl413, `StepCInputs.lean`); thread.
- **`hR` (`4 * L.lamInf γ < expRadiusGp (X.obj (L.φ n)).metric (center γ)`)** — **GAP,
  needs a scale decision.** `expRadiusGp g p = √(gpCoerciveConst g p) * expMapC2Radius g p`
  (`GaussLemmaPullback.lean:425`). `Item3RadiusInput` (`GoodCoveringItem3.lean:82`) only
  gives `ρ k α ≤ expMapC2Radius (metric) c` and `ofReal (ρ k α) < injRadius`; it does NOT
  relate `ρ`/`4λ` to `expRadiusGp` and does NOT bound below by `4λ`. Since `√coercive` can
  be `<1`, `4λ < expMapC2Radius` does NOT give `4λ < expRadiusGp`. So `hR` needs either an
  extended honest scale input (the book's "`D` large enough", carrying the coercive
  constant / stated directly as `4λ < expRadiusGp`) or a coercivity lower bound. DESIGN
  DECISION for the planner.
- **`hmap` (`A γ b (B γ a v) ∈ normalChartAt(center γ) '' hatSourceCage`)**,
  **`hKU/hKV` (`normalChartAt(center γ) '' hatSourceCage ⊆ U γ`, `Binf γ v ∈ V γ`)**,
  **`hactive_mem` (`dist x (decodedCompPts … a b x γ) < radSeq a b x`)**,
  **`hrad` (`0 < radSeq a b x`)** — **GAPS**: cage↔chart-image geometry + composed-map
  preservation + active-radius facts. No producers; entangled with `radSeq`/`join` choice.

## The wall (why I stopped rather than write a `sorry`-laden file)

1. **Which maps?** The book's local maps (B1_JOIN_HANDOFF) are the *cross-sequence*
   `F_{kℓ}^α = H̄_ℓ^α ∘ (H̄_k^α)⁻¹` (M_k → M_ℓ). `existsTransUniv` provides *same-manifold*
   overlap transitions `normalChart_{y} ∘ exp_{x}` on one `X.obj k` (two cover points
   `x,y` on the same manifold), converging as `k→∞`. `unifHatCageSelfComp`'s `B γ a : E→E`
   is abstract so either could type-check, but WHETHER the same-manifold overlap maps are
   the geometrically-correct choice for the averaged self-map of `M_{φ n}` needs
   `chapter4.tex` around `lbl397`/`lbl399` (not loaded). If cross-sequence maps are
   required, no producer exists for them.
2. **Subsequence coordination.** `existsTransUniv` returns its own `phi`; `L` has `L.φ`.
   The join must run the transition extraction on `L`'s subsequence (or refine `L` along
   `phi` via `L.subseq` + the `*_subseq` projections `hatSourceCage_subseq`,
   `hatBall_subseq`). This threading is real and unspecified.
3. **`center γ : (X.obj (L.φ n)).M` vs `existsTransUniv`'s cover points on `X.obj (phi k)`**
   — the identification of the hat center with the cover points along the sequence is the
   crux of the wiring and is book-dependent.

## Smallest next lemmas (in dependency order)

1. **`hR` scale**: decide the honest form. Likely extend `Item3RadiusInput` (or add a
   sibling in `GoodCoveringItem3.lean`) to assert `4 * λ_α < expRadiusGp (metric) c` at
   live centers (book "D large enough"), OR add `gpCoerciveConst` lower bound. Planner call.
2. Resolve the map choice (§Wall 1) from `chapter4.tex` — same-manifold overlap vs
   cross-sequence. Then either reuse `existsTransUniv` or build the cross-sequence producer.
3. Cage↔chart-image bridge: `normalChartAt(center γ) '' hatSourceCage ⊆ ball 0 (expMapC2Radius …)`
   and the composed-map preservation `hmap` — needed for both `hKU/hKV` and `existsTransUniv`'s
   `hUx/hmapsJ`.
4. Only then: the `StepCProducers.lean` join calling `existsTransUniv` → `unifHatCageSelfComp`.

## PLANNER RULING (2026-07-01, from `chapter4.tex` L1515–1707) — all three walls resolved

**Wall 1 — same-manifold transitions ARE correct; no cross-sequence producer is needed.**
The cross-sequence `F_{kℓ}^α = H̄_ℓ^α ∘ (H̄_k^α)⁻¹` appears in the book ONLY at the manifold
level; everything the averaging machinery consumes is expressed in `β`-coordinates, where
(eq `lbl398`, L1541–1547):
```
F_{kℓ,β}^α = J̄_ℓ^{αβ} ∘ J_k^{βα}   : E^β → vec E^β
```
— a two-parameter composition of the SAME-MANIFOLD `M_k` transition `J_k^{βα}` with the
SAME-MANIFOLD `M_ℓ` transition `J̄_ℓ^{αβ}`. Its `→ id` (lbl399, L1552–1559) is exactly
`comp_cInf_id_on`'s shape (`B` at index `k`, `A` at index `ℓ`, limit cocycle
`J̄_∞^{αβ} ∘ J_∞^{βα} = id_β` from the lbl394 transition limits). The POU weights in
`β`-coordinates are likewise functions of same-manifold `J_k^{βγ}` only (L1636–1648), and the
cm gradient equation localizes in the `β`-chart (L1699–1703). So **reuse `existsTransUniv`
as-is** — the abstract `B γ a`/`A γ b : E → E` instantiated with same-manifold transitions at
two different sequence indices IS the book's `F_{kℓ,β}^α`.

**Wall 3 — center identification.** In `normalTransition Y x y = normalChart_y ∘ exp_x` terms:
```
J_k^{βα}  = normalTransition (X.obj k) (c_β k) (c_α k)     (decode-hat center → active-hat center)
J̄_ℓ^{αβ} = normalTransition (X.obj ℓ) (c_α ℓ) (c_β ℓ)     (the SAME pair, reversed)
```
where `c_β k, c_α k` are the LIVE `seqCenter` values of the two hats at index `k`. So ONE
`existsTransUniv` call per (decode-hat `β` =: the capstone's `γ`, active hat `α`) with
`x γ' k := c_β k`, `y γ' k := c_α k` yields both families (its `B` with `(x,y)`, its `A` with
`(y,x)` — matching the audited output shape). The capstone's `center γ` (decoding chart at
index `L.φ n`) is that hat's OWN live center `c_γ (L.φ n)` — supplied by the `seqCenter`
live-center facts (`hcenter`), not a new notion. Active summands `α` range over the hats
meeting the decode hat; `decodedCompPts` should decode the composed maps in the `γ`-chart
exactly as eq L1699–1703 does.

**Wall 2 — subsequence coordination: reindex-first.** Instantiate the transition producer at
the ALREADY-REINDEXED sequence `X ∘ L.φ` (producers are stated for an arbitrary
`PointedRiemannianSeq`), then refine `L` along the producer's returned `phi` via `L.subseq` +
the `*_subseq` projections (`hatSourceCage_subseq`, `hatBall_subseq`). Do not compose two
after-the-fact subsequences.

**`hR` — APPROVED as a new honest scale input** (sibling, NOT an edit of `Item3RadiusInput`):
`Item3GpScaleInput` in `GoodCoveringItem3.lean`, asserting at live centers the `g_p`-scale
separation in (essentially) the consumed shape — `4 * λ` below `expRadiusGp (metric) c` per
`k`/hat, stated so that the capstone's `hR` (`4 * L.lamInf γ < expRadiusGp … (center γ)`)
follows in one line from the existing `lamInf ≤ λ`-type net facts. Docstring justification:
the book's ball-scale choice (lbl383; cited at L1672 "by the choice of balls in Lemma lbl383
we can apply Proposition lbl434") with the lbl427 scale `r < min{inj/3, π/(6√K)}`; in the
formalization `expMapC2Radius` is an opaque choice radius, so this comparison is un-provable
without the uniform-radius anchoring — the SAME policy and native-discharge frontier as
`Item3RadiusInput` (record it in `CHAPTER4_PLAN.md`'s honest-input boundary when added).
Do NOT take a `gpCoerciveConst` lower bound instead (messier, non-book shape).

**Also noted from the book for the B1 layer (not this brick):** `F_{kℓ;r}(O_k) = O_ℓ`
(basepoint preservation via the `χ_k` cutoff, L1676–1678) and `|∇^p F_{kℓ;r}| ≤ C̃_{p+1}`
uniform in `k` (L1674–1676) are stated obligations of lbl400/lbl434 — keep them in view when
stating the join endpoint so B1 can consume it.

## Reusable facts confirmed present
`StepCTransitionRefine.{existsTransRefine,existsTransFinite,existsTransUniv}`;
`StepBApproxIso.comp_cInf_id_on`/`comp_tendsto_id_on` (lbl399, feeds `hatChartPtsOfComp`);
`NetLimitData.{unifHatCageSelfComp,hatChartPtsOfComp,hatSourceCage,hatSourceBall,
hatSourceCage_subseq,hatCageCompact,hatCageSub,hatCageSrcOfRad,sourceComplete}`;
`centerAverage.{unifTwoIdDataSelf,inputOfFillSelf,activeFill}`; `decodedCompPts`;
`StepCInputs.StrictDistInput` (honest); `Item3RadiusInput`, `seqCenter`, `NetLimitData.lamInf`.

## RULING #2 TAIL — σ/overlap quantitative discharge (2026-07-04)

Deliverable (2) of the last-mile session. Two lemmas added to `StepCProducers.lean`:

- **`hUx_of_sigma` (GREEN, sorry-free) — the σ-discharge of `stepCJoin`'s `hUx`/`hVy`.** Given a
  per-hat radius family `σ : Fin (pb.A r) → ℝ` with `σ γ ≤ expMapC2Radius (X.obj (L.φ k)).metric (x γ k)`
  for every subsequence index `k` (`hσ` — the `Item3RadiusInput`-shaped `g_p`-scale field, a
  `k`-independent `σ γ`), the domain `U γ := Metric.ball 0 (σ γ)` is `⊆ ball 0 (expMapC2Radius (x γ k))`
  by `Metric.ball_subset_ball`. Instantiate with `x`/`y` for `hUx`/`hVy`. This is the "σ from the
  λ-window" discharge: the domain-radius hypotheses of the join collapse to the single scale field, no
  per-`k` threading. (The scale field `hσ` itself is the honest `Item3RadiusInput`/`lbl383` field.)

## RULING #4 — `hatCageImg'` CLOSED, StepCProducers is 0-sorry (2026-07-04)

The open/closed-ball gap is dissolved by restating with the *strict scale hypothesis* (no boundary
analysis). `StepCProducers.lean` now has **ZERO `sorry` tokens** (verified by grep). Three green decls:

- **`properBallImgOfRad'` (GREEN)** — coercive-tightened `properBallImgOfRad`:
  `normalChartAt c '' closedBall c R ⊆ ball 0 σ` for any `σ` with `R / √(gpCoerciveConst c) < σ`
  (strict) and `R < expRadiusGp c`. Proof: `metricBall_subset_normalBall` gives `v = normalChartAt c q`
  with `√(g_c(v,v)) = dist c q ≤ R`; coercivity `gpCoerciveConst_le` gives
  `√coercive·‖v‖ = √(coercive·‖v‖²) ≤ √(g_c(v,v)) ≤ R` (via `Real.sqrt_mul`+`Real.sqrt_sq`), so
  `‖v‖ ≤ R/√coercive < σ` by `le_div_iff₀` + `lt_of_le_of_lt hbound hσ`. **The strict `<` in the
  hypothesis is what kills the closed-ball boundary — the closed cage radius `dist ≤ R` still yields
  `‖v‖ < σ`.**
- **`hatCageImg'` (GREEN, was 1 sorry)** — target `ball 0 (sigma γ)` under `hσ : 4 λ^γ/√coercive < σ γ`
  (+ the chart-domain `hR : 4 λ^γ < expRadiusGp`); proof = `hatCageInClosed` + `properBallImgOfRad'`.
- **`SigmaScaleField` (def) + `.expRadiusGp` (GREEN)** — the sibling `lbl383` scale field folding both
  bounds: `∀ γ k, 4 λ^γ/√(gpCoerciveConst (x γ k)) < σ γ ∧ σ γ ≤ expMapC2Radius (x γ k)`. Its `.1`
  feeds `hatCageImg'`'s `hσ`, `.2` feeds `hUx_of_sigma`, and `.expRadiusGp`
  (`4 λ^γ/√c < σ ≤ expMapC2Radius ⟹ 4 λ^γ < √c·expMapC2Radius = expRadiusGp`, via `div_lt_iff₀` +
  `expRadiusGp` defeq) feeds `hatCageImg'`'s `hR` — so both cage-image and domain hypotheses of
  `stepCJoin` come from this ONE honest field.

- **Overlap/cocycle audit (`hovlJ`/`hovlJbar`/`hLeft`/`hRight`).** These are `NormalOverlapOn` +
  `normalTransition` round-trip hypotheses of `stepCJoin`, produced per-`(γ,k)` from the Step-B
  transition machinery (`StepCTransitionRefine`/`StepBTransition`, `normalTransition` /
  `NormalOverlapOn`); they thread through `existsTransUniv`'s parametric inputs (the join is already
  parametric over them). No new producer needed — they are supplied at the capstone call site from the
  Step-B `normalTransition` cocycle, the same as `hmapsJ`/`hmapsJbar`.

## 2026-07-13 packing-local Item 3 input

`stepCJoinFixed`, `stepCJoinDataFixed`, and `stepCJoin` now require only
`Item3GpScaleAt ... pb r n`, exactly the finite fixed-index fact used to feed
the capstone's `hR`. The legacy all-index `Item3GpScaleInput` is no longer a
consumer boundary in this file. Focused verification and the narrow refresh
passed.

This closes the join-side `g_p` quantifier mismatch, not the independent
`SigmaScaleField`, full item-3 convexity/physical-cage, or Hessian/Neumann
producers. The finite exp-diffeomorphism radius tail is now checked separately.
The concrete `StepB1RawInput` producer and textbook B1 theorem remain 0%;
dedicated Step-B/B1 machinery is about 80%, Chapter 4 machinery about 76%,
whole-HCG machinery about 53%, and compactness endpoints remain 0%.

## 2026-07-13 canonical sigma tail and refinement

Added `SigmaScaleAt` and `SigmaScaleTail` to distinguish a sigma inequality at
one subsequence index from the eventual finite-family statement actually
produced by the radius profile.  `SigmaScaleField.at` and `.to_tail` project an
all-index field, `SigmaScaleTail.subseq` preserves an eventual tail under a
strict refinement, and `SigmaScaleTail.exists_field` shifts once past the tail
to recover the all-index field required by the existing Step-C consumer.

For the canonical totalized centres, `NormalRadiusProfile.sigmaCenterTail`
chooses `sigma gamma = 8 * L.lamInf gamma`.  Under the one-shot
`16 < ratio * D` budget it proves both the coercive lower inequality and the
upper `expMapC2Radius` inequality eventually, using
`seqCenterD_dist_eq` to read the controlled radius.  Separately,
`sigmaCenter_le` derives the uniform comparison-radius bound from
`8 * lambda D 0 < r1`.

`MetricCompactnessInputs.sigmaCenterData` packages that canonical tail with
the `r1` bound, while `MetricCompactnessInputs.exists_sigmaField` performs the
single tail shift and returns the `SigmaScaleField` used downstream.  These
declarations passed focused verification.

This closes the sigma producer for the canonical `x` family only.  No analogous
profile connection has yet been proved for an arbitrary partner `y` family,
so that is still a real producer-side wiring obligation.  `StrictDistInput`
and its Hessian/Neumann strict-convexity producer remain an independent
frontier.  The sigma/refinement API itself is complete (100%), but
`StepB1RawInput`, textbook B1, and all compactness endpoints remain 0%; the
whole-HCG machinery estimate is not raised above about 53% by these helpers.

## 2026-07-13 eventual H6 join and support-local blocker

`stepCJoin` now combines its sixteen per-slot geometric conditions into
`NormalTransAt` and calls `existsTransTail`.  Thus a single finite common shift,
not an all-index strengthening, feeds the H6 transition diagonal.  Focused
verification passed.

The remaining `hKV0` obligation in `stepCJoinFixed`, `stepCJoinDataFixed`, and
`stepCJoin` is intentionally still visible.  Pair H6 gives a large item-3
target anchor and only conditional inverse-limit cancellation; it does not map
the entire canonical cage into the reverse eight-lambda convergence domain.
The checked active-support theorem in `StepCPairTail` gives the needed six-
lambda containment only when the atom/weight is nonzero.  Closing the capstone
therefore requires a support-local specialization of the averaging/composition
consumer, or a genuinely stronger later-reference cage.  Treat this as an
architecture consultation frontier, not a missing rewrite lemma.

## 2026-07-13 support-local H6 transition join

The support-local choice has now been implemented and focused-verified.
`binfMemClosed` consumes eventual rather than all-index membership;
`HasAtomWeightLim.binf_of_weight` turns a nonzero limit weight into an
interacting target whose forward limit lies in the closed six-lambda ball.
`exists_supp_trans` extracts all interacting targets for one fixed live source.

`exists_supp_fin` performs the outer transition extraction once on the finite
dependent type `Sigma alpha, InterSlot alpha`. It returns one common strict
subsequence, curried forward/reverse limits and cocycles for every live source,
and the same support-to-six-lambda readout. It deliberately retains the
pre-refinement `InterSlot` indices; further refinement preserves atom packages
but need not make the refined interaction subtype surjective. Both focused
checks passed.

The remaining blocker is no longer an H6 derivative or pair-extraction gap.
The fixed-manifold capstone must assemble source-local chart pullbacks into the
global source ball, totalize noninteracting targets only behind zero weights,
and make `exists_hat_cm_tail` support-local (it still requests point convergence
on the whole `hatBall`). This is a real outer API/quantifier design question,
not a local Lean error. Sparse active-support machinery is about 92% and
pair-to-capstone integration about 78%; whole-HCG machinery remains about 53%,
while `StepB1RawInput`, textbook B1, and all compactness endpoints remain 0%.

## 2026-07-13 point-level interaction totalization

Added `interSlot?` on the original stabilized `InterSlot L pb r alpha` and
`totalPts`, which totalizes only a pair-indexed point family to the ambient
finite target slots.  A missing interaction is filled by the source point; no
equivalence with an interaction subtype after subsequence refinement is used.

The two `activeFill` readouts are now checked.  Zero limit weight returns the
source point without inspecting the lookup.  At nonzero weight, the caller
passes the exact target-existence implication produced by `exists_supp_fin`;
the lookup's chosen target is identified using injectivity of the underlying
finite slot projection.  The point family remains an explicit parameter because
the live tree has no canonical `pairDecodedPts` yet; that family belongs to the
later fixed-manifold source-patch producer, not to interaction lookup.

Focused verification passed.  These lookup/totalization primitives are complete
(100%), but the fused `exists_supp_pts_fin` producer is not yet stated (0%) and
the source-patch cover plus pair-decoded point family remain the next producer
work.  Sparse active-support machinery is now about 94%, pair-to-capstone
integration about 80%, and whole-HCG machinery remains about 53%; `StepB1RawInput`,
the textbook B1 theorem, and all compactness endpoint theorems remain 0%.

## 2026-07-13 per-slot closed-ball readout

Extracted and focused-verified `HasAtomWeightLim.binf_of_slot`.  Its input is one
original stabilized `InterSlot`, the corresponding H6 limit-map convergence,
and a nonzero normalized limit weight at that slot.  Its conclusion is exactly
that the slot's limit image lies in the closed six-lambda ball.  It neither
selects a target nor asks for source-wide interaction data, so the future fused
atom/support producer can reuse it after its dependent-pair extraction.

The existing `binf_of_weight` API is unchanged and now performs only the honest
weight-to-interacting-slot selection before calling the per-slot lemma.  This
removes duplicated radius/weight-tail reasoning without adding assumptions or
changing the old `InterSlot L` index.  The per-slot readout is complete (100%);
the fused `exists_atom_supp_fin` producer is still unstated (0%).  Sparse
active-support machinery remains about 94%, pair-to-capstone integration about
80%, and whole-HCG machinery about 53%; `StepB1RawInput`, textbook B1, and all
compactness endpoint theorems remain 0%.

## 2026-07-13 fused source-patch and sparse-point producer

`MetricCompactnessInputs.exists_atom_supp_fin` and
`MetricCompactnessInputs.exists_supp_pts_fin` are now checked and sorry-free.
The first extracts one master subsequence, the finite live-source cover,
source-local H6 atom/weight limits, old-`InterSlot` transition limits, and the
nonzero-weight closed-six-lambda readout.  The second pulls each limit-weight
family back only through its own frozen normal chart and constructs the
two-index decoded point family.

The frozen source index is correctly eventual.  On that same tail the proof
combines the item-3 `expRadiusGp` scale with all live-center equations, uses the
canonical source cage for the prescribed source slot, closes only the actual
nonzero support inside the target six-lambda ball, and applies the generic
composition convergence theorem.  It calls the dependent pair extractor once,
keeps the original `InterSlot L ... alpha`, and totalizes only the final
point-valued family at the ambient `Fin` boundary.  No chartwise weights are
glued, no overlap equality or chart selector is asserted, and no whole-cage
target containment or new radius assumption is used.

Focused verification passed with no local warning.  Both fused producer
theorems are complete (100%), and the source-cover/sparse-point architecture is
complete (100%).  The final support-local center/branch outer theorem is not yet
stated (0%); its dedicated pair-to-capstone machinery is about 90%.  Whole-HCG
machinery remains about 53%, while `StepB1RawInput`, the textbook B1 theorem,
and all compactness endpoint theorems remain 0%.

## 2026-07-13 source-patch hat containment

`MetricCompactnessInputs.exists_supp_pts_fin` now exports, on its existing
frozen-index tail, the explicit containment of every source patch in the hat
ball belonging to its prescribed source slot.  The proof reuses the producer's
existing exp-image sandwich and the normal-chart left inverse; it adds no input
and makes no assertion about another source chart or target slot.

Focused verification passed.  The fused producer and its source-local
cover/weight/point package remain complete (100%).  The sibling
`StepCSupportCapstone.exists_supp_cm_fin` and its global-ball corollary are now
checked, so the approved conditional pair-to-capstone architecture is 100%.
Whole-HCG machinery is about 54%, while `StepB1RawInput`, the textbook B1
theorem, and all compactness endpoint theorems remain 0%.

## 2026-07-14 retained support convergence data

`HasSuppConvData` now names the coherent data already extracted by
`exists_atom_supp_fin`: source-domain openness and the eight-lambda bound,
all-stage source-cover geometry, each source-local `HasAtomWeightLim`, and the
two-sided `Jinf`/`Jbarinf` transition limits.  `exists_supp_pts_fin` retains
this predicate on the same master subsequence while continuing to consume the
nonzero-support readout to build its existing point tail.  No chartwise weights
are glued and no compatibility or radius hypothesis was added.

Focused verification and the exact producer-module refresh passed.  This
closes the data-erasure seam needed by the next compact-patch/global-map stage;
it does not construct `StepB1RawInput`.  The concrete raw producer and textbook
B1 theorem remain theorem-level **0%**, as do all compactness endpoints.

## 2026-07-14 compact source cores

`HasCompactCover` and the strengthened eventual payload of
`exists_supp_pts_fin` now produce one compact core inside every frozen
source-local patch, with the cores still covering the whole closed source
ball.  The proof applies the existing finite compact-cover theorem to the open
sets `chi.source ∩ chi ⁻¹' U`; it does not incorrectly claim that the
source-ball intersections themselves are open.

Focused verification and the exact producer refresh passed.  The compact cores
are sufficient domains for the retained `MapCInfConvOnCompacts` data at fixed
source stage.  They do not solve the uniform-in-stage/all-pairs tail, define the
single global comparison map, or produce the two-sided covariant metric bounds.
Those remain the next architecture/analytic frontier; theorem-level endpoint
percentages are unchanged.

## 2026-07-15 nested-core retention

`exists_atom_supp_fin`, `HasSuppConvData`, and `exists_supp_pts_fin` now retain
the fixed compact cores `C0` and `C1` produced by `exists_live_cores`, including
compactness, `C0 alpha ⊆ interior (C1 alpha)`, `C1 alpha ⊆ U alpha`, and the
all-stage source-ball cover by strict-inner-core exponential images.  The old
open-domain geometry is recovered from these containments rather than by a
second cover extraction.

Focused verification and the exact producer refresh passed.  The retained
origin-metric witness used to define these quadratic cores is not a full local
metric convergence theorem.  The support-sensitive target family and the
common-domain moving-stage implicit solver remain genuine analytic/API
frontiers.  The all-pairs chart tail, `StepB1RawInput`, textbook B1, and every
compactness endpoint remain 0%; running machinery estimates stay about
94% / 86% / 57% for Step-B/B1 / Chapter 4 / whole HCG.
