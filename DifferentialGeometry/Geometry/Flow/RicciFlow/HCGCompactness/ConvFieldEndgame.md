# ConvFieldEndgame.lean — concrete P4 upgrade-data producer

The live canonical output is concrete `FlowUpgradeData`, produced by
`flowUpgrade_of_maps` / `flowUpgrade_of_mc` and consumed by the conditional
Theorem 3.10 wrappers.  The older conclusion-valued theorems remain
compatibility consumers.  The tracked mathematical inputs (Thm 3.9's `mc`,
moving-Shi `hShiT`, `hsmooth`, and the comparison data) remain explicit.

## 2026-07-09: endgame now exports concrete upgrade producers

`flowUpgrade_of_maps` and `flowUpgrade_of_mc` now produce
`FlowUpgradeData X mc`, exposing the selected subsequence and the actual
`FlowLimitData`. The established public theorems `flowLimit_of_maps` and
`flowLimit_of_mc` are retained as compatibility consumers and are one-line
applications of `.toConclusion`. Thus the canonical theorem path can consume
the endgame's concrete construction without an exact-conclusion backend; that
former compatibility API has been removed.

The pointed-limit contract is now retained in the produced data:
`FlowLimitData.hL0 : L.atTime 0 = mc.limit`. Previously
`flowUpgrade_of_maps` required `hPlim : P = mc.limit`, but its result forgot
that fact; deleting `hPlim` would have allowed an alleged upgrade over `mc` to
carry an unrelated pointed limit. The producer now records
`hPL.trans hPlim`, so both equalities have durable mathematical content. A
repository-wide call audit found only the two same-file consumers; both already
supply the required pointed-limit equality and need no signature change.

Focused verification and the targeted module refresh passed. The
producer/consumer split itself is 100%.
Conditional endgame assembly from its tracked mathematical inputs is 100%
checked; the remaining `hsol`/PDE producer frontier and unconditional Theorem
3.10 remain separate, with the latter still 0%. The project-wide endpoint is
still 0%; this structural refactor does not change the project map's roughly
59% Chapter 4 machinery estimate or the roughly 45% whole-HCG machinery estimate.

## 2026-07-08: `hsol` DECOMPOSITION — the `hpde` chain hits a REAL frontier (NOT mechanical)

**Finding (verified by reading the producers): the P4 close-out's `hpde` is NOT
"verbatim-pluggable".**  `isSolutionOn_of_reg`'s `hpde` field wants, at each
`t ∈ D.regular` and each `x`, `HasDerivAt (fun s => (gInf s).inner x v w)
(-2·ricciTensor (gInf t) x v w) t`.  The only producer is `metricLimit_pde(On)`
(`LimitSolutionEquation.lean:213/273`) — but it requires a SEQUENCE OF GENUINE
`SolutionOn`s `S : (k) → SolutionOn (M := mc.limit.M)` whose metrics converge to
`gInf` (its `hkder` calls `metric_derivWithin_eq_neg_two_ricci (S k) (hS k)` — the
per-`k` flow equation).  **The endgame's converging sequence `gSeqExt (co.φ k)` is
bump-extended and is NOT a Ricci flow on `mc.limit.M`** (off `grow` the bump kills
the flow property); the genuine flows (`isSolutionOn_sourceFlow`) live on the
per-`k` `SourceDomain`s, not on a fixed `mc.limit.M`.  `metricLimit_pde/pdeOn`
currently have ZERO consumers — the bridge was never built.

**GOOD news:** `ricciConv_of_dnConv` (`RicciFromJets.lean:1698`) takes a PLAIN
metric sequence `gSeq` (NOT `SolutionOn`s) + `hlowSeq/hlowInf/hbddSeq/hbddInf`
(λ-lower & order-≤2 covariant bounds at `x` for BOTH sides) + `hconv` (`convPt`
orders ≤2 at `z = x`) → Ricci convergence.  So `hRicConv` and `hinner` (order-0,
via `metricInner_tendsto`) ARE producible from `(endgameCo …).convPt` + endgame-level
bounds (with the standard "limit inherits the bounds" step, ε→0 on `derivNorm_le_cov_add`).

**The genuine remaining frontier = the `gSeqExt` local PDE + a shift variant:**
1. **`gSeqExt` local PDE** (NEW lemma, ~focused session): for `x ∈ grow (co.φ k)`,
   `HasDerivWithinAt (fun s => (gSeqExt … (co.φ k) s).inner x v w)
   (-2·ricciTensor (gSeqExt … (co.φ k) t) x v w) (Icc β ψ) t`.  Route (banked pieces,
   but the COMPOSITION is new): on `grow` (bump ≡ 1) `gSeqExt = srcMetric`-pullback
   (`gSeqExt_inner_of_mem`), whose `s`-derivative is `-2·Ric` by
   `isSolutionOn_sourceFlow`'s equation (`metric_derivWithin_eq_neg_two_ricci`) —
   transported to `x ∈ mc.limit.M` through the source-target diffeo + `restrictOpen`,
   with `Ric(gSeqExt) x = Ric(srcMetric-pullback) x` by the Brick-1 curvature
   naturality (`ricciTensor_restrictOpen`/pullback).  This is a real HasDerivWithinAt
   -through-pullback + curvature-equality construction.
2. **shift variant of `metricLimit_pde`** (small): `hasDerivWithinAt_lim`
   (`:74`) needs `∀ k` derivatives, but `gSeqExt`'s per-`x` PDE holds only for
   `k ≥ k0(x)` (from `bf.grow_cover {x}`).  Fix with the sequence-shift trick
   (`f̃ k := f (k+k0)`) or a `hasDerivWithinAt_lim`-eventual restatement, then a
   `metricLimit_pde'` that takes `hkder` DIRECTLY (dropping the `S : SolutionOn`
   packaging — its body is exactly the `refine hasDerivWithinAt_lim …` half).
3. **the `HasDerivWithinAt → HasDerivAt` upgrade** (small, as the plan noted):
   `D.regular` open, `regular ⊆ carrier ⊆ Icc β ψ`, so `Icc β ψ ∈ 𝓝 t` and
   `HasDerivWithinAt.hasDerivAt` applies.

**PART A.3 (continuity fields):** `metricTensorContLim` (`FlowLimitRegularity.lean:208`)
gives the METRIC's joint continuity only — there is NO landed `ricci`/`rm04`/`scalar`
continuity-of-`gInf` producer (the file has only `chartGram*`/`metricTensorContLim`).
So `hscalarCont`/`hscalarTime`/`hricciCont`/`hrm04Cont` are all currently CARRIED.
**PART B (`scalar`):** analogous — `scalarConv_of_dnConv` gives scalar convergence of
the plain sequence, but the pullback-composition (target scalar at `Φ.map k x` =
source-flow scalar = `gSeqExt` scalar via bump-1 locality) is the same kind of
banked-but-uncomposed bridge as A.1.  **PART C** is ready the moment `hsol` decomposes.

**DECISION (2026-07-08):** did NOT force `hpde`; landing it needs the A.1 local-PDE
bridge (a genuine construction), not a producer call.  `flowLimit_endgame`
(hsol/scalar tracked) stands verified; A.1 + A.2 is the next focused brick.

## Historical execution record (superseded as current instructions)

> Everything below this notice is retained for proof provenance.  The old
> `STATUS`, `THE FRONTIER`, `READY-TO-EXECUTE`, and mechanical execution-map
> headings are superseded; do not resume from them.  The live route is the
> concrete `FlowUpgradeData` producer described above.

### 2026-07-07b: compatibility consumer `flowLimit_endgame` wired + proved

`flowLimit_endgame` (ConvFieldEndgame.lean:508) upgrades `flowLimit_of_mc` to the
ruling-5a book-facing form: its hypotheses are ONLY `mc`, the book-cited
sequence-flow inputs, and the tracked regularity/scalar inputs `hsol`/`scalar`.
Targeted build green 3923 jobs; `#print axioms flowLimit_endgame = [propext,
Classical.choice, Quot.sound]` sorry-free.  Also axiom-clean: `endgameCo`,
`endgameCo_zero`, and `pointedCGHMaps_of_manifold` (FlowLimitUpgrade.lean:65).

**The four intermediate inputs are now BUILT (not assumed):**
- `Φ₀` — `pointedCGHMaps_of_manifold X mc.limit mc.subseq mc.maps` (the missing
  generic-`P` field-copy of `pointedCGHMaps_of_atZero`, added this pass).
- `co` — **`endgameCo`** (ConvFieldEndgame.lean:283): executes all four Brick-7a
  producers into `convOut` with `cLow := (Crel·Bmax)⁻¹` and
  `hcLow := inv_pos.2 (mul_pos (one_pos.trans_le hCrel1) (one_pos.trans_le hBmax1))`.
  Producer arg orders (verbatim): `hbound_of_equiv R hsrc htgt β ψ gRefT B Crel
  Bmax hBmax hCrel1 hequivT hrel`; `covTail_of_bounds …hequivT hrel hcovSrc hchi`;
  `lipTail_of_src R bf hsrc htgt β ψ hlipG`; `lipSrc_of_soln R hsrc htgt β ψ hβψ
  hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT`.  Since it is a
  `def`, `(endgameCo …).gInf` is the term `hsol`/`scalar` are stated against.
- `hzero` — **`endgameCo_zero`** (:385): `gInf_zero_eq Φ₀ R bf hsrc htgt β ψ
  (endgameCo …) h0 mc.limit.metric (conv0_of_cp Φ₀ R hsrc htgt mc.limit.metric hcp)`.

**The book-cited inputs threaded** (all over `Φ₀`, granularities copied verbatim
from the 7a producers): `gRefT`, `B`/`Crel`/`Bmax` + `hBmax`/`hCrel1`/`hBmax1`,
`hequivT` (window equiv, eq-3.3), `hrel` (source comparability), `hShiT` (moving
Shi), `hcovSrc`/`hchi` (source covariant + bump-tower bounds), `hlipG` (source
Lipschitz), `hcp` (`MetricSourceCPConvOn` time-0), `hwin`/`hcarrier`/`h0`.

**What is taken WHOLE vs decomposed (honest):** `hsol : IsSolutionOn
((endgameCo …).gInf …)` is taken as ONE tracked input — NOT decomposed via
`isSolutionOn_of_reg` into `hsmooth` + `hpde` (`metricLimit_pdeOn ∘
ricciConv_of_dnConv`) + the four continuity fields.  So ALL FOUR continuity
fields (`hscalarCont`/`hscalarTime`/`hricciCont`/`hrm04Cont`) are **carried**
inside `hsol`, not individually wired.  `scalar` is likewise taken whole (its
discharger is the `scalarConv_of_dnConv` chain).  REMAINING refinement = expand
`hsol` via `isSolutionOn_of_reg` (wiring the `hpde` chain from `(endgameCo …).convPt`
+ the continuity producers `metricTensorContLim`/`RicciContinuityInMetricTime`),
leaving only `hsmooth` (ruling-5a) + genuinely-unproducible continuity carried.
`RicciFromJets.lean` mojibake repaired 2026-07-04 — the `hpde` imports can be re-added.

### 2026-07-07: compatibility consumer `flowLimit_of_mc` written + proved

`flowLimit_of_mc` (ConvFieldEndgame.lean) assembles `CompactnessConclusion X`
from `mc` (Thm 3.9) plus the honest tracked producer outputs. `lake env lean`
green; targeted-build `#print axioms` pending (queued behind a concurrent build).

**The cast/universe/subst core that made it clean — `flowLimit_of_maps`:** the
verified `flowLimit_of_co` hardcoded the maps `endgamePhi mc L hL0` (over
`L.atTime 0`), and feeding it from the AA output built over `mc.limit` needs the
`mc.limit ↔ L.atTime 0` transport — genuine cast hell (`PointedCGHMaps X P` is
indexed by the WHOLE `P`, so metric-independence of its FIELDS does NOT make the
two map-types defeq; and `subst hL0` hits the occurs-check because
`L := flowOfMetric mc.limit …` contains `mc.limit`). RESOLUTION: generalize to
**`flowLimit_of_maps`**, which takes an ABSTRACT `P : PointedRiemannianManifold`
+ `hPlim : P = mc.limit` (ties `P`'s universe to `X`'s — the tie `hL0` used to
give) + `hPL : L.atTime 0 = P` + maps `Φ` over `P`, and does `subst hPL` INSIDE
its own proof (there `P` is a variable and `L` an abstract binder → NO occurs
-check). `hLmetric` is stated as `HEq` (well-typed pre-subst, `eq_of_heq` after);
`scalar` needs `hPL.symm ▸` with an explicit type ascription (motive) + a `have`
coercion post-subst. `PointedCGHMaps.compSubseq` was generalized `L.atTime 0 → P`.
`flowLimit_of_co` is kept as the `Φ := endgamePhi` wrapper. Net: `flowLimit_of_mc`
passes `P := mc.limit`, `Φ := Φ₀` DIRECTLY — **no cast at the call site**.

**`flowLimit_of_mc`'s honest tracked inputs (each with its discharger):**
- `mc : MetricCompactnessConclusion (X.atZero)` — Theorem 3.9 (book-cited).
- `Φ₀ : PointedCGHMaps X mc.limit mc.subseq` — the limit-manifold comparison maps
  (`= pointedCGHMaps_of_manifold X mc.limit mc.subseq mc.maps`, a trivial
  field-copy; taken as input to avoid the generic-P producer's universe wiring).
- `R`/`bf`/`hsrc`/`htgt` — reference metric / bump family / σ-compactness
  (`nonempty_bumpFamily`, `isSigmaCompact_of_isOpen`).
- `co : ConvOut Φ₀ R bf hsrc htgt β ψ` — the AA output; discharger = `convOut` fed
  by the four Brick-7a producers (`ConvFieldInputs.lean`).
- `hzero : co.gInf 0 = mc.limit.metric` — discharger = `gInf_zero_eq` ∘ `conv0_of_cp`.
- `hsol : IsSolutionOn ({base := {metric := co.gInf}})` — discharger =
  `isSolutionOn_of_reg` (tracked `hsmooth` per ruling 5a + `metricLimit_pdeOn` ∘
  `ricciConv_of_dnConv` + the 4 continuity producers).
- `scalar : ScalarPullbackTendsto (hL0.symm ▸ Φ₀.compSubseq co.φ co.hφ)` (`hL0 =
  flowOfMetric_atTime …`) — discharger = `scalarConv_of_dnConv`.

**The proof** is 3 lines: `hL0 := flowOfMetric_atTime X.D mc.limit co.gInf hsol 0
hzero`; then `flowLimit_of_maps mc (flowOfMetric …) mc.limit rfl hL0 Φ₀ R bf hsrc
htgt β ψ hcarrier co (fun t _ => HEq.rfl) scalar`. `hLmetric` is `HEq.rfl`
because `L.S.family.metric = co.gInf` definitionally (`flowOfMetric_metric`).

**REMAINING = wiring the 4 tracked producer outputs** (`co`/`hzero`/`hsol`/
`scalar`) from the deeper Brick-7a cited inputs + the PDE inputs — the
"verbatim-pluggable" assembly (`ConvFieldInputs.md`/`FlowLimitBuild.md` ledgers);
each producer is itself verified. `RicciFromJets.lean` mojibake was REPAIRED
2026-07-04, so the PDE-input path's imports can be re-added. This is a large but
mechanical follow-up; the endgame theorem's SHAPE and the non-circular assembly
are now settled and checked.

## 2026-07-06: PHANTOM-L RE-PARAMETRIZATION REFACTOR **DONE** (build-light, verified)

The P-index refactor is complete and the whole cascade builds:
`build +…ConvFieldEndgame` = **"Build completed successfully (3923 jobs)"**;
`#print axioms flowLimit_of_co = [propext, Classical.choice, Quot.sound]` (NO
sorryAx — the verified assembly core survived the refactor unchanged).

**The design that shipped (two zones, not one):**
- **AA-machinery layer = re-indexed by `P : PointedRiemannianManifold`** (NOT
  `L.atTime 0`): `PointedConvergence` P-zone (the `PointedCGHMaps`/
  `SourceDomainMetricData`/producer chain + `FunctionPullbackTendsto`), plus the
  WHOLE of `SourceDomainFlow`, `ConvFieldInputs`, `ConvFieldAssembly`,
  `ConvFieldMain`. `SourceDomainMetricData.ofRestrictPullback` gained a
  `limitMetricFamily : ℝ → SmoothRiemannianMetric I P.M` param threaded through
  every producer; `ConvFieldMain.ofRP_supOn_{def,eq,conv}` gained a `gInf` param
  replacing the 4 `L.S.family.metric` refs.
- **L-output layer = stays over `L : PointedFlowData`, maps typed `L.atTime 0`**:
  `PointedConvergence` L-zone (`ScalarPullbackTendsto`/`PointedCGConverges`/
  `SmoothCGHConverges` + `.ofRestrictPullback` keeps `L.S.scalar`), plus
  `FlowLimitUpgrade` (`FlowLimitData`/`flowLimit_upgrade`) and `ConvFieldEndgame`
  (`endgamePhi`/`compSubseq`/`flowLimit_of_co`).

**WHY re-index-by-P for the AA machinery, not retype-to-`L.atTime 0`:** the first
attempt retyped every AA `Φ : PointedCGHMaps X L → X (L.atTime 0)` — that spawned
~100 `(L.atTime 0).M`-vs-`L.M` instance-synthesis failures (the letI's key on
`L.M`, `Φ.source` lands in `(L.atTime 0).M`, different discrimination-tree head,
no reduce at instances-transparency). Since `ConvFieldAssembly.srcMetric` calls
`SourceDomainFlow.sourceFlow`, the whole AA chain must share ONE binder — so all
four AA files are pure `L → P` renames (`ConvFieldAssembly` had a local
`let P : Nat→Nat→Prop` predicate that collided → renamed to `Pfit`; `ConvFieldMain`
had 8 `L.S.family.metric` → threaded `gInf`).

**The `(L.atTime 0).M` friction is REAL but confined to the L-output layer**
(where maps ARE over `L.atTime 0`): fix by declaring the guard letI's over
`(L.atTime 0).M` with value `L.topology` (defeq-accepted), and in `flowLimit_of_co`
adding a parallel `(L.atTime 0).M` instance block alongside the `L.M` one.
`L.S.family.metric` needs the FULL 6 instances (`+IsManifold(∞+1)/SigmaCompact/T2`)
to elaborate; the cross-manifold `L.M ≡ (L.atTime 0).M` defeq (needed by
`hLmetric` and the `gInf := L.S.family.metric` arg) rides on
`backward.isDefEq.respectTransparency false`. External consumer
`HamiltonPositiveRicciAdapter` needed `L.basepoint → (L.atTime 0).basepoint`
(its `basepoint_map` simp lemma now rewrites the re-indexed basepoint).

**STILL REMAINING = the endgame INSTANTIATION** (building a NON-vacuous
`CompactnessConclusion X` from `mc` alone). The refactor was the stated *only*
structural blocker; now the non-circular route is open: build `co` over
`mc.limit` (P := mc.limit) via the AA producer `convOut` first, then
`L := flowOfMetric X.D mc.limit co.gInf hsol`, then `hL0 := flowOfMetric_atTime`,
then `co`-over-`mc.limit` = `co`-over-`endgamePhi mc L hL0` by defeq (needs
`flowOfMetric`'s `atTime 0 ≡ mc.limit`), and feed `flowLimit_of_co`. Its two
honest frontiers: the `convOut` wiring (7a comparison data + moving-Shi) and
`hsol : IsSolutionOn co.gInf` (the PDE solution — its `RicciFromJets` input path
is separately blocked on that file's mojibake, owned by another session).

## Ruling A (hcovTail granularity): SKIPPED — decision + reason

Ruling A proposed weakening `hcovTail` in `hbdd_gSeqExt` (ConvFieldAssembly) from
all-of-`Φ.source k` to `grow k` granularity, to drop the `hchi` citation.

- `hbdd_gSeqExt` invokes `hcovTail` only at the tail (`k0 ≤ k`) where
  `z ∈ K' ⊆ grow (ρ k) ⊆ Φ.source (ρ k)` — so the hypothesis COULD be weakened.
- BUT the 7a producer `covTail_of_bounds` (ConvFieldInputs.lean, ~370 lines,
  DONE/green) already PROVES the STRONGER `Φ.source k` statement using `hchi` in
  its positive-order collar branch. To actually DROP `hchi`, `covTail_of_bounds`
  would have to be rewritten to only target `grow k` — a substantial rewrite of a
  large, verified proof, NOT the "~1 focused edit" ruling A budgets for.
- Ruling A's own escape clause: if bigger than ~1 edit or destabilizing, SKIP and
  carry `hchi` as one more tracked input ("a genuine bump-tower bound, not a
  wrapper"). So: SKIPPED. `hchi` is carried as a tracked input of the endgame.

## Ruling B (mc time-0 discharge / referenceMetric freeness)

`MetricSourceData.referenceMetric` is a FREE field (confirmed: `limit_inner`/
`pullback_inner` pin only the limit/pullback slots; nothing pins reference). The
7a producer `conv0_of_cp` consumes `hcp` stated ENTIRELY in flow-side terms
(`srcMetric`/`resSrc g0`/`refRes R`), NOT in `mc`'s `MetricSourceData`. So `hcp`
is carried as a tracked input (the "mc-comparison data" the plan sanctions);
Theorem 3.9's public conclusion `MetricCompactnessConclusion` is NOT changed.

## Historical status (2026-07-04; superseded): phantom-L refactor blocker

- **`flowLimit_of_co` (the assembly core) — VERIFIED.** Targeted `build +…ConvFieldEndgame`
  = "Build completed successfully (3923 jobs)"; `flowLimit_of_co` builds sorry-free. It takes
  `(mc, L, hL0, R, bf, hsrc, htgt, β, ψ, hcarrier, co, hLmetric, scalar)` and assembles the full
  8-field `FlowLimitData` for `mc' := mc.compSubseq co.φ co.hφ` → `flowLimit_upgrade` →
  `CompactnessConclusion X`. All 8 fields (`L`/`hL0`/`maps`/`scalar`/`hσsrc`/`hσtgt`/`refMetric`/`conv`)
  discharged: σ-compactness via `isSigmaCompact_of_isOpen`, `refMetric` via `refRes`, and the
  `conv` field via `ofRP_supOn_conv` + the sub-window inclusion (`Φ'.partialDiffeomorph k`
  reduces to `endgamePhi.partialDiffeomorph (co.φ k)` by `rfl`, so `ofRestrictPullback` reduces
  with no `▸`-cast). Rulings A (SKIP, carry `hchi`) and B (`referenceMetric` free, `hcp` carried)
  as recorded above.
- **Unused imports dropped.** `LimitSolutionEquation`/`RicciFromJets`/`FlowLimitRegularity` are
  NOT used by `flowLimit_of_co` (it takes `co`/`scalar`/`hLmetric` as inputs, does not construct
  the PDE data), so their imports are omitted to keep the core buildable. The FULL endgame
  (constructing `L` and the PDE inputs) must re-add them.

## Historical frontier (superseded): phantom-L instantiation circularity

`flowLimit_of_co` takes `L`, `co : ConvOut (endgamePhi mc L hL0) …`, and `hLmetric :
L.S.family.metric = co.gInf` as INPUTS. To instantiate the endgame they must be constructed:
`L := flowOfMetric X.D mc.limit co.gInf (isSolutionOn_of_reg … hsmooth …)` — but `co` needs
`endgamePhi mc L hL0`, which needs the TERM `L`. **Genuine term-level circularity** (`L` needs
`co.gInf`; `co` needs `L`). A dummy `L₀` is impossible: `PointedFlowData` requires
`isSolution : IsSolutionOn`, and the only solution metric IS the AA limit `co.gInf` (a constant
family is not a Ricci flow — ruling 5b forbids provisional `L`).

**The resolution (identified, NOT yet executed — a multi-file refactor):**
`PointedCGHMaps X L subseq` (`PointedConvergence.lean:499`) uses `L` ONLY through
`L.M`/`L.topology`/`L.charted`/`L.basepoint` — NEVER `L.S`/`L.smooth`/`L.sigmaCompact`/`L.t2`
(verified by reading the structure: its 4 fields mention only those projections). So the fix is
to **re-parametrize the `Φ`-indexed AA machinery by a manifold-data record (or
`PointedRiemannianManifold`) instead of the full `PointedFlowData L`**. Then the construction
is non-circular: build the AA over `mc.limit : PointedRiemannianManifold` directly → `gInf` →
`L := flowOfMetric X.D mc.limit gInf hsol` (whose `(M,topology,charted,basepoint)` = `mc.limit`'s
by `rfl`, per `flowOfMetric`) → the `FlowLimitData.maps : PointedCGHMaps X L subseq` holds over
`L` by defeq (same manifold data). **Scope:** mechanical (only 4 projections of `L` appear) but
cascades through the whole `Φ`-indexed chain: `PointedCGHMaps` + `source`/`SourceDomain`/
`sourceFlow`/`gSeqExt`/`ConvOut`/`convOut` + `ConvFieldInputs` producers + `FlowLimitData.maps`/
`flowLimit_upgrade`. Est. 1 focused refactor session. This is the ONLY remaining blocker to a
non-vacuous endgame; `flowLimit_of_co` is ready to consume the re-parametrized pieces.

## Separate blocker: `RicciFromJets.lean` mojibake (owning session)

`RicciFromJets.lean` currently fails to compile with "expected token" at `:1916:68`/`:2033:13` —
double-encoded-unicode corruption (`≤` → `â‰¤`, bytes `c3 a2 e2 80 b0 c2 a4`), the exact trap the
plan's danger points flag. It is a parallel session's file (not claimed). This blocks the FULL
endgame's PDE-input path (`ricciConv_of_dnConv`/`scalarConv_of_dnConv`) but NOT the assembly core.
Byte-reversible repair by the owning session (or a sanctioned mojibake fix) needed before the PDE
inputs can be wired.

## Verification

`build +…ConvFieldEndgame` GREEN (3923 jobs); `#print axioms flowLimit_of_co
= [propext, Classical.choice, Quot.sound]` (verified 2026-07-04, no sorryAx; the
`MetricCompactness.lean:1138`/`Field.lean:282` sorry warnings are unrelated declarations
`flowLimit_of_co` does not depend on).

## Historical refactor spec (superseded — do not execute): P-index re-parametrization

**Key simplifier (verified):** `PointedCGHMaps X L subseq` (`PointedConvergence.lean:499`) and
`PointedRiemannianCGMaps (X.atZero) (L.atTime 0) subseq` (`MetricCompactness.lean:35`) have the
IDENTICAL 4-field structure (`partialDiffeomorph`/`source_exhausts`/`base_mem`/`basepoint_map`);
the manifolds coincide because `X.atZero.obj k = (X.term k).atTime 0` and `L.atTime 0` preserve
`M/topology/charted/basepoint`. And **`mc.maps : PointedRiemannianCGMaps (X.atZero) mc.limit
mc.subseq`** already. So build the AA over `mc.limit : PointedRiemannianManifold` DIRECTLY.

**The circularity (why the re-index is unavoidable):** `co : ConvOut (endgamePhi mc L hL0)` is
typed over `PointedCGHMaps X L subseq` ⟹ needs the TERM `L : PointedFlowData`; `L := flowOfMetric
mc.limit co.gInf (isSolutionOn_of_reg … hsmooth …)` needs `co.gInf`. No dummy `L₀` (PointedFlowData
requires `isSolution`; the only solution metric is `co.gInf`). Re-indexing the AA machinery by
`PointedRiemannianCGMaps X' P subseq` (`X' : PointedRiemannianSeq`, `P : PointedRiemannianManifold`)
removes `L` from `co`'s type ⟹ build `co` over `(X.atZero, mc.limit, mc.maps)` first, then `L`.

**File-by-file (bottom-up; each is a signature `L : PointedFlowData → P : PointedRiemannianManifold`
+ `X : PointedFlowSeq → (X' : PointedRiemannianSeq, and pass the FLOW seq `X` separately ONLY where
`X.term k` — the k-th flow — is actually pulled back, i.e. `sourceFlow`) + `L.foo → P.foo` renames;
NO proof rewrites where re-typing suffices):**
1. `PointedConvergence.lean` (51 refs — the bulk): re-index `PointedCGHMaps` and ALL of
   `source`/`SourceDomain`/`sourceOpen`/`targetOpen`/`sourceDomTop/Charted/Smooth/T2/SigmaOf`/
   `targetDom*`/`sourceTargetDiff`/`SourceDomainMetricData`/`ofRestrictPullback`/`derivNormSupOn`
   by `P : PointedRiemannianManifold`. **`ofRestrictPullback.limitMetric` currently uses
   `L.S.family.metric t`** → add a `limitMetricFamily : ℝ → SmoothRiemannianMetric I P.M` argument
   (Brick-5 `ofRP_supOn_conv` already mediates it via `hmetric`, so consumers are hyp-compatible).
   PREFER: make `PointedCGHMaps X L subseq` a thin `def := PointedRiemannianCGMaps (X.atZero)
   (L.atTime 0) subseq` so `HamiltonPositiveRicciAdapter` + `FlowLimitData.maps` keep working by
   defeq. Rebuild green (heavy file — check `HamiltonPositiveRicciAdapter` still compiles).
2. `SourceDomainFlow.lean` (4): `sourceFlow`/`isSolutionOn_sourceFlow`/`sourceFlow_metric_eq`
   re-index by `P`; `sourceFlow` additionally takes the FLOW seq `X` (for `X.term (subseq k)).S`).
3. `MetricCompactnessSubseq.lean`: `compSubseq` re-index (if it references the maps' L).
4. `ConvFieldAssembly.lean` (2): `gSeqExt`/`BumpFamily`/`hlow`/`hbdd`/`hgLip` re-index by `P`.
5. `ConvFieldMain.lean` (1) + `ConvFieldInputs.lean` (1): `ConvOut`/`convOut`/`ofRP_supOn_conv`/
   the 5 producers re-index by `P`.
6. `FlowLimitUpgrade.lean` (5): `FlowLimitData.maps` re-types over `L.atTime 0` (defeq via the
   `PointedCGHMaps` alias); `pointedCGHMaps_of_atZero`/`cghMaps_of_hL0` simplify or become `id`.
7. `ConvFieldEndgame.lean` (this file — re-add the 3 dropped PDE imports after `RicciFromJets`
   mojibake is repaired): the NON-circular instantiation:
   `co := convOut (X.atZero) mc.limit mc.maps R bf hsrc htgt β ψ … (7a producers)` →
   `L := flowOfMetric X.D mc.limit co.gInf (isSolutionOn_of_reg co.gInf hsmooth (hpde from
   metricLimit_pdeOn∘ricciConv_of_dnConv on co.convPt) (scalar/ricci/rm04 continuity))` →
   `hL0 := flowOfMetric_atTime … (gInf_zero_eq … from mc.convergence via conv0_of_cp)` →
   `flowLimit_of_co mc L hL0 R bf hsrc htgt β ψ hcarrier co hLmetric scalar` (hLmetric =
   `flowOfMetric_metric` rfl) → `FlowUpgradeData X mc` via the checked upgrade
   constructor → `solutionComp_of_mc X mc`.  The former
   `smoothFlowLimitInput_of_flowLimitData` route was deleted. Tracked inputs:
   `mc` (Thm 3.9), the moving-Shi bounds
   (via `srcShi`), `hsmooth`, + the 7a-carried comparison data (`hequivT`/`hrel`/`hcp`/`hcovSrc`/
   `hlipG`/`hchi`).

**Scope/why not in-session:** ~73 refs across 8 files incl. the foundational cross-session-shared
`PointedConvergence.lean`; a structural-index change is not incrementally green (tree broken until
the whole cascade converts), so it needs a clean full-budget session in one coherent pass, then the
`RicciFromJets.lean` mojibake repair before the PDE-import re-add. The assembly core `flowLimit_of_co`
is verified and consumes the re-indexed pieces unchanged.

## EMPIRICAL FINDINGS from the 2026-07-04 execution attempt (restored, tree left green)

An attempt was made (snapshots `.pre7b`, restored per the rule-3 discipline — no half-converted
tree left). Concrete findings that REFINE the recipe:

1. **Unification via alias is IMPOSSIBLE** — `MetricCompactness.lean` (home of
   `PointedRiemannianCGMaps`) IMPORTS `PointedConvergence.lean`, so `PointedConvergence` cannot
   reference `PointedRiemannianCGMaps` (circular). **Decision:** keep `PointedCGHMaps` a `structure`,
   just re-index its own binder `(L : PointedFlowData X.D) → (P : PointedRiemannianManifold)`. This is
   actually SIMPLER (no `X.atZero` inside `PointedConvergence`; `PointedCGHMaps X P subseq`).
2. **The uniform rename works cleanly** for ~270 refs via a mojibake-safe Python `.replace` (io utf-8,
   newline=''): binders `(L : PointedFlowData (I := I) X.D)`/`{…}` → `(P : PointedRiemannianManifold
   (I := I))`, `PointedCGHMaps (I := I) X L subseq` → `… X P subseq`, and `L.M/topology/charted/smooth/
   sigmaCompact/t2/t2TangentBundle/basepoint` → `P.*`. Leaves exactly the `L.S`-role refs.
3. **`limitMetricFamily : ℝ → SmoothRiemannianMetric I P.M` threading** (the `L.S`-role, 6 refs):
   `SourceDomainMetricData` (add a field + `limit_inner` uses `(limitMetricFamily t)` not
   `L.S.family.metric`), `ofCanonical` (add param + constructor line), `ofRestrictPullback` (add param;
   `limitMetric := restrictOpen (limitMetricFamily t)`; pass to `ofCanonical`), `ScalarPullbackTendsto`
   (add param; `uInf := metricScalarAt (limitMetricFamily t) x` — NOT `L.S.scalar t x`).
4. **UNDER-SCOPED in the original spec — the OUTPUT-convergence layer also needs the family.**
   `PointedCGConverges`/`SmoothCGHConverges` (`PointedConvergence.lean:~1770/1779`) and downstream
   `CompactnessConclusion`/`flowLimit_upgrade` bundle the maps + scalar convergence; the flows converge
   to the LIMIT FLOW's metric FAMILY, which `P : PointedRiemannianManifold` (single metric) lacks.
   Either (a) thread `limitMetricFamily` through them too, OR (b) keep `PointedCGConverges`/
   `SmoothCGHConverges` indexed by `L : PointedFlowData` with their `maps` field typed
   `PointedCGHMaps X (L.atTime 0) subseq` (P := L.atTime 0) and `scalar_converges :
   ScalarPullbackTendsto maps (L.S.family.metric)`. **(b) is likely cleaner** (keeps flow-output
   structures flow-aware; only the maps/metric machinery goes P-indexed). The `… X L subseq` straggler
   also hits `PointedCGConverges`/`SmoothCGHConverges` (3 sites) — a broad `X L subseq → X P subseq` is
   NOT safe there under option (b); handle them by option (b) instead.
5. **Revised effort:** honest multi-hour, one-coherent-pass session — the maps/metric machinery rename
   (~mechanical, scripted) + the `limitMetricFamily` threading (~5 defs) + the output-layer decision
   (option b) + the 6-file cascade + the endgame instantiation. The Python rename script is at
   `scratchpad/reindex_pc.py` (reproducible). Snapshots were removed after restore.

## Historical mechanical execution map (superseded; 2026-07-05 record)

The zone-aware rename + full threading surface are now mapped exactly. A future one-pass session
(ideally with a committed checkpoint so `git checkout` is the revert, or commit-per-file) applies:

**PointedConvergence.lean — ZONE-AWARE (split at the docstring `/-- Pointwise pullback convergence
of scalar curvature`, i.e. just before `def ScalarPullbackTendsto`):**
- **P-zone (lines 1..split, the maps/metric machinery + metric-convergence + `FunctionPullbackTendsto`):**
  the validated uniform rename — binders `(L : PointedFlowData (I := I) X.D)`/`{…}` →
  `(P : PointedRiemannianManifold (I := I))`/`{…}`; `PointedCGHMaps (I := I) X L subseq` → `… X P subseq`;
  `L.{M,topology,charted,smooth,sigmaCompact,t2,t2TangentBundle,basepoint}` → `P.*`. (Script:
  `scratchpad/reindex_pc2.py`.) Leaves exactly 5 `L.S` = the metric-family refs to thread.
- **L-zone (split..EOF: `ScalarPullbackTendsto` 1735, `PointedCGConverges` 1770, `SmoothCGHConverges`
  1779 + `ofSpacetime`/`ofRestrictPullback`):** KEEP `L : PointedFlowData` binders; only retype
  `PointedCGHMaps (I := I) X L subseq` → `… X (L.atTime 0) subseq` (4 sites); KEEP `L.S.scalar` (1 ref).
  `ScalarPullbackTendsto` needs NO `limitMetricFamily` param (it keeps `L`, so `L.S.scalar` is in scope) —
  this SUPERSEDES finding-3's `ScalarPullbackTendsto` line.

**`limitMetricFamily : ℝ → SmoothRiemannianMetric I P.M` threading (the 5 P-zone `L.S` + the chain):**
- `SourceDomainMetricData` (struct @1050): ADD field `limitMetricFamily`; `limit_inner` (@1092) uses
  `(limitMetricFamily t)` not `L.S.family.metric`.
- `ofCanonical` (@1135): ADD param before `limit_inner`; `limit_inner` param (@1174) uses it; constructor
  line `limitMetricFamily := limitMetricFamily`.
- The **producer chain — each ADDS a `limitMetricFamily` param and passes it to the call below**:
  `SourceDomainMetricData.ofRestrictPullback` (@1232; sets `limitMetric := restrictOpen (limitMetricFamily t)`;
  @1294/1324/1325) ← `SourceMetricConvergenceData.ofRestrictPullback` (@1551; calls @1574/1579) ←
  `SourceSpacetimeConvergenceData.ofRestrictPullback` (@1651; calls @1675/1679) ← [L-zone]
  `SmoothCGHConverges.ofRestrictPullback` (@1812; call @1837 SUPPLIES `L.S.family.metric`).
- **All 11 `SourceDomainMetricData.ofRestrictPullback` call sites** get the family arg after
  `(referenceMetric …)`: `PointedConvergence` 1574/1579/1675/1679/1837; `ConvFieldMain` 409/447/533/584
  (supply `co.gInf`-side / the mediating family); `FlowLimitUpgrade` 114 (`FlowLimitData.conv`);
  `SourceDomainFlow` 249.

**Cascade (call-site P-inference + the family arg): `SourceDomainFlow`, `MetricCompactnessSubseq`,
`ConvFieldAssembly`, `ConvFieldMain`, `ConvFieldInputs`, `FlowLimitUpgrade`** — then the endgame
instantiation (unchanged from §7 above).

**PROCESS NOTE (2 budget-bounded restores now):** this refactor reproducibly exceeds one agent-turn.
Recommend the planner either (i) run it as a single uninterrupted full-context pass with a COMMITTED
checkpoint (so revert = `git checkout`, not snapshots), OR (ii) split into committed sub-steps —
commit after `PointedConvergence` converts+`build +…PointedConvergence` green, then the cascade
file-by-file — so it proceeds incrementally without the all-or-nothing shared-tree risk. The rename
is scripted (minutes); the threading is the 11 sites above; the endgame core `flowLimit_of_co` is
verified and consumes the result unchanged.
