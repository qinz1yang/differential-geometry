# ConvFieldAssembly.lean — Brick 4 of the P4 conv engine

**Goal.** On the single limit manifold `M∞ = L.M`, build the bump-extended sequence
`gSeqExt : ℕ → ℝ → SmoothRiemannianMetric I L.M` and prove the three RAW hypotheses of
`windowGInfAll` (`MetricPreconvWindowAll.lean`) for it with `gRef := R`:
`hbdd` (∀-compact cov bounds), `hgLip` (∀-compact/∀-order time-Lipschitz), `hlow`
(uniform `c·R ≤ gSeqExt`).  Deliverable = `gSeqExt` + the 3 hypotheses + the dense net,
sorry-free, so Brick 5 can call `windowGInfAll`.

## Parametrization (plan KEY fact #5)

Section is parametrized by `(L : PointedFlowData X.D)`, a subsequence, and
`Φ : PointedCGHMaps X L subseq`.  `M∞ := L.M`; `R : SmoothRiemannianMetric I L.M`.
Every mc-derived analytic input (moving-Shi on the sequence flows, window
metric-equivalence, lower bound, initC seed) enters as a HYPOTHESIS stated against `Φ`.

## Source flow + bump construction

- `sourceFlow Φ k` (Brick 2) is a `SolutionOn` on `SourceDomain Φ k = ↥(sourceOpen Φ k)`
  (open subtype of `L.M`).  `sourceFlow_metric_eq` : its metric family is
  `ofRestrictPullback.pullbackMetric t = Diffeomorph.pullbackMetric ((S_k.metric t).restrictOpen (targetOpen)) (sourceTargetDiff)`.
  Call it `srcMetric k t : SmoothRiemannianMetric I (SourceDomain Φ k)`.
- Compact exhaustion `Kx : CompactExhaustion L.M`.  For each `j`, threshold
  `m j := (Φ.source_exhausts.subset (Kx j) (Kx.isCompact j)).choose` gives `Kx j ⊆ Φ.source k` ∀ k ≥ m j.
- Bump family: opens `V j` with `Kx j ⊆ V j ⊆ closure (V j) ⊆ Φ.source (m j)` (compact closure
  via `exists_isOpen_..`/normality), bumps `χ j : L.M → ℝ`, `χ j = 1` on `Kx j`,
  `tsupport (χ j) ⊆ Φ.source (m j)`, valued `[0,1]`, smooth.
- Per-k bump index `bidx k := largest j with m j ≤ k` (0 if none, use a single named
  `threshold`/`bidx` helper to avoid omega drift).
- `gSeqExt k t := if h : ∃ j, m j ≤ k then R.bumpExtendOpen (sourceOpen Φ (m (bidx k))) (srcMetric (m (bidx k)) t) (χ (bidx k)) … else R`.
  (constant-R head below `m 1`, KEY fact #4).

**PROBLEM discovered while wiring: `srcMetric` at threshold `m (bidx k)` vs at `k`.**
The source domains differ per `k`; the bump uses `sourceOpen Φ (m (bidx k))` and the
source flow of THAT index.  Need one clean indexing.  (Design in progress.)

## Difficulty ranking (why the deliverables split)

- **`hlow` (EASIEST, no covariant derivatives).** `c·R ≤ gSeqExt k t` pointwise.  On `V`
  (χ=1): `gSeqExt = srcMetric`, and `srcMetric ≥ c·R` from the transported window
  equivalence (`metricUniformEquivalentOnWindow_restrictOpen` ∘ `_pullback`) + the pullback
  isometry.  Off `V` (annulus/outside): `bumpForm = χ•src + (1-χ)•R`, both summands `≥ c'·R`
  (src via equivalence, R via `1·R`), so convex combo `≥ min(c',1)·R`.  Pointwise convex-combo
  inequality — CLEAN.  Time-0 seed for `initC` from `mc.convergence` (Brick 5 concern; hlow
  itself needs only the equivalence hyp).

- **`hgLip` (MEDIUM).** `metricDerivNorm a (gSeqExt k s) (gSeqExt k t) R x ≤ L|s-t|`.  Same `k`,
  same bump `χ`.  `bumpForm` is AFFINE in the source metric, so the difference tensor
  `gSeqExt k s − gSeqExt k t = χ•(src_s − src_t)` (the `(1-χ)•R` cancels).  The order-0 seminorm
  should transport by scaling by `χ ∈ [0,1]`.  But higher-order metricDerivNorm involves the
  metricCovDeriv of the DIFFERENCE against `R`, and `χ` is `x`-dependent → product-rule terms.
  TAIL via `hgLipFinSol`/`hgLip0Sol` on `sourceFlow` transported; HEAD `metricDerivNorm a R R = 0`.
  Annulus higher-order = same wall class as hbdd.

- **`hbdd` (HARDEST — the flagged wall).** `metricCovDerivNorm q (gSeqExt (ρk) t) R z ≤ C` ∀k,
  ∀z∈K'.  TAIL (`k ≥ m(j₀)` where `K'⊆Kx j₀`): `gSeqExt = srcMetric` on `K'`, transported bound
  via `covBddAllSol` on `sourceFlow` (needs SolCovData on source flow — from cited inputs,
  restriction-invariance `metricCovDerivNorm_restrictOpen`??? + `_pullback`).  HEAD/MID (finitely
  many `k < m(j₀)`): each `z ↦ metricCovDerivNorm q (gSeqExt k t) R z` bounded on compact `K'`.
  **WALL: NO `metricCovDerivNorm` spatial-continuity / BddAbove API exists** (confirmed:
  `LimitSolutionEquation.md:70`, no grep hits for `metricCovDerivNorm.*Continuous`).  The
  annulus (`support χ \ V`) bump metric's covariant-derivative norm cannot be bounded by
  transport (it is a genuine χ-weighted convex combo, not the pullback) and the
  continuity+compactness route is blocked by the missing continuity lemma.
  → smallest missing API: `metricCovDerivNorm_continuousOn` (or `ContinuousAt`), assembled from
  `tensor0SField_eval_smooth_slots_contMDiffAt` (smoothness of the `metricCovDeriv g R q` tensor
  field as a section) + continuity of `x ↦ normSq0S R x (A x)` for a continuous tensor field `A`
  + `Real.sqrt` continuity.  This is a real sub-project (build the continuity of the whole
  covariant-derivative tower as a section, then compose).

## Status (2026-07-02 — `hbdd` LANDED)

DELIVERED sorry-free (targeted build green 3911 jobs + `#print axioms` = `[propext,
Classical.choice, Quot.sound]`):
- `SrcSigma`/`TgtSigma` (per-`k` σ-compactness inputs), `srcMetric` (source-flow metric extractor).
- `BumpFamily` structure + `nonempty_bumpFamily` (existence: compact exhaustion `Kx`,
  `bidx = findGreatest`, collar `V` via normality, cutoff via
  `exists_contMDiffMap_one_nhds_of_subset_interior`, `tsupport ⊆ closure V ⊆ Φ.source k`).
- `gSeqExt` (the bump-extended sequence on `L.M`).
- `gSeqExt_inner_of_mem` / `gSeqExt_inner_of_notMem` (pointwise evaluation).

## 2026-07-17 fixed-family reindexing bridge

Added `SrcSigma.compSubseq`, `TgtSigma.compSubseq`, and
`BumpFamily.compSubseq`, together with the definitional readout
`gSeqExt_compSubseq`.  Thus the open-time diagonal keeps one original bump
family while a fixed-window producer is rerun after any prescribed refinement;
it does not choose a fresh bump family for each time window.  Verification is
focused-green and the exact module refresh is green.
- `hlow_gSeqExt` (the `hlow` hypothesis of `windowGInfAll`): from the cited uniform source
  lower bound `cLow·R ≤ srcMetric`, `gSeqExt (ρk) t ≥ min(cLow,1)·R` everywhere — convex-combo
  on the support, `=R` off it.  CLEAN, no covariant derivatives.
- **`hbdd_gSeqExt` (the `hbdd` hypothesis of `windowGInfAll`) — NEW.**  Cited hypothesis
  `hcovTail : ∀ q, ∃ C, ∀ k t∈[β,ψ], ∀ z∈Φ.source k, metricCovDerivNorm q (gSeqExt k t) R z ≤ C`
  (uniform over `k`, discharged in Brick 5 from Thm 3.9's window covariant bounds transported to
  the source flows).  Proof: `grow_cover` gives `k0` with `K' ⊆ grow (ρ k) ⊆ Φ.source (ρ k)` for
  `k0 ≤ k` (using `k ≤ ρ k` via `StrictMono.id_le`); the TAIL then inherits `Ctail` directly.
  The finitely many HEAD/MID indices `k < k0` are each ONE fixed smooth metric, bounded on `K'`
  by `metricCovDerivNorm_bddOn` (`MetricCovDerivContinuity.lean`, the CONSUMED unblocker — no
  annulus analysis).  Combine `C := max Ctail ((Finset.range (k0+1)).sup' Chead)`.  KEY: consumed
  `MetricCovDerivContinuity.lean` (import added); no χ-Leibniz needed because `hbdd` fixes `t`
  before `∃C`, so each metric is a fixed smooth metric.
- Dense net: reuse `denseIccSeq` (`MetricPreconvWindowSolutions.lean`) directly at Brick 5.

Added to `Geometry/Metric/BumpExtend.lean` (canonical home): `bumpExtendOpen_inner` (all-`x` convex
formula) + `bumpExtendOpen_inner_of_notMem_tsupport` (off-support = `R`).

## FRONTIER (hgLip only) — blocked on the χ-Leibniz collar tower

`hgLip` (time-Lipschitz, all orders `a ≤ p`) is NOT delivered.  The obstruction is now sharper
than the earlier "missing continuity" diagnosis (that was RESOLVED — `metricCovDerivNorm_bddOn`
LANDED and dispatches `hbdd`).  The genuine wall for `hgLip` is the **bump collar Lipschitz
factor**:

`hgLip` needs `metricDerivNorm a (gSeqExt k s)(gSeqExt k t) R z ≤ L·|s−t|` for all `a ≤ p`, all
`k`, on every compact `K'`.  The time difference cancels the `(1−χ)R` summand:
`gSeqExt k s − gSeqExt k t = χ_k · (src_s − src_t)` on `Φ.source k`, and `= 0` off `tsupport χ_k`
(dichotomy `z ∈ Φ.source k ∨ z ∉ tsupport χ_k` is TOTAL since `tsupport χ_k ⊆ Φ.source k`).  So
the seminorm at order `a` is `√ normSq0S R z (a+2) (∇_R^a (χ_k·(src_s−src_t)))`.

- **Order 0** (`a = 0`): `∇^0(χ·T) = χ·T`, `normSq0S R z 2 (χ·T) = χ²·normSq0S R z 2 T`, so
  `metricDerivNorm 0 = |χ_k z|·√normSq0S R z 2 (src_s−src_t at z) ≤ 1·(source order-0 Lip) ≤ L|s−t|`.
  TRACTABLE from a cited order-0 source Lip.
- **Orders `a ≥ 1` on the collar `{0 < χ_k < 1}`**: `∇_R^a(χ_k·T)` expands by the Leibniz/binomial
  tower into `Σ_{i≤a} (∇_R^i χ_k) ⊗ (∇_R^{a−i} T)` (with slot cycles).  The `∇^i χ_k` factors are
  bounded on the compact `K'` (fixed smooth `χ_k`), and `∇^{a−i} T = ∇^{a−i}(src_s − src_t)` is
  time-Lipschitz from the source (`hgLipFinSol` transported).  But the χ-Leibniz tower
  `|∇^a(χ·T)|_R ≲ Σ_i |∇^i χ|_R · |∇^{a−i} T|_R` is **CONFIRMED MISSING** (grep-verified; the
  single-STEP tensor-product rule `nabla0S_product_realizes` in
  `Tensor/RSTensor/ProductNablaLeibniz.lean` exists, but the ITERATED all-orders bound + its
  norm sub-additivity is a multi-lemma sub-project).

The consumer `windowGInfAll` needs ONE `L` for ALL `a ≤ p`, so an order-0-only lemma is NOT
consumable — `hgLip` is all-or-nothing.  Carrying the collar bound as a "cited" hypothesis on all
of `Φ.source k` (rather than only on `grow k` where `χ = 1`) would be a forbidden
frontier-wrapper: the source producers genuinely bound only the `χ = 1` region (`grow k`), NOT the
collar, so an honest cited hypothesis leaves the collar uncovered.

**Smallest unblocking API** (a real sub-project, ~1 session): the iterated χ-Leibniz norm bound
`metricCovDerivNorm a (χ·T) ... ≤ Σ_{i≤a} C(a,i)·‖∇^i χ‖·metricCovDerivNorm (a−i) T ...`, built by
induction from `nabla0S_product_realizes` (one-step Leibniz) + `metricDerivNorm_bddOn`-style
compact bounds on `∇^i χ` + `Real.sqrt`/`normSq0S` sub-additivity.  With that lemma the collar
closes: `∇^{a−i}(src_s − src_t)` carries the `|s−t|` factor from the transported source time-Lip,
and the finitely-many `∇^i χ` factors are bounded on `K'`.

Obstruction class: MISSING API (reusable tensor-algebra infrastructure — the iterated Leibniz
tower), not a mathematical obstruction.  The bound is true; the Lean tower lemma is absent.

## hgLip_gSeqExt LANDED (2026-07-03, planner-verified: build green 3912, axiom-clean)

All three raw hypotheses are now delivered; Brick 4 DONE. The theorem followed the header
proof plan (tail = cited gSeqExt-granularity Lipschitz on `grow k`; head/mid = χ-Leibniz via
the BANKED m-fold tower `iterCov_smulF_le` + `smulByFun_eq_product` + `metricDerivNorm_eq_iterCov`;
constants by `Finset.sup'`). Two final-mile repairs (after a third process crash killed the
executor mid-verification):

- **Instance-spelling gap**: implicit resolution cannot cross `SourceDomain Φ k` vs
  `↥(sourceOpen Φ k)` — `restrictOpen`'s `[SigmaCompactSpace U] [T2Space U]` goals sit at the
  `↥` spelling where the `SourceDomain`-spelled letIs do not fire (and vice versa). letI
  aliases at the other spelling do NOT fix it (the underlying `TopologicalSpace` instance
  argument still mismatches). The working idiom (same as `gSeqExt`'s `bumpExtendOpen` call and
  `ofRestrictPullback`): `let inst : C ↥(sourceOpen …) := by change C (SourceDomain …); exact …`
  then pass EXPLICITLY via `@`. Encapsulated once as the file-level `private def refRes`
  (restricted reference metric), 31 call sites swapped.
- **Generic-rank instance wall**: `HSub (Tensor0SField ∞ 2) …` fails synthesis (whnf timeout
  shape) — the codebase's own `set_option backward.isDefEq.respectTransparency false in`
  workaround applies, and it must go BEFORE the theorem's doc comment (after it = parse error).

## 2026-07-03 (Brick-5 session): encoding corruption repaired; `refRes` un-privatized

This file was found DOUBLE-ENCODED on disk (UTF-8 bytes re-read as cp1252 and re-saved as
UTF-8 **with BOM**) after the morning green build.  The BOM breaks Lake's import-header scan
(`setup.json` gets `"importArts": {}`), which surfaces as the misleading
`invalid -D parameter, unknown configuration option 'linter.style.emptyLine'` on every fresh
compile.  Repaired byte-reversibly (BOM stripped; cp1252 round-trip with C1-control fallback;
zero mojibake residue), rebuilt GREEN.  If this error shape reappears, check the file head for
`EF BB BF` before suspecting the lakefile.  (`RicciFromJets.lean` had the same BOM as of this
session — owned by a parallel session, not touched.)

`refRes` is now PUBLIC (was `private`): Brick 5 (`ConvFieldMain.lean`) states its carried
hypotheses (`hlipSrc`-granularity) and the conv-field reference slot against it, and adds the
general-metric mirror `resSrc` (with `refRes_eq_resSrc : … := rfl`).

## 2026-07-17: normalization compatibility repair

Two metric-tensor extensionality proofs stopped because their combined `simp only` step made
no progress after the imported normal forms changed. Replacing that fragile normalization with
explicit rewrites by `metricTensorField_apply` and `restrictOpen_inner` preserves the statements
and proof route. Focused verification and the exact module refresh both passed. Brick 4 remains
complete; this maintenance repair changes no theorem, machinery, or whole-project progress
estimate.

## 2026-07-17: canonical exact lower-bound producer

The convex-combination proof formerly embedded in `hlow_gSeqExt` is now the public theorem
`gSeqExt_lower`. It gives the exact constant `min cLow 1` for every sequence index and every
time in the window; no subsequence parameter is needed because the source/off-source dichotomy
covers all stages. `hlow_gSeqExt` keeps its existing public statement and is now only the
compatibility consumer that packages this positive constant along an arbitrary strict
subsequence. Focused verification and the exact module refresh passed.

Accounting is unchanged: this exact producer and the `hlow` sub-brick are 100%, Brick 4 remains
100%, and no downstream endpoint or mathematical input was discharged. The conditional P4
assembly remains checked from its tracked inputs, while unconditional Theorem 3.10 remains 0%;
the whole-HCG machinery estimate remains roughly 45%, with the unconditional project endpoint
still 0%.

## 2026-07-18: grow-local covariant tail

`hbdd_gSeqExt` now asks for the uniform covariant estimate only on `bf.grow k`,
which is the region its tail proof actually consumes. The obsolete conversion
from grow membership to the whole source domain was removed. Focused
verification and the exact module refresh pass.
