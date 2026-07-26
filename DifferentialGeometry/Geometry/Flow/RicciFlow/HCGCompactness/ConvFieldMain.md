# ConvFieldMain.lean — Brick 5 of the P4 conv engine

**Goal.** Apply `windowGInfAll` to the Brick-4 bump-extended sequence `gSeqExt`,
package the output as DATA (`ConvOut`: one `φ`, one global `gInf`, sup-level
`conv` + pointwise `convPt` along the SAME subsequence), prove the conv-field
bridge (the `FlowLimitData.conv` shape at `(Φ, φ k)` granularity), and identify
`gInf 0` with the time-0 Cheeger–Gromov limit.

## Deliverables (statement shapes)

- `ConvOut Φ R bf hsrc htgt β ψ` (structure, ruling 5a): fields `φ : ℕ → ℕ`,
  `hφ : StrictMono φ`, `gInf : ℝ → SmoothRiemannianMetric I L.M`,
  `conv` (∀ K compact ∀ p ∀ ε>0 ∃ k0 ∀ k≥k0 ∀ t∈[β,ψ]:
  `metricDerivNormSupOn K p (gSeqExt (φ k) t) (gInf t) R < ε`),
  `convPt` (same, pointwise `∀ a ≤ p ∀ x ∈ K` — the Brick-6 consumer shape,
  e.g. `FlowLimitRegularity.lean`'s `hconv` at `a = 0`, and the z = x instance
  feeding `ricciConv_of_dnConv`).
- `convOut` (def): ONE `windowGInfAll` call; raw hypotheses discharged by
  `hgLip_gSeqExt`/`hbdd_gSeqExt`/`hlow_gSeqExt`; carried cited inputs at the
  EXACT Brick-4 granularity (dischargers unchanged): `hbound` (uniform source
  lower bound, `cLow·R ≤ srcMetric`), `hcovTail` (∀q ∃C tail covariant bound on
  `Φ.source k` at `gSeqExt` granularity), `hlipTail` (gSeqExt-granularity
  time-Lipschitz on `grow k`), `hlipSrc` (per-k source-granularity time-Lipschitz
  vs `refRes`).  Extraction via `.choose` (Prop-∃ → data, `Classical.choice`);
  `convPt` derived along the SAME `φ` by the `windowGInfAll_pt` BddAbove pattern
  (singleton-tail split; `derivNorm_le_sup_sing` + `derivNorm_le_cov_add` +
  `metricDerivNorm_triangle`, `hbdd_gSeqExt` along `φ` supplies the `Cf q`).
  Instances at `L.M`: letI five + `WeaklyLocallyCompactSpace` via
  `ChartedSpace.locallyCompactSpace` (the `nonempty_bumpFamily` idiom);
  `Nonempty L.M := ⟨L.basepoint⟩`; dense net = `denseIccSeq` (needs `β ≤ ψ`).
- `ConvOut.comp_subseq`: checked.  It retains the fixed-window limit family
  and both convergence fields after a further strict reindexing.  This is a
  downstream stability operation; the open-window diagonal still needs to
  rerun the fixed-window producer after each already-chosen outer subsequence.
- `ofRP_supOn_eq` (per-index three-slot identification): for `K ⊆ bf.grow k`
  and `hmet : L.S.family.metric t = gIt`,
  `(ofRestrictPullback (Φ := Φ) (k := k) (hsrc k) (htgt k)
     (fun _ => refRes Φ R hsrc k)).derivNormSupOn K p t
   = metricDerivNormSupOn K p (gSeqExt k t) gIt R`.
- `ofRP_supOn_conv` (the conv-field bridge): given `co : ConvOut` and
  `hmetric : ∀ t ∈ [β,ψ], L.S.family.metric t = co.gInf t` (Brick-6/7
  discharger: `rfl` once `L` is built with metric `gInf`), the
  `FlowLimitData.conv` statement at index `co.φ k` for every compact/order/ε,
  `t ∈ [β,ψ]` (sub-windows `Icc a b ⊆ Icc β ψ` free by inclusion).
- `gInf_zero_eq` (Step 4): from `h0 : 0 ∈ [β,ψ]` and `hconv0` (pointwise time-0
  convergence of the pulled-back source metrics toward `g0`, stated in `Φ`
  terms: `∀ x v w ε>0 ∃k0 ∀k≥k0 ∀ hx : x ∈ Φ.source k,
  |(srcMetric Φ hsrc htgt k 0).inner ⟨x,hx⟩ v w − g0.inner x v w| < ε`),
  conclude `co.gInf 0 = g0`.  Proof: two `Tendsto`s at each `(x,v,w)` —
  T1 from `convPt` on `{x}` + `metricInnerApply_diff_le` (fixed factor
  `finrank · (R-quadratic terms)`), T2 from `grow_cover {x}` + `chi_one`
  (χ = 1 at x eventually) + `gSeqExt_inner_of_mem` + `hconv0` — then
  `tendsto_nhds_unique` + `metric_ext_inner` (+ `ContinuousLinearMap.ext`
  twice: `.inner x` is a bundled `→L` map, NOT a plain function — `funext`
  fails there).
- Helpers: `sourceCompactSet_image_eq` (the plan-named image lemma, extracted
  from `sourceCompactSet_isCompact`), `resSrc` (general-metric `refRes` mirror;
  `refRes_eq_resSrc : refRes Φ R hsrc k = resSrc Φ hsrc k R := rfl`),
  `resSrc_inner` (rfl), `supOn_resSrc_eq` (sup-level restriction invariance for
  three `resSrc` slots, via `@metricDerivNormSupOn_restrictOpen` with the
  change-built instances), `derivNorm_congr_left` (first slot depends only on
  `metricTensorField` — via the rfl-lemma `metricCovDeriv_eq_covDerivOfField`),
  `supOn_congr_left` (sup-set congruence).  The two congr lemmas are
  relocation candidates for `PointedConvergence.lean` (kept here to avoid
  invalidating the deep import chain mid-phase).

## Route notes / gotchas

- **The slot-swap never crosses nested subtypes.**  The pullback slot
  (`ofRestrictPullback.pullbackMetric t` ≡ `srcMetric k t`, rfl by
  `sourceFlow_metric_eq`'s own rfl) is swapped against
  `resSrc (gSeqExt k t)` POINTWISE over `K` via: restrict both triples to
  `O := ⟨val ⁻¹' W, _⟩ : Opens (SourceDomain Φ k)` (`W` = the `chi_one` open,
  `K ⊆ grow k ⊆ W`) with `metricDerivNorm_restrictOpen` (ambient =
  `SourceDomain`), swap with `derivNorm_congr_left` (the metrics agree on ALL
  of `O` since χ ≡ 1 there: `metricTensorField` ext by `DFunLike.ext` +
  `ContinuousMultilinearMap.ext` + `gSeqExt_inner_of_mem` + subtype eta), and
  come back.  Then `supOn_congr_left` + `supOn_resSrc_eq` +
  `sourceCompactSet_image_eq` land on `L.M`.
- **`ofRP_supOn_def := rfl` WORKS** (one-shot definitional unfolding of
  `derivNormSupOn ∘ ofRestrictPullback` into the three explicit slots,
  through the tactic-built defs incl. `sourceFlow`).  No decomposition needed.
- **No BddAbove fight for the bridge**: `windowGInfAll`'s conclusion is already
  sup-level; the BddAbove pattern is needed only for `convPt` (copied from
  `windowGInfAll_pt`, along MY `φ` so one subsequence serves everything —
  subsequence discipline).
- `.inner` of `SmoothRiemannianMetric` is `→L`-bundled: metric-value equalities
  need `ContinuousLinearMap.ext`, not `funext` (the ONE first-compile error).
- Instance plumbing: the `SourceDomain Φ k` vs `↥(sourceOpen Φ k)` gap handled
  exclusively through `refRes`/`resSrc` (let + `change` + explicit `@`), per
  the Brick-4 lesson.  `respectTransparency` workaround NOT needed (no
  generic-rank `Tensor0SField` arithmetic here — `hmTF` is an ext, not algebra).

## Encoding incident (2026-07-03, IMPORTANT)

`ConvFieldAssembly.lean` (untracked, Brick 4) was found DOUBLE-ENCODED on disk
(UTF-8 read as cp1252, re-saved as UTF-8 **with BOM**) — after this morning's
green build, before this session's first read.  Symptom chain: the BOM breaks
Lake's import-header scan → `setup.json` gets `"importArts": {}` → lean
validates lakefile options against an EMPTY import closure →
`invalid -D parameter, unknown configuration option 'linter.style.emptyLine'`
on every fresh compile.  Repaired byte-reversibly (strip BOM; UTF-8 → cp1252
with C1-control fallback for `𝕜`'s 0x9D byte; result strict-UTF-8, 334 `Φ`,
zero mojibake); `refRes` un-privatized in the same file (Brick-5 reuse, one
word).  **`RicciFromJets.lean` also has a BOM** (another session's claimed
file, no mojibake hits — NOT touched; that session's builds will hit the same
`importArts: {}` error until the BOM is stripped).

## Brick-7 handoff

- Instantiate `rmaps := hL0.symm ▸ mc.maps` per ruling 5b (`cases hL0` FIRST),
  `Φ := pointedCGHMaps_of_atZero X L subseq rmaps`; my statements are for
  GENERAL `Φ` (strictly more general, defeq-instantiable).
- The bridge is at `(Φ, co.φ k)` granularity; the `FlowLimitData.conv` field
  is stated against the re-indexed maps (`mc.compSubseq co.φ co.hφ`) — the
  re-spelling should be rfl-style (each `compSubseq` field reduces
  definitionally; mirror `compSubseq_supOn`).  If not rfl, a small spacetime
  `SourceDomainMetricData.compSubseq` wrapper is the known-shape fix.
- `hconv0`'s discharger: `mc.convergence` (sup-seminorm on compacts of the
  time-0 `MetricSourceData`) ⟹ pointwise inner form via singleton-sup
  (`sSup` of a singleton set) + `metricInnerApply_diff_le` + the atZero/atTime
  field-defeq identification of the time-0 pullbacks with `srcMetric k 0`.
  Noted, not executed (per the plan).
- `hmetric`'s discharger: `rfl` once Brick 6 sets `S.family.metric := gInf`.
- Windows: `[β,ψ]` fixed here; the conv field's `∀ Icc a b ⊆ X.D.carrier`
  quantifier is served by sub-window inclusion when `Icc a b ⊆ [β,ψ]`, else by
  the window-exhaustion diagonal (plan Brick 3 note) at Brick 7.

## Verification

- Targeted build `+…HCGCompactness.ConvFieldMain`: GREEN (first compile: ONE
  error, the `funext`-vs-`ContinuousLinearMap.ext` fix above).
- `#print axioms` on `convOut`, `ofRP_supOn_eq`, `ofRP_supOn_conv`,
  `gInf_zero_eq`: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Normal-form refresh (2026-07-17)

- `ofRP_supOn_eq` remains complete (100%); this repair does not change the
  theorem statement, API, or any HCG endpoint accounting.
- After upstream normal-form changes, the local tensor-field equality no longer
  made progress with the old `simp only` prelude.  It now changes definitionally
  to the two restricted metric inner products and uses the existing explicit
  restriction, `resSrc`, bump-extension, and cutoff rewrites.
- Focused verification passed; the exact module refresh also passed.

## Fixed-window documentation correction (2026-07-17)

The `ConvOut` docstring now states its actual quantifier scope: one subsequence
serves every spatial compact and derivative order on the single parameter
window `[β, ψ]`.  It does not claim one subsequence over all time windows.  This
is documentation-only and leaves the global-window diagonal as the explicit P4
frontier.

The focused check could not reach this documentation-only edit because the
shared build cache currently lacks the unrelated upstream
`TensorNabla.TensorExtension` object file.  The last proof-bearing version of
this module remains checked; no declaration or proof body changed here.

## 2026-07-18 grow-local carried input

`convOut` now carries `hcovTail` at the exact `bf.grow k` granularity used by
the compact-exhaustion and PDE consumers. Focused verification and the exact
module refresh pass; no new geometric input was introduced.
