# MetricCompactnessSubseq.lean — notes

Re-indexes the whole MSM135 Theorem 3.9 conclusion record along a further
strictly monotone subsequence. Brick-5 prerequisite of `P4_CONV_PLAN.md`
(after Arzelà–Ascoli extracts `φ`, the `mc` record must follow it before the
limit flow is assembled).

## What is here

- `ExhaustsByOpen.comp_subseq` is imported from its canonical low-level home in
  `PointedConvergence.lean`: an open exhaustion re-indexed along a strictly
  monotone map is still an exhaustion.  Keeping it below both the Riemannian
  and spacetime comparison-map wrappers avoids a later import-layer duplicate.
  The consumer remained focused-green and its exact module refresh passed
  after the move.
- `PointedRiemannianCGMaps.compSubseq` + simp `compSubseq_source`
  (`(Φ.compSubseq φ hφ).source k = Φ.source (φ k)`, rfl).
- `MetricSourceData.compSubseq` + simp `compSubseq_supOn`
  (`derivNormSupOn` unchanged, rfl — name kept inside the 20-letter budget).
- `MetricCGConvergenceData.compSubseq`, `PointedRiemannianCGConverges.compSubseq`.
- Endpoint `MetricCompactnessConclusion.compSubseq` with `subseq := mc.subseq ∘ φ`,
  `limit := mc.limit`, `limit_complete := mc.limit_complete`, plus simp
  rfl-lemmas `compSubseq_subseq`, `compSubseq_limit`.

## Defeq findings (the Brick-5 question)

- `MetricSourceData (Φ.compSubseq φ hφ) k` is NOT defeq to
  `MetricSourceData Φ (φ k)` **as types**: they are applications of the same
  structure constant with syntactically different parameters
  (`subseq ∘ φ`/`Φ.compSubseq φ hφ`/`k` vs `subseq`/`Φ`/`φ k`), and inductive
  applications are defeq only argument-wise. So the naive
  `domain := fun k => mc.convergence.metrics.domain (φ k)` does not typecheck.
- However every **field type** depends on the maps record only through
  `MetricSourceDomain`, `.source`, `.map`, `metricSourceCompactSet`, which all
  reduce (delta of `compSubseq` + projection-of-mk iota + beta) to the
  `Φ`-at-`φ k` spellings. `MetricSourceData.compSubseq` is therefore a pure
  field-by-field re-wrap: all 11 fields accepted as plain `:= D.<field>` with
  no casts, no `show`, no transport lemmas.
- `derivNormSupOn` is preserved definitionally through the re-wrap:
  `compSubseq_supOn` is proved by `rfl`. Consequently the `converges` field is
  just the `MapCPConvOn.comp_subseq` pattern (`MapConvergence.lean:95`):
  extract `k0`, evaluate the original at `φ k ≥ k ≥ k0`, and the old-shaped
  conjunction is accepted against the new-shaped goal by defeq.

## Gotcha

- `source_exhausts := Φ.source_exhausts.comp_subseq hφ` as a plain term failed
  with `failed to synthesize TopologicalSpace L.M`: the lemma's
  instance-implicit is not solved by unification there and `L.topology` is a
  record field, not an instance. Fix = the parent file's own idiom:
  `by letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M :=
  L.charted; exact ...`. All other fields elaborated as plain terms.

## Verification

Passed: focused check green; targeted module build green;
`#print axioms MetricCompactnessConclusion.compSubseq =
[propext, Classical.choice, Quot.sound]` (no `sorryAx`; checked via a
temporary `#print axioms` in a targeted build, then removed and rebuilt green).

## Status in the larger plan

This is the mechanical re-index sub-item of Brick 5 only. Brick 5 itself
(global `gInf`, `gInf 0 = mc.limit.metric` identification, the `conv` field)
remains OPEN and still needs Bricks 3–4 outputs.

## 2026-07-10 D6 original-sequence reindexing

Added the non-monotone reindexing family
`PointedRiemannianCGMaps.ofSubseq`, `MetricSourceData.ofSubseq`,
`MetricCGConvergenceData.ofSubseq`, and
`PointedRiemannianCGConverges.ofSubseq`.  Unlike `compSubseq`, this API starts
with convergence for `X.subseq f` at identity and reinterprets it as convergence
for `X` at `f`; no monotonicity of `f` is needed because the source and target
members are definitionally the same.  D6 combines this with `unrepoint` after
the transported-center equality.

Focused verification and the targeted module refresh passed.

## 2026-07-17 composed sequence-level lift

Added the namespace-local `ofSeqSubseq` family for an arbitrary
`inner : Nat -> Nat`, while preserving the identity-only `ofSubseq` API.
Maps, metric source data, metric convergence data, and pointed convergence on
`X.subseq f` lift definitionally to `X` at `f ∘ inner`.

Added `MetricCompactnessConclusion.ofSeqSubseq`.  Given the necessarily strict
outer index `f`, it lifts a conclusion on `X.subseq f` to one on `X`, with the
subsequence `f ∘ mc.subseq` and the same complete limit.  No new data package
or geometric assumption was introduced.

Focused verification and the targeted module refresh passed after refreshing
the two missing upstream variation modules.
