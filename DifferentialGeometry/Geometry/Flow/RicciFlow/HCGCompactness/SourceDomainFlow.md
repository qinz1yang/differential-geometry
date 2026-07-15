# SourceDomainFlow.lean — Brick 2 of the P4 conv engine

**Goal (Brick 2):** the per-`k` pulled-back flow on `SourceDomain Φ k`. Compose Brick 1
(`solutionOn_restrictOpen`) with P1.4 (`solutionOn_pullback`) to get, for
`X : PointedFlowSeq`, `L : PointedFlowData X.D`, `subseq`, `Φ : PointedCGHMaps X L subseq`, `k`:

```
sourceFlow Φ k hσsrc hσtgt
  := solutionOn_pullback (solutionOn_restrictOpen (X.term (subseq k)).S (targetOpen Φ k))
                          (sourceTargetDiff Φ k)   : SolutionOn (M := SourceDomain Φ k) X.D
```

## Status — DONE (core + one cited-input primitive; verified, axiom-clean)

Targeted `build +…SourceDomainFlow` GREEN (3882 jobs). `#print axioms` for
`sourceFlow`, `isSolutionOn_sourceFlow`, `sourceFlow_metric_eq`,
`metricUniformEquivalentOnWindow_restrictOpen` = `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`). No `sorry` in the file.

### Core deliverables (all sorry-free)
- `sourceFlow Φ k hσsrc hσtgt : SolutionOn (M := SourceDomain Φ k) X.D` — the composition above.
- `isSolutionOn_sourceFlow Φ k hσsrc hσtgt : IsSolutionOn (sourceFlow …)` — via
  `isSolutionOn_pullback (isSolutionOn_restrictOpen (X.term (subseq k)).isSolution (targetOpen Φ k))
   (sourceTargetDiff Φ k)`.
- `sourceFlow_metric_eq … referenceMetric t :
   (sourceFlow …).family.metric t = (ofRestrictPullback … referenceMetric).pullbackMetric t` — closes by
  `rfl`. Both sides are `Diffeomorph.pullbackMetric ((S_k.metric t).restrictOpen (targetOpen Φ k))
  (sourceTargetDiff Φ k)`, so the identity is definitional (identifies the flow with the conv
  field's `g_k` slot).

The two inputs `hσsrc : IsSigmaCompact (Φ.source k)` / `hσtgt : IsSigmaCompact (Φ.target k)` mirror
`ofRestrictPullback` exactly.

### Cited-input transport — metric-equivalence primitive (landed)
- `metricUniformEquivalentOn_restrictOpen` / `metricUniformEquivalentOnWindow_restrictOpen`
  (general `M`, section `RestrictOpenEquiv`): `MetricUniformEquivalentOn(Window)` restricts to an
  open subtype with the SAME constant. Proof is definitional — `MetricUniformEquivalentOn` is an
  inner-product bound, and `restrictOpen_inner` is `rfl`, so `simp only [restrictOpen_inner]` reduces
  the restricted bounds to the originals at `↑x`. This is the "restriction step"; the existing
  `metricUniformEquivalentOnWindow_pullback` (`WindowDataPullback.lean`) composes on top along
  `sourceTargetDiff` to finish the transport in Brick 4.

### Cited-input transport — `MovingShiBoundOn` (DONE — see `MovingShiRestrictOpen.lean`)

**UPDATE: the deferred `ricCovTower_restrictOpen` frontier is CLOSED.** New file
`MovingShiRestrictOpen.lean` (verified, axiom-clean; targeted build green 3880 jobs,
`#print axioms movingShiBoundOn_restrictOpen = [propext, Classical.choice, Quot.sound]`)
lands `covDerivOfField_restrictOpen` → `ricciSection_restrictOpen` → `ricCovTower_restrictOpen`
→ `ricCovTower_normSq0S_restrictOpen` → **`movingShiBoundOn_restrictOpen`**. The grep-confirmed-absent
tower restriction was built as a routine (no-`mfderiv`) analog of `ricCovTower_pullback`; the banked
Rm04/LC/metricCov/normSq0S restriction bricks + `extDerivFun_restrictOpen` were exactly sufficient
(prediction below was accurate — no new curvature-restriction API needed). Composes with
`movingShiBoundOn_pullback` to finish the `sourceFlow` transport. Original analysis retained below.

---

**(historical)** DEFERRED — precise missing frontier:
The `MovingShiBoundOn` transport to `sourceFlow` = restriction step + `movingShiBoundOn_pullback`
(P1.3, `MovingShiPullback.lean`). The **restriction step is a genuine missing API**, not a
hypothesis-wrapper: `MovingShiBoundOn` (`RicBound.lean:141`) is
`√(normSq0S (gSeq i t) x (2+s) (ricCovTower (gSeq i t) (gSeq i t) s x)) ≤ KShi`. Restricting to
an open needs
```
normSq0S (g.restrictOpen U) x (2+s) (ricCovTower (g.restrictOpen U) (g.restrictOpen U) s x)
  = normSq0S g ↑x (2+s) (ricCovTower g g s ↑x)
```
i.e. **`ricCovTower_restrictOpen`** — the restriction naturality of the Ricci-covariant-derivative
tower (`covDerivOfField`/`iterCov`/`ricCovTower`). GREP-CONFIRMED absent: no
`covDerivOfField_restrictOpen`, `ricciSection_restrictOpen`, `iterCov_restrictOpen`, or
`ricCovTower_restrictOpen` anywhere in `DifferentialGeometry/`. The banked restriction bricks
(`OpenSubtypeNaturality`, `RestrictOpenRm04`, `MetricDerivNormRestrict`) cover
Rm04/LC/metricCov/`metricDerivNorm`/`normSq0S` restriction but NOT the cov-derivative tower.

**Smallest unblocking lemma (Brick-1 addendum or Brick-4 concern):**
`ricCovTower_restrictOpen` (analog of `ricCovTower_pullback`, `MovingShiPullback.lean:54`, ~50
lines built from `covDerivOfField_pullback` + `ricciSection_pullback`), then a one-line
`normSq0S_restrictOpen_apply` wrap gives `ricCovTower_normSq0S_restrictOpen`, then a
`movingShiBoundOn_restrictOpen` mirroring `movingShiBoundOn_pullback`. Classification:
**missing-API frontier** (curvature-restriction naturality), not typeclass/coercion. Not attempted
here per the Brick-2 fail-loud rule (the core was green; this is not a Brick-2 obligation).

## letI instance plumbing (the real work) — resolved

Mirrored `ofRestrictPullback`'s `letI` block for `X.term (subseq k)).M` / `SourceDomain` /
`TargetDomain` (Top/Charted/T2/Smooth/SigmaCompact via `sourceDom*`/`targetDom*` + `…SigmaOf hσ`,
`IsManifold I 1/2` via `IsManifold.of_le … (by decide)`, `IsManifold I ((∞)+1)` via
`change IsManifold I ∞ …; infer_instance`). `BoundarylessManifold` on every domain is AUTO from
`[I.Boundaryless]` (Mathlib `BoundarylessManifold.open` / boundaryless-model instance), so it is not
carried or constructed — the key enabler that keeps Brick 2 thin.

### GOTCHAS
1. **`∞` ambiguity.** Do NOT `open scoped ENNReal` here. With `ENNReal` open, `∞` in
   `IsManifold.of_le … (n := ∞)`, `≤ ∞`, and `change IsManifold I ∞ …` becomes ambiguous
   (`ℝ≥0∞` vs `WithTop ℕ∞`). Pin `(n := (∞ : WithTop ℕ∞))` and drop `ENNReal` from `open scoped`
   (match `PointedConvergence`, which does not open it).
2. **Subtype-vs-abbrev instance diamond.** `solutionOn_restrictOpen S (targetOpen Φ k)` needs the
   U-instances at the **`↥(targetOpen Φ k)`** form; a `letI : … (TargetDomain Φ k)` (the abbrev, which
   carries an embedded `letI` topology) does NOT get found for the `↥(targetOpen)` query
   (`failed to synthesize SigmaCompactSpace ↥(targetOpen Φ k)`). Fix: register those instances
   (SigmaCompact/T2/IsManifold 1/(∞+1)) **also** at the literal `↥(targetOpen (I := I) Φ k)` form
   (RHS is the `targetDom*`/`…SigmaOf` term — defeq, so `letI` accepts it). Keep the abbrev-form
   `TargetDomain`/`SourceDomain` instances too, for the `solutionOn_pullback` call along
   `sourceTargetDiff` (whose `M`/`N` ARE the abbrevs).
3. **`IsSolutionOn` return type needs SigmaCompact + T2.** Stating `IsSolutionOn (sourceFlow …)` (and
   `sourceFlow`'s own `SolutionOn` return type) requires `SigmaCompactSpace`/`T2Space (SourceDomain)`
   in the signature `letI` block, because the `ricciNormGrad` field mentions `gradientFun`, which
   demands them. Add `T2Space := sourceDomT2` and `SigmaCompactSpace := sourceDomSigmaOf … hσsrc` to
   the return-type `letI` of `sourceFlow`, `isSolutionOn_sourceFlow`, AND `sourceFlow_metric_eq` — in
   the SAME order (T2 before Smooth, SigmaCompact after Smooth) so the three signatures' `sourceFlow`
   applications share instances.

## Denominator / role in project

Brick 2 of 7 in P4 (final assembly of MSM135 Ch4 Thm 3.10 ⇐ 3.9, `P4_CONV_PLAN.md`). It is a thin
composition brick (the mathematics lives in Bricks 1/P1.3/P1.4). The `sourceFlow`/metric identity
feed the conv field's `g_k` slot (Bricks 4–5); the `MovingShiBoundOn` restriction is the one thing
Brick 2 could not close and is now precisely scoped for a `ricCovTower_restrictOpen` addendum.
Whole HCG compactness project ≈ 25–30% (unchanged by this thin brick; it unblocks the g_k-slot
identification for Bricks 4–5).
