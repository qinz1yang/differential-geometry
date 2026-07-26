# DirectLimitManifold.lean — notes (MSM135 Ch4 Step D, D3 = `lbl408`)

The smooth/manifold structure on the sequential topological direct limit
(`Geometry/Topology/DirectLimit.lean`'s `SeqSystem`/`Lim`, consumed read-only).
Abstract infrastructure, no Step A/B/C imports (promotability acceptance test PASSES:
imports are Mathlib manifold + `DirectLimit` + `FiberBundleT2` + `Metric/Basic` +
`Bundle/ClmSectionSmooth` — general layers only).

## State (2026-07-07, 3rd session): **D3 COMPLETE — D3d metric transport DONE, all of D3a–D3e green**

Full `lake build` green (2738 jobs), zero warnings, axiom-clean
(`limitPointedCoc`, `limitMetric`, `limitMetric_pullback`, `stageInner_congr`,
`contMDiffAt_invIncl` all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

### 2026-07-09 review fill — smooth direct-limit manifold hypotheses

Verdict: accepted; no Lean interface change is needed. The current `SmoothSeqSystem` API already
encodes the clean mathematical hypothesis that each transition is a smooth diffeomorphism onto an
open image: the open topological embedding is inherited from `SeqSystem.isOpenEmb`, `contMDiff_F`
is the smooth forward map, and `contMDiffOn_invFun_F` is the smooth inverse-on-range half. This is
not merely a smooth open embedding.

Ambient assumptions are intentionally split by consumer. The bare smooth direct limit uses one
common model-with-corners `(I, H, E)` through its parameters and stage manifold assumptions.
Hausdorff and sigma-compact limits are recovered from stage hypotheses by
`instT2SpaceLim`/`instSigmaCompactSpaceLim`. Finite-dimensionality is attached where the
Riemannian/Ricci-flow metric transport and pointed-limit constructions use it. Boundaryless and
nonzero-finrank assumptions remain on the metric-distance completeness consumer in
`C4/StepDLimit.lean`, not on the atlas construction. Second-countability is still a deferred
topological glue result unless a later endpoint needs it explicitly.

### 2026-07-09 review fill — chart compatibility versus representative independence

Verdict: accepted; the construction is right, but the durable wording should not say that charts
are literally representative-independent. `limChart k a = (inclHomeo k).symm ≫ chartAt H a` is one
admissible chart for each representative `⟨k, a⟩`, with source
`incl k '' (chartAt H a).source`. The `ChartedSpace.chartAt` field chooses one representative by
`Classical.choose`; the atlas is valid because all representative charts are in the atlas and their
overlap transitions are smooth.

The implemented reduction is the expected one. The factor transition
`transitionHomeo k ℓ = (inclHomeo k) ≫ (inclHomeo ℓ).symm` is `(incl ℓ)⁻¹ ∘ incl k` on the overlap.
In `transitionHomeo_contMDiffOn`, with `m = max k ℓ`, it is pointwise
`Function.invFun (F_{ℓ≤m}) (F_{k≤m} x)` on the subset where `F_{k≤m} x ∈ range (F_{ℓ≤m})`.
Smoothness then uses `contMDiff_F hkm`, `contMDiffOn_invFun_F hℓm`, and ordinary smooth stage-chart
compatibility through `limChart_symm_trans` and `modelSpace_contDiffOn`.

### 2026-07-09 review fill — metric overlap gluing uses the real tangent cocycle

Verdict: accepted; no Lean interface change is needed. `MetricCocycle` is already the correct
Riemannian cocycle, not a set-level or distance-level compatibility statement. Its definition says
that for every `h : k ≤ ℓ`, `a : A k`, and tangent vectors `v w`, the later metric evaluated on the
actual differential images
`mfderiv I I (S.toSeqSystem.F h) a v` and `mfderiv I I (S.toSeqSystem.F h) a w` equals the earlier
metric at `a`.

The overlap well-definedness is implemented by `stageInner_mono` and `stageInner_congr`. Locally
`stageInner g k z` pulls `g k` back along the smooth local inverse
`Function.invFun (incl k)`. On an overlap of two stage ranges, both representatives are pushed to
`m = max k ℓ`; the derivative factorization is proved from
`F_{k≤m} ∘ Function.invFun (incl k) =ᶠ Function.invFun (incl m)`, and the tangent-level cocycle
identifies both pullbacks with the `g m` pullback. This is exactly the needed smooth tensor-field
gluing argument; mere distance or ball compatibility would not prove `limitMetric` or
`limitMetric_pullback`.

### 2026-07-09 review fill — inverse smoothness is necessary, not cosmetic

Verdict: accepted; no Lean interface change is needed because `SmoothSeqSystem` already keeps the
necessary inverse-smoothness hypothesis. The counterexample is decisive: take two real-line stages
and `F_{0,1}(x) = x^3`. This map is injective, a homeomorphism onto its image, open with image all
of `ℝ`, and smooth. It is therefore a smooth open topological embedding, but the inverse cube-root
map is not differentiable at `0`.

So `IsOpenEmbedding (F h)` plus `ContMDiff (F h)` would not make the direct-limit atlas smooth:
the stage-1-to-stage-0 transition is cube root. The field `contMDiffOn_invFun_F` is therefore the
minimal honest repair unless the whole transition package is replaced by partial diffeomorphisms or
local diffeomorphisms onto open images.

### 2026-07-09 review fill — `Function.invFun` is range-scoped

Review 10 accepted. `Function.invFun` is acceptable in the current code only because every smoothness
or evaluation theorem keeps the point inside the relevant range. For transitions this is
`contMDiffOn_invFun_F` on `range (F h)`. For stage inclusions this is `contMDiffAt_invIncl k hz`,
where `hz : z ∈ range (incl k)`, and the packaged range-aware API is `inclPartialDiffeo`.

Do not add any theorem requiring global smoothness, continuity, or definitional behavior of
`Function.invFun` away from the range. If this becomes noisy later, the intended refactor is a
range-explicit partial diffeomorphism/local-diffeomorphism package, not a stronger global inverse
claim.

### 2026-07-09 review fill — atlas, not quotient-recursive canonical charts

Review 11 accepted; this is already the implemented route. The atlas is indexed by all
stage-supplied charts `limChart k a`; `ChartedSpace.chartAt` chooses one representative only to
inhabit the typeclass field. The proof burden is `mem_chart_source`, `limChart_mem_atlas`, and
smooth transitions (`limChart_symm_trans` plus `transitionHomeo_contMDiffOn`), not equality of
charts under quotient representative change.

Do not try to redefine the limit chart by quotient-recursive representative independence. That is
the wrong formalization problem and would duplicate the atlas compatibility work in a harder form.

### 2026-07-09 review fill — metric gluing uses local formulas, not sheaf machinery

Review 14 accepted; the current `limitMetric` route is the intended Lean route. It defines the
inner product pointwise using `stageInner g (rep z).1 z`, proves independence on overlaps by
`stageInner_congr`, and proves smoothness locally on a stage range using the local inverse
`Function.invFun (incl k)` plus the test-section engine.

This avoids depending on a general smooth tensor-field sheaf/gluing API. If such an API appears
later it may shorten the proof, but it should not replace the current local-formula route unless it
can express the same range-restricted inverse and cocycle data without adding a new frontier.

### 2026-07-09 review fill — hidden assumptions are consumer-owned

The review's Hamilton/MSM135 hidden-assumption list matches the current layering. The bare
topological direct limit owns only the open-embedding direct-system and transferred topological
properties. The bare smooth direct limit owns the common model-with-corners, stage smoothness,
smooth transitions, inverse-on-range smoothness, `T2`/sigma-compact transfer, and tangent-bundle
`T2` transfer.

Finite-dimensionality, `CompleteSpace E`, basepoints, metric cocycles, connected/preconnected
stage hypotheses, boundaryless/nonzero-finrank assumptions, stage-ball compactness, and metric
exhaustion/properness are not hidden in `SmoothSeqSystem`. They belong to the pointed and
completeness consumers in `C4/StepDLimit.lean` (`limitPointed`, `limitPointedCoc`,
`limitCGMaps`, `limitProper`, `limitComplete`) and ultimately to D4–D6/Hamilton compactness
inputs. Completeness of the limit metric is a separate theorem, not a consequence of forming the
direct limit.

### D3d — `SmoothSeqSystem.limitMetric` (the `g∞` construction), landed this session
Given `g : ∀ k, SmoothRiemannianMetric I (A k)` and the isometry cocycle
`MetricCocycle g` (`(F h)^* g ℓ = g k` pointwise on inner products — D2c's conclusion shape;
honest-input three-part note in its docstring), `limitMetric g hg : SmoothRiemannianMetric I S.Lim`
with the defining pullback property `limitMetric_pullback : (incl k)^* g∞ = g k`.

The 2026-07-09 consumer pass added two readouts. `MetricCocycle.ofSucc` extends adjacent metric
compatibility to every transition by induction, `map_map`, and the chain rule.
`limitMetric_of_mem` states the local formula on `range (incl k)` directly: the glued metric is the
pullback of `g k` along `Function.invFun (incl k)`. Both focused verification and the targeted
module build passed.

Route (all four planned ideas worked):
- **No derivative inverses anywhere**: the fiber form is the *pullback along the smooth local
  inverse* `φ_k := Function.invFun (incl k)` — `stageInner g k z := (precomp (mfderiv φ_k z)) ∘
  ((g k).inner (φ_k z)).comp (mfderiv φ_k z)`, verbatim the `Diffeomorph.pullbackInner` shape with
  `Φ` replaced by `φ_k`.  `contMDiffAt_invIncl` proves `φ_k` is `C^∞` on the open range (it agrees
  there with `(chartAt H a).symm ∘ limChart k a`).
- **Stage-independence** (`stageInner_mono`/`stageInner_congr`): the FORWARD factorization
  `F_{k≤m} ∘ φ_k =ᶠ φ_m` near the range of `incl k` (no `invFun F` needed!), then
  `EventuallyEq.mfderiv_eq` + `mfderiv_comp` + the cocycle at the point `φ_k z`.  Base-point
  mismatches (`φ_k (incl k a) = a` etc., propositional because `invFun` is choice-based) are
  crossed by two subst-based helpers `inner_base_eq`/`mfd_base_eq` stated at ascribed type
  `E →L[ℝ] E →L[ℝ] ℝ` (TangentSpace ≡ E definitionally) — no dependent-`rw` fights.
- **`symm`/`pos`/`isVonNBounded`** at the chosen representative stage (`rep z`), via the generic
  chain-rule helper `mfd_comp_id` (`g' ∘ f =ᶠ id near x ⟹ mfderiv g' ∘ mfderiv f = id`):
  `pos` from injectivity of `mfderiv φ_k` (left-composed to id by `mfderiv (incl k)`),
  bounded-set via image under `mfderiv (incl k)` + `IsVonNBounded.image`.
- **`contMDiff` (the flagged wall — dissolved by the test-section engine)**:
  `cotangentCov_clmSection_smooth_aux` (PUBLIC, `Bundle/ClmSectionSmooth.lean`, works on any
  σ-compact T2 manifold — Lim qualifies) applied twice reduces the metric-section smoothness to
  scalar smoothness against arbitrary smooth tangent sections `Y W`; at each `z₀` localize to the
  stage `k₀ := (rep z₀).1` (`stageInner_congr` on the open range — this is where the cocycle
  enters smoothness), then the stage scalar is `clm_bundle_apply₂` (At-version) of
  `(g k₀).contMDiff ∘ φ` against `z ↦ ⟨φ z, mfderiv φ z (Y z)⟩`, the latter smooth via
  `ContMDiffOn.contMDiffOn_tangentMapWithin` (with `IsOpen.uniqueMDiffOn`, `le_rfl` for `∞+1 ≤ ∞`)
  + `mfderivWithin_of_isOpen`; extract the scalar by `contMDiffAt_totalSpace` and rebundle by
  `Bundle.contMDiffAt_section` (trivial-bundle readout is the bare scalar, `rfl`).

### Lean lessons (this session)
- `TotalSpace.mk'` cannot infer the bundle family from a dependent fiber value — annotate
  `(E := fun b : A k₀ => …)` at every `mk'` in `have`-statements.
- `ContMDiffAt.comp` produces the `∘`-form; restate via `have h := …; exact h` to defeq-cast to
  the λ-form the next combinator expects.
- `Bundle.contMDiffAt_section` is in namespace `Bundle` (file opens `Set Topology` only).
- `∞ + 1 ≤ ∞` in `WithTop ℕ∞` is `le_rfl` (defeq `⊤ + 1 = ⊤` inside the coercion).

## State (2026-07-07, 2nd session): D3a + D3b + **D3c COMPLETE** + D3e assembly GREEN, axiom-clean

## State (2026-07-07): D3a + D3b + **D3c COMPLETE** + D3e assembly GREEN, axiom-clean

`#print axioms` on all capstones (`instIsManifoldLim`, `instChartedSpaceLim`,
`transitionHomeo_contMDiffOn`, `FiberBundle.t2Space_totalSpace`, `instT2SpaceTangentBundleLim`,
`limitPointed`) = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  Full `lake build` green.

**Update 2026-07-07 (2nd session):**
- **D3c COMPLETED** — `T2Space (TangentBundle I S.Lim)`.  The missing producer was a general
  topology fact: NEW `Geometry/Topology/FiberBundleT2.lean` `FiberBundle.t2Space_totalSpace`
  (`[T2Space B] [T2Space F] [FiberBundle F E] ⟹ T2Space (TotalSpace F E)`; ~35 lines: same base
  point → separate inside a trivialization's source (open embedding into the `T2` product `B × F`),
  different base point → pull back separating base opens).  Corollary instance
  `SmoothSeqSystem.instT2SpaceTangentBundleLim` fires it automatically (`IsManifold I 1` lowered
  from `∞` for the tangent `FiberBundle` structure; fibre `E` normed hence `T2`).
- **`SmoothSeqSystem.contMDiff_incl`** — the stage inclusion `incl k : A k → S.Lim` is `C^∞` (in the
  atlas it reads as the identity: `incl k =ᶠ (limChart k a).symm ∘ chartAt a`, both `C^∞` via the
  maximal atlas).  A D3d/D4 prerequisite.
- **D3e — `C4/StepDLimit.lean` `limitPointed`** — assembles the `PointedRiemannianManifold` bundle
  (carrier `S.Lim`, basepoint `incl 0 O₀`, metric `ginf` supplied as input).  ALL structure fields
  (`charted`/`smooth`/`sigmaCompact`/`t2`/`t2TangentBundle`) auto-synthesize from the D3a–D3c
  instances; sorry-free, conditional only on the `ginf` input (= the D3d producer).

## State (2026-07-07, 1st session): D3a + D3b + D3c-part GREEN, axiom-clean, real `lake build`

`#print axioms` on `instIsManifoldLim`, `instChartedSpaceLim`, `transitionHomeo_contMDiffOn`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Full `lake build` green (2329 jobs).

### DONE
- **D3a — `SeqSystem.instChartedSpaceLim : ChartedSpace H S.Lim`.** Charts `limChart k a :=
  (inclHomeo k).symm ≫ chartAt H a`, where `inclHomeo k := (incl_isOpenEmb k).toOpenPartialHomeomorph
  (incl k) : OpenPartialHomeomorph (A k) Lim`. `chartAt z := limChart (rep z).1 (rep z).2` with
  `rep z` a `Classical.choose` representative (`exists_sigma_incl`). Supporting: `inclHomeo_{apply,
  source,target,symm_apply}`, `mem_limChart_source`, `mem_atlas_iff`, `chartAt_lim`.
- **`SmoothSeqSystem I A` structure** (extends `SeqSystem`): factors are `C^∞` manifolds; fields
  `contMDiff_F` (each `F h` is `ContMDiff`) + `contMDiffOn_invFun_F` (its inverse `Function.invFun
  (F h)` is `ContMDiffOn` on `range (F h)`) — i.e. the `F h` are `C^∞` diffeos onto open images
  (the book's `Ψ_k`). Needs `[∀ k, Nonempty (A k)]` (honest: the balls contain their centres).
- **D3b crux `transitionHomeo_contMDiffOn` (`lbl409`).** The factor transition
  `transitionHomeo k ℓ := (inclHomeo k) ≫ (inclHomeo ℓ).symm : OpenPartialHomeomorph (A k) (A ℓ)`
  is `ContMDiffOn` on its source. On the overlap it equals `Function.invFun (F_{ℓ≤m}) ∘ F_{k≤m}`
  (`m = max k ℓ`), proved via `incl`-injectivity at stage `m` + `incl_comp` + `leftInverse_invFun`,
  then `ContMDiffOn.comp` of the two smooth pieces. This is the mathematically meaningful content.
- **`limChart_symm_trans`**: the Lim-chart transition `(limChart k a)⁻¹ ≫ (limChart ℓ b)` equals
  `(chartAt a)⁻¹ ≫ (transitionHomeo k ℓ) ≫ (chartAt b)` ON THE NOSE (`trans` associative,
  `trans_symm_eq_symm_trans_symm` is `rfl`, `symm_symm`).
- **`modelSpace_contDiffOn`** (model-space bridge, `[Nonempty H]`): `ContMDiffOn I I ∞ (f : H → H) s`
  ⟹ `ContDiffOn ℝ ∞ (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)` — the exact `contDiffPregroupoid`
  form `isManifold_of_contDiffOn` consumes. Route: `contMDiffOn_iff_of_subset_source'` (single model
  chart, `extChartAt I x₀ = I`) + `ModelWithCorners.image_eq` (`I '' s = I.symm ⁻¹' s ∩ range I`) +
  `extChartAt_coe`/`extChartAt_coe_symm`/`chartAt_self_eq`.
- **D3b — `SmoothSeqSystem.instIsManifoldLim : IsManifold I ∞ S.Lim`.** `isManifold_of_contDiffOn`;
  each transition → `limChart_symm_trans` → `modelSpace_contDiffOn` of `ContMDiffOn T'` (compose
  `contMDiffOn_chart_symm` + `transitionHomeo_contMDiffOn` + `contMDiffOn_chart` via `ContMDiffOn.comp'`,
  domain matched by `trans_source`). `Nonempty H` from `Nonempty (A 0)` + a chart.
- **D3c (part) — `instSigmaCompactSpaceLim`, `instT2SpaceLim`** (thin wrappers of engine
  `SeqSystem.sigmaCompact`/`t2Space`, need `[∀ k, SigmaCompactSpace/T2Space (A k)]`).

### (RESOLVED 2026-07-07 3rd session) D3d metric transport — see the DONE entry at the top
The bridge described here was built (as the *pullback along the smooth local inverse*, which avoids
every derivative inverse): `MetricCocycle` + `stageInner` + `limitMetric` + `limitMetric_pullback`.
D3e consumes it via `C4/StepDLimit.lean` `limitPointedCoc`.  D3 is COMPLETE; the remaining Step D
lanes are D1/D2/D4/D5/D6 (see `STEPD_PLAN.md`).

## Lessons
- Charts hide `H` behind `.source`: statements like `x ∈ (limChart k a).source` cannot infer `H`
  (metavar → stuck instance). Fix: `(limChart (H := H) k a)` or an `atlas H _`-mentioning goal.
- `set` over-rewrites: `rw [← hz]` where `hz : incl (rep z)… = z` also hits the `rep z` inside
  `chartAt z`. Rewrite the HYPOTHESIS (`rwa [hz] at hmem`) instead.
- `SmoothSeqSystem` needs `contMDiffOn_invFun_F` — a `C^∞` open embedding does NOT have a `C^∞`
  inverse automatically (`x ↦ x³`), so requiring smooth-onto-open-image is honest, not gratuitous.
- Review 5 confirmed the same point at the direct-limit level: the atlas needs the diffeomorphism
  onto-open-image data, while finite-dimensional, T2/sigma-compact, and boundaryless hypotheses
  should stay on the downstream Ricci/Riemannian consumers that require them.
- Review 6 clarified the correct chart story: each representative supplies an admissible chart, and
  the proof obligation is smooth overlap compatibility via the common-stage transition
  `Function.invFun (F_{ℓ≤m}) ∘ F_{k≤m}`. Do not describe this as literal representative
  independence of a canonical chart.
- Review 7 confirmed the metric gluing route: `MetricCocycle` must and does use the actual
  differentials of the transition maps on tangent vectors. Distance-level or set-level
  compatibility is not enough for smooth Riemannian tensor gluing.
- Review 8 records the hard counterexample for inverse smoothness: `ℝ --x^3--> ℝ` is a smooth open
  topological embedding, but the inverse cube-root transition is not `C^1` at `0`. Do not weaken
  `SmoothSeqSystem` to only `IsOpenEmbedding + ContMDiff`.
- Review 10 records that every `Function.invFun` theorem must be range-scoped; prefer
  `inclPartialDiffeo` or a future range-explicit transition package when the inverse domain matters.
- Review 11 records the chart route: all representative charts live in the atlas, and smooth
  transition compatibility is the proof obligation. Do not attempt quotient-recursive canonical
  chart independence.
- Review 14 records the metric route: use pointwise `stageInner` plus local formulas on stage
  ranges; do not wait for or invent a broad smooth-tensor sheaf gluing API.
- The Hamilton/MSM135 hidden assumptions are intentionally downstream-owned: finite-dimensionality,
  boundaryless/nonzero-finrank, basepoints, connectedness, metric exhaustion, stage-ball compactness,
  and completeness live in `C4/StepDLimit.lean` consumers, not in the bare direct-limit structure.

## 2026-07-09 Step-D adjacent-map constructor

`SmoothSeqSystem.ofSucc` is verified. It consumes adjacent smooth open embeddings plus
`ContMDiffOn` for each `Function.invFun` on its range, and uses `SeqSystem.ofSucc` to form every
later-stage transition. `succMap_inv_mdiff` proves that the inverse of each finite composite is
smooth on its actual range; no behavior of `Function.invFun` outside the range is used. This is
the constructor consumed by `C4/StepDLimitMetrics.lean` for the open-ball stage system.
