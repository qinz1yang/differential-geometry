# MetricCovDerivPullback

## 2026-07-13 short-time alignment

`metricDiffCovDerivAt_pullback` was adapted to the merged non-reducible
`Tensor0SSpace` API by evaluating tensor subtraction through the public
`Tensor0SSpace.sub_apply` theorem on both sides.  The statement and the
pullback-naturality argument are unchanged.  Focused verification passed; this
compatibility repair does not change the curvature frontier recorded below.

2026-06-17: started the pullback bridge for the HCG/P4 source-domain
seminorm comparison.  The first target is
`metricCovDeriv_one_pullback_sections`, an order-one metric-covariant-
derivative naturality theorem on smooth section slots.  The proof route uses
`metricCovDeriv_one_eval_smooth_slots`, `directionalDeriv_pullback`, and
`metricCov_pullback`.

Focused verification passed.  The section-slot order-one theorem, its pointwise
slot wrapper, and the all-orders pointwise theorem `metricCovDeriv_pullback`
all elaborate.

The pointwise wrapper uses `ContMDiffSection.exists_eq_at_gen` to extend the
leading direction and the two metric slots to smooth sections, then specializes
`metricCovDeriv_one_pullback_sections`.

The all-orders proof uses pointwise induction: arbitrary slots are first
extended to smooth sections, the leading derivative term is transported by
`extDerivFun_comp_diffeomorph`, and each connection-correction term uses the
induction hypothesis plus `metricCov_pullback`.

The next local step is to turn this pointwise tower naturality theorem into the
source-domain seminorm comparison needed by the P4 compactness layer.

Added the evaluated algebraic bridge
`metricDiffCovDerivAt_pullback`: the difference tower itself transports under
pullback when evaluated on arbitrary slots.  It is a direct specialization of
`metricCovDeriv_pullback` to the two metric towers and is the input the future
`metricDerivNorm` transport lemma needs before invoking tensor-norm invariance.
Verification for this added bridge is pending because the global Lake lock is
currently owned by another build.

Added the HCG-local tensor norm transport lemma
`normSq0S_pullback_eval_of_orthonormal`.  It proves equality of source
`normSq0S` under a pullback metric and target `normSq0S`, assuming an
orthonormal source basis and an evaluated pullback relation for the tensor.  The
proof uses `Diffeomorph.mfderivToContinuousLinearEquiv`, maps the source basis
to the target, rewrites both norms as orthonormal component sums, and matches
the sums term-by-term.  Verification is pending behind the same global Lake
lock.

Added `metricDerivNorm_pullback_of_orthonormal`, the pointwise scalar transport
for `metricDerivNorm` under pullback.  It combines the evaluated
`metricDiffCovDerivAt_pullback` bridge with the tensor norm transport lemma.
The theorem still takes the source orthonormal basis as an explicit input; the
next packaging step is to choose such a basis and lift the equality through
`metricDerivNormSupOn`/source compact sets.  Verification is pending behind the
same global Lake lock.

Added the no-basis pointwise corollary `metricDerivNorm_pullback`, choosing the
source orthonormal basis via the existing `exists_gOrthonormalBasis` producer.
If this verifies, the remaining source-domain bridge is no longer tensor
naturality; it is the `metricDerivNormSupOn` lift over `sourceCompactSet`.
Verification is pending behind the same global Lake lock.

Added `metricDerivNormSupOn_pullback_image`, lifting pointwise pullback
invariance to the raw supremum over a source set `K`, with target set
`Phi '' K`.  This is the natural input for the P4 source-domain convergence
constructor once the image-compact/domain hypotheses are wired.  Verification
is pending behind the same global Lake lock.

Targeted module-build refresh for this new file timed out twice without a Lean
diagnostic, and a later axiom-print pass was blocked by a separate global Lake
build.  So the checked source theorem is in place, but the downstream `.olean`
refresh and all-orders axiom print remain a verification-performance follow-up.

Continuation note: the focused check for the added seminorm transport lemmas is
still blocked by the same active global Lake build.  Process inspection shows
the build is live and advancing through unrelated modules, so this is a shared
verification scheduling blocker rather than a Lean proof error in this file.

2026-06-18 continuation: the earlier lock cleared, but a new active global Lake
build for `ExtendedSolutionRegularity` is holding the lock.  Text-only hygiene
found no `sorry`/`admit` in this file or its two upstream touched files.  The
focused check for the seminorm transport lemmas still has not run.

Second resumed check: the same global build remains active and the Lean worker
set/CPU counters are still moving.  The focused check is still queued behind
shared verification rather than blocked by a known local proof error.

Third resumed check: the same global build is still live; Lean worker CPU
counters increased again.  This satisfies the repeated-tooling-blocker stop
condition for the current goal.  No new Lean diagnostic for this file is
available yet because the focused check still cannot be started safely.

2026-06-21 focused check: the global lock was clear and the check reached the
new seminorm transport section.  The verified part remains the earlier
all-orders `metricCovDeriv_pullback` block.  The current blocker is local
elaboration in `normSq0S_pullback_eval_of_orthonormal`: the proof references an
out-of-scope `infty_ne_zero` helper, then the transported-basis step hits a
coercion/index-validation issue around
`Diffeomorph.mfderivToContinuousLinearEquiv_coe` and an invalid `rw [basis']`.
The downstream `metricDerivNorm_pullback` and
`metricDerivNormSupOn_pullback_image` lemmas are therefore not yet checked.

## 2026-06-29 — P1.3 tower engine DONE; Ricci-`M≃N` is the gating frontier

Whole file now builds green (3638 jobs) — the earlier `normSq0S`/seminorm blockers
above are resolved in the current tree.

NEW (verified):
- `covDerivOfField_succ_eval_smooth_slots` — general single-`covStep` recursion on an
  arbitrary rank-2 base (generalises the private metric-only recursion).
- **`covDerivOfField_pullback`** — the P1.3 engine: general base tower naturality `M≃N`
  (base supplied via `hA0 : A0M y slots = A0N (Φ y)(dΦ slots)`). Faithful mirror of
  `metricCovDeriv_pullback`, base abstracted. This is what `ricCovTower_pullback` needs
  (`ricCovTower g g s = covDerivOfField g (ricciSection (leviCivita g)) s`).

GATING REMAINING = `ricciSection_pullback` (`M≃N`): need
`ricciSection (leviCivita (Φ^*g)) y slots = ricciSection (leviCivita g)(Φ y)(dΦ slots)`,
i.e. **Ricci-tensor naturality for a non-endo diffeomorphism**. Verified bridges:
`ricciSection_apply`; `metricCov = leviCivitaConnectionOfMetric` (defeq, Metric.lean:47);
`metricRicciAt_apply_eq_ricciTensor` (`metricRicciAt g x (vec2 v w) = ricciTensor g x v w`).
MISSING = a curvature pullback at `M≃N` Ricci level. `ricci_tensor_pullback_natural`/
`ricciTensor_pullback_conjugation` are **endo-only** (`M≃M`; core `riemannOp_pullback_pointwise`
+ `Diffeomorph.pushforward` are `M≃M`). But `metricRm04Std_pullback` (PullbackNaturality.lean:479)
IS `M≃N` (0,4) Riemann, proven via `riemannCurvature04At_apply_smooth` + `pushFwdSection`.
Two routes: (1) generalise the endo conjugation chain to `M≃N` (multi-lemma: needs a
`pushFwdSection`-based pushforward + `riemannSec_pullback_pointwise` at `M≃N`); (2) build a
`riemannCurvatureAt` (1,3) `M≃N` pullback mirroring `metricRm04Std_pullback`, then
`ricciFromRm13At` trace naturality. Route 2 reuses the proven `M≃N` smooth-section machinery;
the trace-naturality step is the new content. Then `ricCovTower_pullback` (engine + base) →
MovingShiBoundOn transfer (+ `normSq0S_pullback_eval_of_orthonormal`, already here).

### Update: `ricciSection_eq_ricciTensor` DONE; wall pinned (build green 3705)

NEW verified: `ricciSection_eq_ricciTensor` — `ricciSection (leviCivita g) x (vec2 v w)
= ricciTensor g x v w` (route-independent reduction base; needs import
`Curvature.MetricLeviCivitaReconcile` + `[SigmaCompactSpace M][T2Space M][BoundarylessManifold I M]`).

**All 3 routes for `ricciTensor_pullback` (`M≃N`) converge on ONE missing sub-lemma**:
`riemannOp_pullback_pointwise` at `M≃N` (= `riemannSec_pullback_pointwise` at `M≃N`),
`dΦ(riemannOp (LeviCivita (Φ^*g)) x u v w) = riemannOp (LeviCivita g)(Φx)(dΦu)(dΦv)(dΦw)`.
Route 2's orthonormal-trace summand (`ricciTensor_eq_orthonormal_trace` =
`∑ᵢ g.inner x (riemannOp (LeviCivita g) x Bᵢ v w) Bᵢ`) needs it too — NOT just route 1.
**SMALLEST UNBLOCK = `riemannSec_pullback_pointwise` at `M≃N`**: a dedicated-session
generalisation of the endo-only `Pullback/Conjugation/Riemann.lean` layer (swap
`Diffeomorph.pushforward` (`M≃M`) → `pushFwdSection` (`M≃N`); generalise the
`riemannSec_pullback_pointwise` + `riemannOp_apply_smooth` plumbing). The `M≃N` smooth-section
route is proven viable by `metricRm04Std_pullback`/`covDerivOfField_pullback`, so it is plausible
— but it is a multi-lemma build, not a quick fill. Everything downstream of it
(`ricciSection_pullback` → `ricCovTower_pullback` → MovingShiBoundOn transfer) is mechanical
given the banked engine.

## 2026-07-09: compact-open pullback stability

Added `metricCInf_pullback`, the direct compact-open convergence corollary of
`metricDerivNormSupOn_pullback_image`. Focused verification and the targeted producer build
passed without new `sorry`; this result is independent of the curvature frontier described
above.
