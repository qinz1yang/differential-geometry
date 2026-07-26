# MSM135 Chapter 4 (Theorem 3.9 / `metricCompactness`) — backlog

**Endpoint (RULING 2026-07-05, user):** the Chapter 4 target is the **conditional**
Theorem 3.9 `MetricCompactnessInputs.metricCompactness`
(`C4/MetricCompactnessEndpoint.lean`) — same conclusion, with the book-external
theorems bundled as the explicit input structure `MetricCompactnessInputs`
(A0 CGT decay, `lbl387` packing, A0' multiplicity, `lbl395` normal-coordinate
bounds, `lbl418` exp⁻¹ derivatives, distance realization, scale compatibilities)
plus per-member connectedness.  The **unconditional** `metricCompactness`
(`MetricCompactness.lean`, the historical lone `sorry`) is NOT dischargeable by
Steps A→D — its extra content is exactly those citations, unprovable in-tree
without a Riemannian volume/comparison layer — and stays `sorry` as the external
frontier.  Report Theorem 3.9 progress against the conditional endpoint only.
The per-field mathematical audit lives in `MetricCompactnessInputs.lean` and
`../PROJECT_MAP.md`.

**Endpoint capstone (2026-07-17):** the conditional endpoint is **100% checked**.
`MetricCompactBase.exists_b1_raw` produces a concrete `StepB1RawInput` with all
5/5 fields verified; `compactness_of_b1` performs the checked Step-D assembly;
and `MetricCompactnessConclusion.ofSeqSubseq` transports the nested-subsequence
conclusion back to the original sequence.  The focused endpoint check and exact
targeted refresh are green, with no local `sorry` or `admit`.  The selected
B/C-to-B1 producer route is therefore 100%.  This does not state or prove the
separately named textbook B1 theorem (still 0%), does not complete the historical
full Step-C arbitrary recurrence, and does not discharge the unconditional
Theorem 3.9 external inputs.

**Current interface repair (2026-07-09):** the former P-only
`stepB1_approxIso` statement was false and has been deleted.  The checked
assembly is now `stepB1_of_raw`, consuming `StepB1RawInput`; Step D exposes the
same missing producer explicitly through `directed_of_b1`.  Likewise, the
former all-order `cmChartDerivLe` endpoint was deleted: only
`cmChartDerivLe2` (`j ≤ 2`) is checked, while the arbitrary-order recurrence is
unstated and 0%.  Older occurrences of those two deleted theorem names below
describe historical planning only; they are not live APIs or proved gates.

**Historical B/C producer snapshot (2026-07-11; superseded by the 2026-07-17
capstone above):** the parallel metric-origin and
transition branches have been joined on one common refinement.  Intrinsic
finite-hat atoms, support/coverage, normalized weights, and their common
`C^infty` subsequential limit are packaged by
`StepCAtomPackage.existsAtomWeightLim` and are checked.  The pinned IFT branch,
ambient root-extension gluing/agreement (`existsRootExtension` /
`existsCmExtension`), and the generic conditional center-root producer
`centerReadout_zero` are also checked.  Its concrete finite-hat instantiation
still requires reverse-chart and named-radius smallness needed to instantiate
the checked pointwise differentiability/agreement producers.
`exists_diagInvDom_inf` and `exists_readoutDom_inf` now expose one fixed open
off-diagonal inverse-exp/readout domain carrying all orders simultaneously,
using the existing Route-A `diagExpInv` branch.  `exists_readoutEBall` extracts
a positive finite radius for each fixed base, and `centerPairs_lt_le` closes the
local cage-containment ledger.  The endpoint bundle contains the required
sequence-relative floor as `MetricCompactnessInputs.normalRadius :
NormalRadiusProfile ...`, including `floor_le_radius` and `floor_le_exp`.
The explicit selected-branch route is now checked through
`DiagInvBranch`, `DiagInvReadout`, `stdBranch`, the branch-parametric center
  consumers, `normalDiagAtFull`, and `IsNormalDiag.toBranch`; the quantitative branch
  has forward and inverse `C^infinity` regularity on its full named domains, and
  `IsNormalDiag.full_transport` proves its exact source, target, and inverse
  formulas.  `exists_phase_scale` and `normalBrAccept` choose global positive coefficients
  `aq`, `aδ`, and `aρ`, with `q`, `δ`, the whole quantitative target ball, and
  the common `aρ * mu R` branch domain selected before the sequence index and
  center.  `normalBrScale` preserves the established consumer interface, while
  `normalBrHat` supplies the finite-hat scale inequality.  The fourth-route
minimizing tangent has removed the unquantified `expMapIntrinsic = expMap`
radius from the B1 readout path.  `NormalBranchCage` now chooses one minimizing
coefficient before `D`, specializes the full branch at each slotwise
`rInf + 1` cage, proves the common active-radius half-margin, handles dead
slots, and derives the actual finite-hat selected-branch equation.  The
canonical sigma field and its `r₁` bound are also produced.  The
selected-branch Hessian/Neumann, strict-IFT, and strict-distance route is now
retained through the global source capstone.  Coherent chartwise convergence
data and compact cores covering every frozen source ball are retained on that
same master subsequence.  Dedicated Step-B/B1 machinery is about 95%; the
`StepB1RawInput` producer and textbook B1 theorem remain 0%.

**Historical 2026-07-15 global stage-map/analytic ruling (its open producer
items were discharged on 2026-07-17):** see
`B1_STAGE_MAP_RULING.md` and the answered `B1_MOVING_ROOT_CONSULT.md`.
`stageTarget`, `HasUniqueStageCenter`, and `stageComparisonMap` now give the
chart-independent finite-stage definition, while zero-weight energy congruence
identifies local filled branches with its unique minimizer.  The source-cover
producer now also returns fixed compact nested cores whose strict inner images
cover the source ball, and the producer/capstone chain retains those cores on
the same master subsequence.  The fixed two-bump Route-A filler, old-`InterSlot`
finite totalization, actual stage configuration, and its arbitrary-reindexing
`C^infinity` convergence are now checked in `StepCStageFill`.  The remaining
route is now split at native layers.  Generic map convergence has been moved to
`Analysis/Calculus`; the proof-independent metric spray and
`normalGeodesicSpray_conv` are checked.  The exact
`MapCInfConvOnCompacts.ode_solutionAt` statement is typechecked in
`Analysis/ODE`, but its all-order stability proof is the first honest analytic
frontier and remains 0% with one `sorry`.  Forward normal-phase endpoints,
compact moving roots, selected inverse convergence, and `invVelSum` center
roots follow in that order.  The all-pairs chart-tail theorem,
`StepB1RawInput` producer, and textbook B1 theorem remain 0%; rounded machinery
estimates stay 95% / 87% / 57% for Step-B/B1 / Chapter 4 / whole HCG.

**Rule:** one Lean declaration per book result, in book order. Honest-input fields
ONLY where the book itself cites an external theorem (`lbl384`, the Rauch comparison
in `lbl387`, the Hessian comparison `lbl413`) — with one declared exception: the
"`D` large enough" **construction-stage choices**, which must be discharged at
D6 rather than survive to the endpoint.  The former all-index
`Item3RadiusInput` and `Item3GpScaleInput` exceptions are retired from the
canonical route: the profile now proves packing-local `Item3RadiusTail` and
`Item3GpScaleTail` after `D`, `pb`, and `r` are fixed.  The canonical
`SigmaScaleField`, physical finite-hat cage/readout, selected-branch
Hessian/Neumann, and full-convexity producers are checked.  The remaining
construction-stage work is the all-pairs convergence and quantitative B1
assembly for the now-defined global stage map.
**2026-07-14 correction:** the relative `kappa * mu(distance)` lower profile is
already encoded separately by the endpoint's `normalRadius` field and consumed by
the checked `NormalRadiusProfile.floor_le_*`, `exists_phase_scale`,
`normalBrScale`, and `mul_lambda_lt_*` API.  Branch-scale and
fixed-trivialization `readDom` production are closed.  The live discharge
problem is the concrete stage-weighted B1 raw assembly, not another endpoint
radius record.  The finite-slot
`g_p`, exp-diffeomorphism-radius, canonical sigma/`r₁`, and physical-cage
ledgers are checked from one pre-packing divisor.
Everything the book proves, we prove. Build via
`& .\scripts\lake-locked.ps1 build +<Module>`; no
`sorry`/admissions; `#print axioms`-clean.

Legend: `[x]` done & verified · `[~]` honest-input (book-external) · `[ ]` todo.
§-numbers mirror the BOOK's internal section order (§2 = Step A, §3 = Step B,
§6 = Step C, §4 = Step D — the book proves Step C's tools in its §6), so they are
intentionally non-monotone in this file.

> **Maintenance note (2026-06-11):** done items are collapsed to a one-line
> `→ file:decl` pointer; full build history lives in each file's same-name `.md`.
> The old `ApproximateIsometry.lean` monolith was deleted — its green interface is
> in `ApproxIsometryDefs.lean`, its broken proofs in `ApproximateIsometryArchive.md`.
>
> **Relocation (2026-06-17):** the 21 Ch4-exclusive modules now live in
> `…/HCGCompactness/C4/` (git renames; targeted-build-only, as before — the umbrella
> imports none of them). **Stay in the parent `HCGCompactness/`** (Ch4-content but
> shared with the active Ch3 chain, so not moved): `MapConvergence`, `ArzelaAscoli`,
> `Lemma45Engine`(+`CovariantAbstract`/`SumLemmas`/`Constants`), `MetricCompactness`,
> plus the foundational layer (`Basic`, `PointedRiemannian`, `PointedConvergence`,
> `BoundedGeometry`, `InjectivityRadius`) and the Ch3 P-track. `C4/` is therefore not
> self-contained: it imports up to the parent for those shared engines.
>
> **Dependency-graph fact (2026-06-17):** item-3a is **UNCONDITIONAL** — proved via
> normal coordinates (`Comparison/ExpBallDiffeo.lean:exp_isLocalDiffeomorphOn_ball` →
> `exists_expBall_diffeo_of_lt`), NOT via the Jacobi/Grönwall route. So the
> nonsingularity tower (`Comparison/Variation/CovariantGronwall.lean:covGronwall_ne_zero`,
> `Comparison/ExpNonsingular.lean`, `Metric/InnerExpansion.lean`, and the ∞→finite-order
> parallel-transport refactor in `Comparison/Variation/ParallelTransport.lean`) is **OFF
> the Theorem 3.9 critical path** — reusable global-geometry analysis (no-conjugate-points
> Grönwall), the natural native route to Step B `lbl395` metric bounds, NOT an item-3
> dependency. Do not re-couple it to item-3.

---

## DONE — where to find it

**Approx-isometry interface (F1-def, F1-metric).** `ApproxIsometryDefs.lean`:
`PullbackMetricTensorData`, `PreApproxIsometryData`, `BookApproxIsometryData`,
`IsApproxIsometryOn`, `IsTwoSidedApproxIsometryOn`, `metricCovDerivNormWith`, the
`ConnDiff*` realization vocabulary, and the dimension constants
(`connDiffOneConst`/`connDiffTwoConst`/`connDiffEpsConst_two`/`_three`/`connDiffCoeff`).

**F1 norm comparison (Cor *Norms of tensors*).** Superseded by the `(0,s)` metric-
equivalence factor: `Comparison.lean:sqrt_normSq0S_le_of_metric_equiv` (the book's
`(1+ε)^{(r+q₂)/2}` = `√(C^s)`) over `normSq0S_le_of_metric_equiv`. The old broken
`bookNormRS_compare` (needed the never-ported `normRS`) is archived.

**F2 — Prop *Distances*.** `Distances.lean`: `pathComp_tangent`, `dist_le_tangent`,
`image_ball_tangent`, `edist_le_of_path_comp`, `lipschitz_sqrt_of_dist_le`,
`image_ball_subset_of_lipschitz_sqrt`, and the book-facing
`speed_le_of_c0` / `data_image_ball` producers consumed by Step D.

**F3 — Lemma *Norms of cov. derivs, I*** (`|∇_g^r T|_g ≤ |∇_h^r T|_g + εCΣ_{k<r}|∇_h^k T|_g`).
`Lemma45Engine.lean:lemma45_F3` (component-`compL2` form, sorry-free). Engine:
`hkoszul_of_leviCivita`, `claim1_eps_koszul`, `lemma45_component_bdd` (same file);
`Lemma45CovariantAbstract.lean:lemma45DoubleBdd`; `KoszulDifference.lean:koszul_difference`;
consumes the Claim-1 machinery in `AkMFold.lean` (`claim1`, `P(m)`).

**Good-frame / tower bridge** (the gate for F3→F4's intrinsic lift AND ric_bound R4).
`RicBoundGoodFrame.lean`: `exists_trivONBasis` (smooth gRef-ON-at-a-point frame),
`exists_goodFrame_compBound`, **`compL2_tower_le`** (bounded-Gram `compL2 ↔ √normSq0S`
inequality over a small domain), `gramInv_near_id`;
`KroneckerQuadForm.lean`: `quad_lb_of_near_id`, `quadForm_id_le_pow`,
`sum_posSemidef_mul_posSemidef_nonneg`. (Parallel-session, sorry-free, committed.)

**F5-const / F5 (C⁰) / F6 (scalar).** `Lemma45Constants.lean:compApproxConst`;
`ApproxIsometryComp.lean`: `metricEquiv_trans`, `metricEquiv_comp_eps` (book additive
form), `compEpsAccum`.

**F8tool — Arzelà–Ascoli (Lemma 3.14).** `ArzelaAscoli.lean:arzelaAscoli_subseq_…`;
now also the vector-target core `arzelaAscoli_isCompact_closure` + sequential
`arzelaAscoli_subseq_vec` (proper normed target, used by the F8-engine).

**F9–F13 — direct limit (`lbl379`–`lbl381`).** `Geometry/Topology/DirectLimit.lean`:
`SeqSystem`, `Lim`, `incl`, `incl_injective`, `incl_isOpenMap`, `isCompact_exists`,
`sigmaCompact`, `t2Space` (+ universal property `lift`/`continuous_lift`).

**B0 (normal-coord bounds) stages 1–2.** `Exponential/JacobiVariation.lean:exists_radial_jacobi_radius`,
`Analysis/Calculus/SmoothClamp.lean:exists_smooth_clamp`; smooth exp diffeo
`NormalCoordinates.expMapDiffeo`/`normalChartAt`. See `B0NormalCoordBounds.md`.

**Honest-input fields (book-external).** `GeometricInputs.lean`/`StepAInputs.lean`
(A0 `lbl384` inj-radius decay, A0' Rauch/volume); `StepBInputs.lean` (S6 `lbl418`
exp⁻¹ deriv — `ExpInverseDerivBoundInput`, temporary);
`GoodCoveringItem3.lean` keeps legacy all-index radius/`g_p` declarations only
for compatibility. The canonical `lbl391`/`lbl392` exp-diffeomorphism scale is
`Item3RadiusAt` / `Item3RadiusTail`, and the `lbl383`/`lbl427` intrinsic scale is
`Item3GpScaleAt` / `Item3GpScaleTail`; both are produced from
`NormalRadiusProfile` after packing.

---

## ACTIVE FRONTIER (Track α, no §5 geometry)

- [x] **F4 — Cor *Norms of cov. derivs, II* (`lbl370`).** CLOSED in
      `Lemma45F4.lean`: `lemma45_corII`, `lemma45_corII_bound`, and
      `lemma45_corII_unif` assemble the intrinsic lift with data-independent
      constants. ⟸ F3, good-frame.
- [x] **F5 (C^p part)** — Prop *Composition of approx isometries, I* derivative side.
      **GREEN sorry-free (2026-06-11): `ApproxIsometryCompHigher.lean:comp_cov_le`** —
      `|∇_{g₀}^r(δ₀+δ₁)|_{g₀} ≤ ε₀ + ε₁·C_p` (same-domain). Fiber Minkowski at a g₀-ON
      basis (`exists_gOrthonormalBasis` + `metricInverseInBasis_of_orthonormal` +
      `sqrt_normSq0S_add_le`) splits the composed tower; the `δ₁` term via
      `lemma45_corII` (F4) + `iterCov_add`. ⟸ F4.
- [x] **F6 — Cor *Composition, II* (`lbl372`).** **GREEN sorry-free:
      `ApproxIsometryCompHigher.lean:comp_cov_accum`** — the `n`-fold accumulation
      `e n ≤ C·Σ_{i≤n} εᵢ` via the scalar fold `compEpsAccum` (ApproxIsometryComp.lean). ⟸ F5.
- [x] **F2-book** — Prop *Distances*, localized pre-approx-isometry form:
      `speed_le_of_c0` supplies the path-speed bound and `data_image_ball`
      supplies the image-ball inclusion from `PreApproxIsoDataOn`. ⟸ F1-c0, F2.
- [x] **F7** — Def *Cᵖ-convergence of maps* + *C^∞-conv. on compacts* (`lbl373`).
      **GREEN sorry-free (2026-06-11): `MapConvergence.lean`** — `mapDerivNorm`,
      `MapCPConvOn`, `MapCInfConvOnCompacts` (Euclidean `iteratedFDeriv` form, parallel to
      `PointedConvergence`'s `Metric*` names) + order/subset/subseq API + the bridges
      `mapCPConvOn_of_tendstoUniformly`, `tendstoUniformlyOn_of_cPConv`, `tendsto_of_cInf`.
- [x] **F8** — Cor *Compactness of a sequence of isometries* (`lbl374`), conditional
      on the separately audited [H6] `IsometryDerivBounds` input.
      **ASSEMBLED sorry-free (2026-06-11): `IsometryCompactness.lean`** —
      `isometry_seq_cInf` (convergence core) + `comp_eq_id_of_cInf` (invertibility, fully
      proved) + `isometry_seq_diffeo` (full `lbl374`, incl. the `C^∞` diffeomorphism limit
      via the symmetry argument). With the F8-engine now PROVED, `lbl374` is reduced to
      ONLY the honest-input `IsometryDerivBounds` (the `lbl375`→[H6] §5 derivative
      bounds). The plan's "apply F8tool" understated it: the scalar `ArzelaAscoli` tool is
      not directly enough. ⟸ **F8-engine** (done), F8-input.
- [x] **F8-engine** — *Arzelà–Ascoli for maps* (`MapConvergence.exists_cInf_subseq`).
      **PROVED sorry-free + axiom-clean (2026-06-11)**: smooth `Φₖ` with all `∇ʳΦₖ`
      bounded on compacts ⇒ `C^∞`-on-compacts convergent subsequence + smooth limit.
      Actual route (deviations recorded in `MapConvergence.md`): equicont/MVT →
      vector AA (`arzelaAscoli_isCompact_closure`, proper target; NEW
      `cmm_finiteDimensional` fills the Mathlib gap for `ContinuousMultilinearMap`) →
      diagonal-free compact countable product over all orders →
      `hasFDerivAt_of_tendstoUniformlyOn` on unit balls assembling a full
      `HasFTaylorSeriesUpTo ⊤` of the limit. ⟸ F8tool(scalar+vector).
- [~] **F8-input** — honest-input `IsometryDerivBounds` (`lbl375`→[H6] §5): isometry +
      bounded uniformly-Euclidean metrics ⇒ all `∇ʳΦₖ` bounded on compacts (book externalizes
      the polynomial recursion to [H6] §5).

---

## §5 Supporting: distance / exp⁻¹ derivatives — PARKED

The proper-realization Hopf--Rinow route is no longer blocked: C4 now uses the
checked intrinsic minimizing-exponential endpoint through `HopfRinowProper.lean`.
This §5 distance/exp-inverse layer remains parked on the separate Gauss/cut-locus/
Riemannian-gradient API surface and the convexity-specific inputs.

- [ ] S1 `lbl411` ∇d² · S2 `lbl412` Hess d² · [~] S3 `lbl413` Hess comparison (honest-input)
      · S4 local convexity · S5 `lbl417` convex balls · [~] S6 `lbl418` exp⁻¹ deriv (honest-input).

---

## §2 Step A — good coverings (`L783–1369`) — METRIC CORE DONE

**Done (2026-06-08/09, verified + axiom-clean; see `ch4-thm39-stepA` memory +
`GoodCovering.md`/`GoodCoveringOrdered.md`):** A1 (λ), A2 Zorn net + the book's
distance-ORDERED greedy net (`GoodCoveringOrdered.lean`, abstract
`[MetricSpace][ProperSpace]`), A3 cover/count, A4 finite cover, A5/A6, A7 `lbl390`
window, A8 `lbl391` radii, A9–A13, and the **capstone
`GoodCoveringSeq.lean:exists_stableNetData`** = `lbl383` items 1,2,4,5,6,7 on a
diagonal subsequence. The old `GoodCoveringOrdered.lean:exists_proper_realization`
Hopf--Rinow deferral is discharged through `HopfRinowProper.lean` and the intrinsic
exp endpoint. Honest inputs: A0 `lbl384` CGT decay, A0' PackingBound/ratio-ballMult
(Bishop–Gromov), RealizesEdist.

- [ ] **A-item3 — `lbl383` item 3** (exp∘L diffeo at λ-scale + geodesic convexity):
      the ONLY remaining Step A content. UN-PARKED 2026-06-11 (user: full 3a+3b);
      brick plan + status in `Geometry/Comparison/ConvexBalls.md`. **DONE sorry-free
      (2026-06-11):** B1 (`ConvexBalls.lean:isConvexWith_smallNormalBall`, lbl417) ·
      B2 (`ExpBallDiffeo.lean:exists_diffeo_of_injOn` [Mathlib-TODO glue] +
      `exists_expBall_diffeo`) · B3-pieces: ODE heart
      (`SecondOrderGronwall.lean:gronwall_sub_linear`/`gronwall_ne_zero`) ·
      ℓ²/ON-frame (`InnerExpansion.lean`) · frame producer
      (`PerpFrame.lean:exists_parallel_frame`) · KEYSTONE
      (`CovariantGronwall.lean:covGronwall_ne_zero`) · the **∞→finite-order
      refactor** of the parallel-transport chain (5 thms in `ParallelTransport.lean`
      + callers) so the clamped radial curve (ContMDiff 8) qualifies · injectivity
      reduction (`ExpNonsingular.lean:mfderiv_exp_injective_of_jacobi`).
      **B3 RESOLVED 2026-06-13 — item-3a COMPLETE & UNCONDITIONAL.** The Jacobi/Grönwall
      nonsingularity tower was UNNECESSARY for `hloc`: `ExpBallDiffeo.lean:
      exp_isLocalDiffeomorphOn_ball` discharges it directly from
      `NormalCoordinates.expMapDiffeo` (exp IS a partial diffeo via normal coords;
      source ⊇ ball), and `exists_expBall_diffeo_of_lt` is the unconditional item-3a
      ball-diffeo producer. **3b** = `ConvexBalls.lean:isConvexWith_smallNormalBall`
      (lbl417 assembly) modulo the §5 honest-inputs (Hopf–Rinow join selector + lbl416
      d²-Hessian-convexity, both = the plan's approved §5/`lbl413` boundary).
      **B5 exp-diffeomorphism bridge DONE; full item 3 remains open.**
      `GoodCoveringItem3.lean`: `PointedRiemannianManifold.exists_expBall_diffeo` (layer
      bridge net-manifold → exp ball diffeo) + the compatibility consumer
      `exists_seqItem3Diffeo`.  The canonical finite-slot radius is now produced
      by `Item3RadiusTail` and `exists_item3Diffeo`.  This closes 3a and its
      radius quantifiers; 3b still requires the §5 convexity/Hessian and
      physical-cage assembly, so the full textbook item-3 theorem is 0%.
      Optional: fold `exists_seqItem3Diffeo` into the `exists_stableNetData` capstone as a
      field (presentation only). The Jacobi/Grönwall bricks (keystone, ExpNonsingular, ∞→N
      refactor) are reusable analysis, now relevant to Step B `lbl395`, not item 3.
      **⟹ STEP A (faithful, book-benchmark) = COMPLETE modulo the declared black boxes**
      (A0/A0' decay+volume, §5 `lbl413`/`lbl416` convexity + C²-radius scale; the
      former proper-realization Hopf--Rinow black box is discharged).

## Convergence spine — canonical analytic interface (RULING 2026-06-17)

One convergence API across Steps B/C/D; do NOT spawn a parallel hierarchy.

- **State every new Step B/C/D convergence/limit fact `U`-relative** on
  `MapConvergence.MapCInfConvOnCompacts U` (the maps/metrics live on bounded Euclidean
  balls, not `Set.univ`), produced by the localized engine
  `MapConvergence.exists_cInf_subseq_on` (B-loc). Use the global
  `exists_cInf_subseq`/`MapCInfConvOnCompacts Set.univ` only for genuinely total maps.
- **Diffeomorphism limits** (transition maps, gluing) go through
  `IsometryCompactness.isometry_seq_diffeo` — its output (`PartialDiffeomorph` + the
  `Ψ∘Φ=id` cocycle) IS the `lbl394` transition-limit shape. No new isometry-compactness
  machinery.
- **Metric limits**: a metric in chart coords is a `MapCInfConvOnCompacts U` of the
  Gram-form-valued map `E → (E →L E →L ℝ)`; reuse the map engine, no metric-AA.
- **The pointed-CG-source vocabulary** (`MetricCompactness.lean`'s `MetricSourceCPConvOn`/
  `MetricCGConvergenceData`) appears ONLY at the **D5 endpoint**, reached by ONE bridge
  from the assembled local Map-convergence. The metric-side (`MetricCPConvOn`, LC
  covariant deriv) and map-side (`MapCInfConvOnCompacts`, Euclidean `iteratedFDeriv`)
  stay **parallel + bridged**, never unified (CLAUDE.md variant rule: different concept).
- Reusable Euclidean-analysis engines (`MapConvergence`, `MapConvergenceDeriv`,
  `ArzelaAscoli`, `DiagonalSubseq`) are promotion candidates to `Analysis/` post-completion
  (principle 1, "liberate buried byproducts"); deferred while Step B/C/D are in flight.

## §3 Step B — local metrics & transition maps (`L1370–1882`)

B0 stages 1–2 done (above); B0 stages 3–5 (x-derivative Grönwall) remain. **Spine:** use
the convergence-spine ruling above (B-loc `exists_cInf_subseq_on` + `isometry_seq_diffeo`).
`lbl395` (normal-coord metric bounds) is honest-input (book cites [H6] Cor 4.12); the
Jacobi/Grönwall tower (now off the item-3 path) is the native-discharge candidate for it.

- [x] B1 selected producer route for `lbl397`: conditional assemblies
      `stepB1_of_raw` and `stepB1_of_bounds` are checked, and
      `MetricCompactBase.exists_b1_raw` now produces the concrete
      `StepB1RawInput` with 5/5 fields checked.  The global stage map, exact
      local inverse, arbitrary finite-order intrinsic metric bounds, and master
      subsequence transport are all verified.  The separately named textbook
      B1 theorem is still unstated and therefore 0%; do not conflate that
      statement-level accounting with completion of the selected producer.

## §6 Step C — nonlinear averages (`L2638–end`)

- [~] C1 `lbl429` center of mass — `StepCCenterOfMass.centerOfMass` + `expInv_eqn_local`
      (conditional on `StrictDistInput`) · [~] C2 `lbl430` regularity at every finite
      order — COMPLETE; only the arbitrary-order quantitative derivative bounds remain 0%
      (see the 2026-07-05 item below) · [~] C3 `lbl434`
      averaging maps — `stepCJoin` (0-sorry, honest scale inputs) · [~] C4 `lbl436`
      average-of-→id-maps →id — the `stepCJoin` endpoint shape (averaged concrete maps
      → id on `hatSourceBall`). ⟸ B6.
      **C3 join COMPLETE 2026-07-03:** `StepCProducers.lean` — (A) `stepCJoinFixed`
      (`unifHatCageSelfComp` with `hR`/`hKV` discharged) + (B) `stepCJoin` (concrete
      `normalTransition` maps via `existsTransUniv` on `X.subseq L.φ`, averaged → id). Both
      green, no sorry, axiom-clean `[propext, Classical.choice, Quot.sound]`. Endpoint =
      `∃ phi, StrictMono phi ∧ (averaged concrete-map → id on hatSourceBall)` for B1. Bridges:
      `Item3GpScaleAt` (hR fixed-slot scale), `properBallImgOfRad`/`hatCageImg` (cage↔chart-image),
      `binfMemClosed` (hKV limit). Overlap/cocycle/σ-domain inputs threaded parametrically.
      **C2 `lbl430`(i) at C¹ COMPLETE 2026-07-04:** `StepCSmoothness.lean` — the center of mass is
      strictly differentiable (`C¹`) in (weights, points). Chain (all sorry-free, axiom-clean):
      readout-form equation `chartCmEqn'` (RULING #3, smooth via `contMDiffAt_totalSpace`, no `A⁻¹`)
      + `readout_sum_eq_zero_iff` (zero-set = book's `Σμᵢexp⁻¹qᵢ=0`) + `chartCmEqn'_contDiffAt`
      (`hjoint` PROVED) + `readoutSol_hasStrictFDerivAt` (Banach IFT + local uniqueness conjunct) +
      `center_hasStrictFDerivAt` (last-mile: IFT-injectivity identifies `chart_p∘c` with the implicit
      `f`) + **`centerOfMass_hasStrictFDerivAt` (2026-07-04, GREEN — the literal `centerOfMass` symbol
      in a `HasStrictFDerivAt` statement)**. **`hc_cont` DISCHARGED 2026-07-04 (GREEN):**
      `Comparison/CenterOfMass.metricEnergy_argmin_stable` (general argmin-stability: `μ,pts`
      continuous + `c a` a global min in a compact `K` + unique min at `p₀` ⟹ `c` continuous at `p₀`;
      sequential reduction + `IsCompact.tendsto_subseq` + limit-passing via joint energy continuity +
      uniqueness) → `StepCCenterOfMass.centerOfMass_cont` (the literal center's point continuity, from
      `min`/`mem`/`unique` + `centerEnergy_eq_dist` + `ProperSpace`) → `StepCSmoothness.centerOfMassChart_cont`
      (compose with `normalChartAt_contMDiffOn.continuousAt` = the `hc_cont` `Tendsto`). So the C2
      endpoint is conditional ONLY on `CmHessianInput` + `StrictDistInput` + smallness (`hc_solves` =
      per-params `expInv_eqn_local`+`readout_sum_eq_zero_iff` threading; `hpts`/`hsrc` = config
      point-map continuity + center-in-chart-source).
      **σ quantitative discharge (Ruling #4) 2026-07-04 — StepCProducers is 0-SORRY:** `properBallImgOfRad'`
      (coercive-tightened, GREEN) + `hatCageImg'` (GREEN, `⊆ ball 0 (σ γ)` under strict `4λ/√c < σ γ`;
      the strict scale kills the open/closed gap) + `hUx_of_sigma` (GREEN) + `SigmaScaleField` (the ONE
      sibling `lbl383` field folding `4λ/√c < σ ∧ σ ≤ expMapC2Radius`, `.expRadiusGp` derives `hR`).
      **2026-07-13 canonical producer closure:** `SigmaScaleAt`/`SigmaScaleTail`,
      `sigmaCenterTail`, `sigmaCenter_le`, and `exists_sigmaField` produce one
      common refinement for all ordered-net slots and include the `r₁` upper
      bound.  The real fixed-`beta`/active-`alpha` atom route can project this
      same field twice; only the old generic arbitrary-`y` API lacks a distance
      profile, and it will not be strengthened with an endpoint assumption.
      **B1 (`lbl397`) honest boundary, repaired 2026-07-09:** the false P-only
      `stepB1_approxIso` skeleton was deleted.  `StepB1RawInput` records the raw
      comparison-map producer data, while `stepB1_of_raw` and
      `stepB1_of_bounds` are checked conditional assemblies.  This was the
      2026-07-09 boundary snapshot; the concrete producer was discharged on
      2026-07-17, while the separately named textbook B1 theorem remains 0%.
      The partial-diffeomorph carrier and localized approximate-isometry
      conclusion are settled.
      See `StepCProducers.md` / `StepCSmoothness.md`.
      **C2' (`lbl430` all-order) — REGULARITY HALF DONE 2026-07-05 (parallel session,
      lbl430(ii)):** `centerOfMass_contDiffAt` (`StepCSmoothness.lean:900`) — the center
      of mass is `C^n` for every finite `n`, via the pinned-`Φ` `C^n` Banach IFT
      (`implicitSol_contDiffAt`), conditional only on `CmHessianInput` +
      `StrictDistInput` + smallness; full build green.  **REMAINING for `lbl397`'s
      `(ε,p)` for every `p`: the derivative-BOUNDS half** — `lbl430`'s quantitative
      `|∇^{p+1}cm| ≤ C̃_{p+1}` (uniform over the configuration family), which the B1
      assembly must thread; regularity alone gives no uniform constants.

## §4 Step D — directed system, limit, assembly (`L1883–2102`)

**Execution plan: `STEPD_PLAN.md` (2026-07-05, STEPB_PLAN granularity).**  Summary:

- [x] D1 `lbl406` directed system (`exists_directedApproxSystem` + the partial-data
      composition brick `partialData_comp`) ⟸ the explicit `StepB1RawInput` producer, F6, F2.
- [x] D2 `lbl407` limiting metrics on balls (diagonal + `Ψ_j` isometry-in-the-limit).
      The former `lbl404` composition-convergence gate is already checked.
- [x] D3 `M_∞` smooth structure + metric transport (`DirectLimitManifold.lean`:
      charted/IsManifold/metrizable + `g∞` with `incl* g∞ = g_{k,∞}`) ⟸ F9–F13 (done).
- [x] D4 convergence to the limit (`ofRestrictPullback` instantiation + ONE
      chart-estimate→`derivNormSupOn` bridge).
- [x] D5 completeness (`MetricComplete limit` via compact closed balls / ProperSpace).
- [x] **D6 ASSEMBLY: discharge `MetricCompactnessInputs.metricCompactness`**
      (the CONDITIONAL endpoint — ruling 2026-07-05) from D1–D5, including the
      already checked finite-slot radius/`g_p`, sigma, physical-cage,
      selected-branch Hessian, and full-convexity producers.

---

## Critical path (updated 2026-07-17)

**DONE:** Step A (metric core + item 3, modulo declared inputs); F-track engines;
the selected B/C stage-map and exact-inverse route; the concrete 5/5
`StepB1RawInput` producer; all Step-D consumer machinery; and the conditional
endpoint `MetricCompactnessInputs.metricCompactness`.  The checked endpoint
chain is `exists_b1_raw → compactness_of_b1 → ofSeqSubseq`.

**Remaining, kept separate:** the textbook B1 theorem is not separately stated
or proved (0%); the older full Step-C arbitrary quantitative recurrence is
incomplete but is not required by the selected route; and the unconditional
`metricCompactness` remains 0% because its CGT, Bishop–Gromov/uniform-packing,
[H6], and connectedness inputs lie outside this conditional Chapter 4 assembly.
Chapter 4 machinery is approximately 95%; whole-HCG machinery is approximately
60%.

### 2026-06-22 — `lbl394` DONE (both halves); B1 scoped (intertwines with C)

`lbl394` (local metric limits `exists_metricLimit_normalCoord` + transition limits
`exists_transitionLimit_normalTransition`) is COMPLETE and verified — both now rest only on
honest geometric containments (metric: `hsub`; transition: `hUx`/`hVy`/`hmapsJ`/`hmapsJbar`),
the `C∞` normal chart inverse having been built (`StepBInputs.normalChartAt_contMDiffAt_infty`,
fresh IFT-at-∞). See `StepBLocalMetrics.md` / `StepBTransition.md` / `StepBInputs.md` (2026-06-22).

**B1↔C correction (book L1531):** `lbl397` (B1, "approx-iso on a large ball") is the map
`F_{kℓ;r}` built BY AVERAGING the local maps `F_{kℓ}^α` via center of mass — i.e. B1's proof
USES Step C's averaging (`lbl434`). So B1 and C are NOT cleanly sequential; the plan's
`B1→…→B6 → C` ordering is a labeling artifact. Actual structure:
`lbl394 (J,J̄ limits, done) → lbl398/lbl399 (local maps F^α_{kℓ,β}=J̄∘J → id) → [C averaging] → lbl397`.

**Live next brick (2026-07-15):** the source-local center and intrinsic-join
capstones, canonical global stage map, smooth support-sensitive Route-A
configuration, and metric-to-geodesic-spray convergence are checked.  The
next theorem is the proof of `MapCInfConvOnCompacts.ode_solutionAt`: limit
trajectory tubes, large-stage containment, and all parameter variational jets.
Its statement is already in the tree, but the theorem remains 0%.  After it,
the sequence is forward normal phase, compact moving root, selected inverse,
then `invVelSum` center roots, with one threshold uniform in the reference,
source, and target stages.  See `B1_STAGE_MAP_RULING.md` and
`B1_MOVING_ROOT_CONSULT.md`; the pasteable proof-level question is in
`B1_ODE_STABILITY_CONSULT.md`.  Do not restart the resolved sigma, H6, Hessian,
intrinsic-join, or smooth-filler routes.

The geometric branch-scale work preceding this gate is complete:
`normalDiagAtFull` packages the smooth quantitative endpoint and normal-coordinate fence,
`IsNormalDiag.toBranch` / `full_transport` transport it exactly to
`DiagInvBranch`, and `normalBrAccept` supplies global positive relative
coefficients, whole-target domain and inverse data with the required quantifier
order.  `normalBrScale` is its checked compatibility projection.  `NormalBranchCage` already
checks the eventual live-center sublevel, one common selected `B.readDom`
branch, and the finite center/point consumer.  The physical large-`D`,
pair-index cage, dead-slot, readout, Hessian/Neumann, strict convexity, and
intrinsic-join ledgers are checked.  Atom/weight production and pinned
gluing/agreement are no longer frontiers.  Generic `C^infinity` ODE stability
is not part of this completed geometric ledger and remains the live analysis
frontier above.

**Off the critical path (reusable analysis, do NOT re-couple to Thm 3.9):** the
Jacobi/Grönwall nonsingularity tower (`CovariantGronwall`/`ExpNonsingular`/`InnerExpansion`
/∞→finite parallel-transport) — item-3a is unconditional without it; it is instead the
native-discharge candidate for Step B `lbl395`.

**§5 status:** item-3's §5 dependence collapsed (item-3a unconditional via normal coords).
The remaining §5 surface is honest-input only.

Honest-input boundary (total, restructured 2026-07-05 — see
`MetricCompactnessInputs.lean` + `../PROJECT_MAP.md` for the per-input audit):

- **Sequence-level, bundled in `MetricCompactnessInputs`:** A0 `lbl384` (CGT decay),
  `lbl387` `PackingBound`, A0' `VolumeComparisonInput` (**statement fixed 2026-07-05
  and sharpened 2026-07-08: capped at containing scale `m * r ≤ r0`, not just
  `r ≤ r0` — the uncapped form was FALSE in hyperbolic members**),
  `RealizesEdist`, and `lbl395` `NormalCoordMetricBoundInput`.  The temporary S6
  `ExpInverseDerivBoundInput` and endpoint field were removed after the H6
  finite source-slot migration and a zero-consumer audit.
- **Construction-stage, DISCHARGED at D6 (may not survive to the endpoint):**
  `normalRadius : NormalRadiusProfile ...` now produces both packing-local
  `Item3GpScaleTail` and `Item3RadiusTail` from one pre-packing divisor; the
  legacy all-index inputs are compatibility-only.  Sigma/`r₁`, full convexity,
  and physical-cage discharge are checked; the global stage-map remains.
- **Configuration-stage, DISCHARGED at D6:** `CmHessianInput` /
  `StrictDistInput` (per-configuration `lbl413`/`lbl416`
  consequences at book scale).
- **Bundle-v2, gated on the B-loc bridge:** F8 `lbl375`/[H6] §5
  (`IsometryDerivBounds`) — per-map-sequence; its universally-quantified bundle
  field shape is pinned by the B-loc brick.

The former Step A Hopf--Rinow `exists_proper_realization` input is discharged
(`HopfRinowProper.lean`; note `Comparison/HopfRinow.lean` still carries 4 DEAD
sorries in 3 unconsumed intrinsic-frontier statements — audited harmless 2026-07-05).
The H6 localized isometry-derivative producer now supplies the transition and
atom extraction chain directly; no S6 derivation or replacement input remains.
The smooth support-locality frontier is closed by the fixed two-bump Route-A
filler; the old whole-cage `hKV0` is neither needed nor restored.  The current
B/C consultation frontier is the common-domain selected normal-diagonal
inverse/readout convergence theorem, then the moving center equation and
implicit-solver convergence theorem.  See `B1_MOVING_ROOT_CONSULT.md`.  The
pointwise support capstone and smooth finite-slot configuration convergence
are checked.

**Shared with Chapter 3:** the good-frame producer (`RicBoundGoodFrame.lean`) is the
same gate as ric_bound's R4 (`RicBound.lean` endpoint, `RicBoundAssembly.aN_intrinsic_point`);
and the convergence spine (`MapConvergence`/`exists_cInf_subseq`/`isometry_seq_diffeo`) is
consumed by Ch3's P3 metric-preconvergence too.

## 2026-07-08 volume-input wiring status

`Volume/Packing.lean` now has the checked generic capped packing cardinality
gate, `C4/VolumeComparisonBridge.lean` has the explicit uniform local-volume
producer `UniformBallPack` and its checked conversion to `VolumeComparisonInput`,
and `MetricCompactnessInputs.lean` has `MetricCompactnessInputs.ofUniformVolume`
to build the conditional endpoint bundle from that producer.

This is dedicated producer infrastructure only. `VolumeComparisonInput` from
`SeqBoundedGeometry` remains 0% proved until a real Bishop–Gromov/uniform-volume
producer supplies `UniformBallPack`.  The explicit-volume conditional endpoint
`MetricCompactnessInputs.metricCompactness` is nevertheless complete (100%): it
honestly accepts that input through `MetricCompactnessInputs`.  Native
Bishop–Gromov/uniform-packing production is the remaining unconditional gap,
not an endpoint-assembly gap.

The unconditional route's next concrete target is the Bishop–Gromov producer
for `UniformBallPack`; the Steps B/C/D conditional assembly lane is closed.
