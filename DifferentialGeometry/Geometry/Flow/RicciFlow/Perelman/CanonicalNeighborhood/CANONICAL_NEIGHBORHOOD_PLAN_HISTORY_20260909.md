# Chapter 25 (formerly Chapter 12): no local collapsing and canonical neighbourhoods — plan

**Implementation scope, 2026-09-08:** the user now asks to prove Chapter25's own
arguments first and defer upstream integration. The Chapter25 task starts with
new `ScalarCutoff`, `EarlySlabVolume` and `ScalarNoncollapse` leaves. Reuse actual
native objects and already available lemmas; preserve accurate earlier inputs
without implementing other chapters. The full audit below remains the baseline;
new source is not counted as verified until its check/build/axiom receipts exist.

**Verified checkpoint, 2026-09-08 20:09 UTC:** §8.7 closes the early-slab volume
lemma without a radius/time restriction, the scalar cutoff/volume argument,
and the instantiated 3D strong-scalar and spatial noncollapse endpoints.
Eleven new public theorems have complete focused/build/standard-axiom receipts.
The §8.2 matrix and §8.1 census are the earlier planning baseline, not the updated
completion state. Arbitrary-dimensional entropy remains an explicit earlier input.
The subsequent §8.8 kernel-calculus checkpoint adds three more verified public
theorems, for **four new leaves / fourteen verified public declarations** this
continuation; full geometric cone exclusion remains open.

**Full-chapter planning audit, 2026-09-08:** see §8 for the current statement
census, source coverage, missing upstream inputs and execution order. This audit
covers all of Chapter 25, including the final canonical-neighborhood transfer.
It supersedes historical coverage estimates below, but does not reassign the
active Chapter 23 implementation lane or authorize work on Chapter 24.
The Soul task is doing Chapter 25 planning only; no Lean source or artifact was
changed for this audit. Current project guidance governs verification; older
workflow descriptions below are historical records.

Current owner correction (2026-09-08 UTC): this task owns Chapters 22, 23
and 25 in the reorganized book; Chapter 24 remains external. The old branch
audit found substantial Chapter 22 work but no dedicated Chapter 23
compactness implementation, so active proof work now starts at Chapter 23.
See `../KappaSolutions/KAPPA_COMPACTNESS_PLAN.md` for that execution lane.
The historical ownership and interface descriptions below are superseded
by this correction, `HANDOFF_CODEX.md` and the later status entries.

Owner's numbering: Chapter 12 = book25 `\chapter[No local collapsing and canonical neighborhoods]`
(labels `scn-*`). Scope of this lane, per the owner (2026-09-06): the first half, §12.2–§12.11,
which does not consume Chapter 9 (reduced geometry) or Chapter 11 (neck–cap); the rest waits for
the collaborator's merge of the 4.29 `Perelman/LGeometry` layer. Inputs from later chapters and
appendices enter as named `Prop` interfaces (placeholders) and are discharged when their
producers land. Refer to book displays by `\label`, never by tex line number.

Working rules for this lane are those of `Estimates/Shi/BANDO_SHI_PLAN.md` §3 (one worker per
new file, `lake env lean` only, no `lake build` by workers, at most 4 `lean.exe` host-wide —
another session is active on the Shi-chain files `Estimates/Shi/*`, `Solution/IntervalTransport.lean`,
`Estimates/MetricComparison.lean`, which this lane must not edit).

## 1. Crosswalk (§12.2–§12.11)

| Book node | Status | Where / gap |
|---|---|---|
| `def:scn-three-noncollapsing-predicates` (spatial tensor, parabolic tensor, strong scalar) | partial | `Perelman/Noncollapsing/Defs.lean`: `FlowMetricBall`, `IsRmControlled` (parabolic slab), `IsKappaNoncollapsed`, `KappaNoncollapsedBelowScale`, `NoLocalCollapsing` = the **parabolic tensor** predicate. Spatial-tensor and strong-scalar predicates: not stated. |
| `lem:scn-noncollapsing-scaling` | partial | `Noncollapsing/ScaleTransfer.lean` (`paraBall_kappa`, `backBall_kappa`, `NoLocalCollapsing (paraSolution …)`) for the parabolic predicate. |
| `lem:scn-mu-Sobolev-relaxation`, `thm:scn-mu-monotonicity-interface` | audit | `Entropy/W/*` (functional, first variation, `LowerBound`), `Noncollapsing/FlowBallFunctional.lean` (`flowball_w_upper`, `exists_sel_w_bound`), `CutoffFunctional.lean`, `CutoffEnergy.lean`. |
| `lem:scn-cutoff-entropy-doubling`, `lem:scn-local-entropy-volume`, `lem:scn-early-slab-volume` | audit | `Noncollapsing/{CutoffFunctional, FlowBallFunctional, EarlyTime}.lean` (`early_vol_low`, `early_ball_low`). |
| `thm:scn-smooth-no-local-collapsing` | **verified (parabolic form, dim 3)** | `Noncollapsing/EarlyTime.lean` `no_local_open` (closed 3-manifold, `closedOpen 0 ω`, `NoLocalCollapsing S ρ`); `Persistence.lean` `noncollapse_after`; `TimeSpan.lean` `noncollapse_span` (regular windows). Book form is spatial-tensor, all `n ≥ 2`. |
| `cor:scn-parabolic-noncollapse-injectivity` | partial | parabolic half is the tree's form; injectivity (CGT) via `Compactness/Foundations/NoncollapseInjectivity.lean` — audit. |
| `thm:scn-strong-scalar-no-local-collapsing` | not stated | |
| `lem:scn-noncollapse-passes-to-limit` | not stated | needs the pointed-convergence interface (`HCGCompactness.CompactnessConclusion`). |
| `def:scn-Phi-almost-nonnegative`, `lem:scn-admissible-Phi-majorant`, `lem:scn-Phi-scaling` | not stated | new file `Perelman/CanonicalNeighborhood/PinchingDatum.lean` (W-B). |
| `prop:scn-HI-to-Phi` | not stated | producer in the tree: `DimensionThree/HamiltonIvey/Pinching.lean` `hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagationOn` (`pinchHeight3 λ_min ≤ δR + 2δK e^{2+1/(2δ)}/(1+2K(t−t0))`), `RegionTransfer.lean` for `curvatureOperatorRegionPropagationOn`. |
| `def:scn-frozen-cylinder`, `def:scn-kappa-model-witness`, `def:scn-good-bad-points`, `lem:scn-model-witness-stability`, `lem:scn-good-point-derivatives` | not stated | wave 2 (W-C); `lem:scn-good-point-derivatives` consumes Chapter 7 (`Estimates/Shi/LocalAllOrders.lean`). |
| `prop:scn-maximal-point-singularity-model` | not stated | wave 2 (W-C); Hamilton compactness interface. |
| `lem:scn-bad-point-selection`, `lem:scn-local-propagation`, `lem:scn-good-point-buffered-canonical` | not stated | wave 2 (W-D). |
| `lem:scn-cone-terminal-exclusion`, `lem:scn-compact-path-approximation`, `lem:scn-finite-horn-produces-cone`, `thm:scn-bounded-curvature-at-distance` | not stated | wave 3; seven finite-horn inputs (`rem:scn-finite-horn-endpoint-status`) as interfaces. |
| `prop:scn-terminal-limit-global-bound`, `prop:scn-first-backward-slab`, `lem:scn-recentered-source-bound`, `lem:scn-uniform-moving-slice-propagation` | not stated | wave 3. |
| `lem:scn-remote-point-triangle`, `lem:scn-open-nonnegative-sphere-separation`, `lem:scn-far-point-separating-neck`, `prop:scn-ancient-extension` | not stated | wave 3; Toponogov (App A) and sphere separation (App C) interfaces. |
| `thm:scn-abstract-model-theorem` | not stated | wave 3 endpoint of the first half. |

## 2. Placeholder interfaces (named `Prop`s, to be discharged later)

From `sec:scn-formalization` ("imported interfaces requiring separate blueprint nodes"):
𝒲/μ monotonicity; compact logarithmic Sobolev; local Cheeger–Gromov–Taylor injectivity;
Hamilton compactness with one worldline-preserving embedding and source-ball capture; Hopf–Rinow;
finite-end intrinsic-metric, ray and triangle-approximation interfaces for the local Toponogov
theorem; compactness of the finite-end direction space; marked compact-annulus convergence to the
open cone; Cheeger–Gromoll splitting; soul and Sharafutdinov exhaustion; nonnegative-Ricci
at-most-two-ends; invariance of domain; smooth Jordan–Schoenflies; curvature-operator
null-eigenvector condition. Plus, for §12.12–12.13 only: `def:red-kappa-solution` (Chapter 9) and
`thm:ncs-kappa-canonical-neighborhood` (Chapter 11). Each interface lives in
`Perelman/CanonicalNeighborhood/Interfaces.lean` once first needed, with the book label in its
docstring; a theorem consuming one carries it as an explicit hypothesis.

## 3. Dispatch

### W-A — `Perelman/Noncollapsing/Predicates.lean` (§12.2, §12.3 audit)
Add the spatial-tensor and strong-scalar predicates of `def:scn-three-noncollapsing-predicates`
on `FlowMetricBall`; the implication bridges (spatial ⇒ parabolic; strong scalar ⇒ spatial with the
`|Rm| ≤ r⁻² ⇒ R ≤ c_n r⁻²` normalisation made explicit); `lem:scn-noncollapsing-scaling` for all
three via `ScaleTransfer.lean`'s `paraBall`; and an audit note stating exactly which book nodes of
§12.3 the existing `no_local_open`/`noncollapse_after`/`noncollapse_span` and the cutoff/flow-ball
functionals already prove, and what the spatial-tensor and strong-scalar theorems still need.

### W-B — `Perelman/CanonicalNeighborhood/PinchingDatum.lean` (§12.4)
`AdmissiblePinchingFunction`, `PhiAlmostNonnegative`, `lem:scn-admissible-Phi-majorant`,
`lem:scn-Phi-scaling`, and `prop:scn-HI-to-Phi` from the tree's asymptotic Hamilton–Ivey
inequality; the blow-up nonnegativity in scaling-stable pointwise form, with the limit passage
stated against the pointed-convergence interface or left as a named interface.

### W-C — `Perelman/CanonicalNeighborhood/ModelWitness.lean` (§12.5–§12.6) — wave 2
`def:scn-frozen-cylinder` (`frozenBackwardCylinder x t A S Q`, terminal-time ball × backward
interval, with its parabolic-rescaling identity `eq:scn-normalized-frozen-cylinder`);
`def:scn-kappa-model-witness` as a structure (`Q = R(x,t) > 0`, admissibility `t − (εQ)⁻¹ ≥ 0`,
the ancient model `(N, h, p)` with `R_h(p,0) = 1`, one time-independent embedding `F : V → M`
with `F p = x`, metric equivalence `eq:scn-model-metric-equivalence`, the explicit `C^m`
closeness `eq:scn-model-explicit-Cm` with `m_ε = ⌈ε⁻¹⌉ + 1`, source-ball capture
`eq:scn-model-source-capture`, orientation clause); `def:scn-good-bad-points`;
`lem:scn-model-witness-stability` (restriction δ ≤ ε with strict inequalities, openness of the
good set where the cylinder is admissible); `lem:scn-good-point-derivatives`
(`|∇R⁻¹ᐟ²| ≤ C_*`, `|∂_tR⁻¹| ≤ C_*` at good points, from Chapter 7's global estimates on the model
(`Compactness/Shi/Local.lean` `movingShi_complete` / Cor 7.17) transported through the witness);
`prop:scn-maximal-point-singularity-model` (spacetime maxima → ancient κ-solution limit) against
the tree's Hamilton compactness `HCGCompactness.compactnessSol` (`PointedFlowSeq`,
`CompleteInput`, `CurvBoundInput`, `FlowerScaleInjBound` from `Compactness/Foundations/`), the
injectivity input from `NoncollapseInjectivity.lean`, κ from `no_local_open`, nonnegativity from
W-B, ancientness from `−Q_i t_i → −∞`. The ancient κ-solution notion is Chapter 9's
`def:red-kappa-solution`: define a placeholder `IsAncientKappaSolution` in
`Perelman/CanonicalNeighborhood/Interfaces.lean` mirroring that definition field by field
(complete slices on `(−∞,0]`, nonnegative curvature operator, bounded curvature on compact
subintervals, κ-noncollapsed at all scales, nonflat), to be identified with Chapter 9's when it lands.

### W-D — `Perelman/CanonicalNeighborhood/BadPointSelection.lean` (§12.7, selection) — wave 2
`lem:scn-bad-point-selection` in per-flow form (strong induction on `⌊K/R⌋₊`, curvature at least
doubling per step, total time drop `≤ 2H/Q̂`), minimal hypotheses (closed slab in the carrier,
scalar curvature bounded above on it, the admissibility threshold making "not bad ⟹ good"
valid), then the sequence form with `H_i = min(√Q̂_i, Q̂_i/4)` and `∀ᶠ i` instead of a
subsequence: `eq:scn-bad-selected-basic`, `eq:scn-bad-window-admissible`,
`eq:scn-higher-curvature-good`.

### W-E — `Perelman/CanonicalNeighborhood/LocalPropagation.lean` (§12.7, propagation) — wave 2
`lem:scn-local-propagation` in unrescaled scale-invariant form with `eq:scn-higher-curvature-good`
as a hypothesis (so it does not wait for W-D): the first-crossing argument at levels `2QL`/`4QL`
from `GoodPointDerivativeBounds` (interface, W-C), the lower bound and the `|Rm|` bound from
`PhiAlmostNonnegative` (dimension-3 eigenvalue identities; the pointwise "eigenvalue bounds ⟹
|Rm| bound" step named as an interface only if absent from the tree), the uniform-limit clause
from `Φ(s)/s → 0`, then the book's rescaled display via `frozenBackwardCylinder_paraSolution`.

### Deferred: `lem:scn-good-point-buffered-canonical`
Its statement is written entirely in Chapter 11's vocabulary (canonical tuple, `α`-neck collar,
central sphere, buffered core, ball sandwich, algebraic intersection), none of which exists in the
tree, and Chapter 11 is the collaborator's. A `Prop` named `CanonicalTupleInterface` would carry
no content, so it is not written; the lemma is stated when Chapter 11's definitions land.

## 4. Status log

- 2026-09-06: lane opened on the owner's instruction relayed from the Shi-chain session; §12.3's
  theorem found already proved in the tree in parabolic form for dimension 3 (`no_local_open`).
  W-A, W-B dispatched.
- 2026-09-06 (coordination with the Shi-chain session, agreed): file ranges disjoint (they: `Estimates/Shi/*`, `Solution/IntervalTransport.lean`, `Estimates/MetricComparison.lean`, possibly a new `Estimates/Shi/SectionalFromCurvatureBound.lean`; we: `Perelman/CanonicalNeighborhood/*`, `Perelman/Noncollapsing/Predicates.lean`). `DifferentialGeometry.lean` is shared: before committing, `git diff DifferentialGeometry.lean` must show only this lane's import lines; otherwise stage only our hunk (`git add -p`-equivalent patch). Neither side commits `AGENTS.md` or `Galerkin/Basic.lean`. Host budget: their worker runs up to 2 `lean.exe` (including a 30–60 min `LEAN_NUM_THREADS=2 lake build DifferentialGeometry` at stage ends); this lane stays at 2; check for a running `lake.exe` before any targeted build. Chapter 7 will expose the book-exact Theorem 7.1 as `shi_local_all_orders_norm_of_solution` / `shi_local_all_orders_curvature_scale_of_solution` (unprimed; the primed versions exist now) — `lem:scn-good-point-derivatives` and later ball-local uses of Shi in this lane wait for those names.
- 2026-09-06 (wave 1 landed): W-A committed (`cca4926c3`): spatial-tensor and strong-scalar predicates, bridges (`b_n = n²`, `c = √(max 1 n²)`, strong scalar ⇒ spatial with `κ/cⁿ` below `cρ`), scaling laws; audit: the 𝒲-cutoff engine uses only time-t data, so the spatial form of `thm:scn-smooth-no-local-collapsing` is a restatement of seven lemmas (`shrink_rm`, `exists_coll_scale`, `flowball_wform`, `flowball_w_upper`, `exists_sel_w_bound`, `noncollapse_span`, `noncollapse_after`) plus a slab-free `lem:scn-early-slab-volume` (`family_vol_low` needs `r² ≤ t`) — **deferred; this lane uses the parabolic convention** (Perelman's), recorded as a deviation. W-B verified: §12.4 complete; convention: tree eigenvalues = sectional curvatures, so `PhiAlmostNonnegative` is `λ_min ≥ −Φ(R)`; `Φ = majorant(inf_δ(δs + 2δKe^{2+1/(2δ)})) + Ke³`; limit passage = interface `RescaledCurvatureTendsto` (the convergence structure `SmoothCGHConverges` lacks a curvature-operator pullback field — a future addition to `Compactness/`). W-C running (§12.5–12.6). Coordination: this lane ≤ 2 lean.exe; other session's W30 runs long root builds.

- 2026-09-06 (W-C landed, `53755cdea`): §12.5–12.6 — frozen cylinder with `eq:scn-normalized-frozen-cylinder`, placeholder `IsAncientKappaSolution` (in `ModelWitness.lean`, not `Interfaces.lean`: a fresh module cannot be imported by a sibling until built; merge or import once both are built, and collapse `PointedFlowRmNormLeScalar`/`PointedFlowSqrtRmNormLeScalar`, identify `PointedFlowNoncollapsedAllScales` with `Predicates.lean`'s spatial predicate), `KappaModelWitness` with the explicit `C^m` closeness on the product bundle (left time derivatives at `s = 0`), good/bad points, restriction under `δ ≤ ε` (stronger than the book: no strictness needed), the model half of `lem:scn-good-point-derivatives` via `movingShi_complete` with the tree's explicit constant, the compactness step of `prop:scn-maximal-point-singularity-model` against `compactnessSol` and the ancient assembly with nonflatness derived. Named interfaces (each with its reason in `ModelWitness.md` §4): `BlowUpLimitNonnegativeCurvature`, `NoncollapsePassesToLimit`, `RmNormBoundedByScalarCurvature` (`nonneg curvature operator ⟹ |Rm| ≤ CₙR`, the only step turning scalar bounds into the tensor bounds `CurvBoundInput`/`movingShi_complete` want), `GoodSetOpen`, `GoodPointDerivativeBounds` (two gaps: `movingShi_complete` needs `Ioc α ψ ⊆ D.regular` so the model bound stops short of `s = 0`; no curvature-jet-from-metric-jet transport along a partial diffeomorphism). Structural obstruction recorded: `compactnessSol` wants one fixed open window for the whole sequence, and the rescaled right endpoints `Q_i(T − t_i)` are not bounded below, so the ancient limit needs a diagonal step across windows that the tree cannot yet state; the ancient datum is taken as input. Four leaves built (`Predicates`, `PinchingDatum`, `Interfaces`, `ModelWitness`). Wave 2 dispatched: W-D (selection) and W-E (propagation) in parallel; `lem:scn-good-point-buffered-canonical` deferred to Chapter 11's vocabulary.
- 2026-09-06 (W-D landed): `BadPointSelection.lean` — `lem:scn-bad-point-selection` proved with no interface: `BadPointSelected` (the three displays plus the sharp displacement `t̂ − 2H/Q̂ ≤ t`), per-flow `exists_badPointSelected` by strong induction on `⌊K/R⌋₊`, the sequence form `eventually_exists_badPointSelected` over varying manifolds/time intervals with `selectionDepth Q̂ = min(√Q̂, Q̂/4)` and `∀ᶠ i` in place of a subsequence. Finding: in W-C's definitions `IsBadPoint = ¬IsGoodPoint` with admissibility inside the witness, so "not bad ⟹ good" needs no threshold; the threshold `Q ≥ 2/ε` (from `s ≥ 1/4` on the selected window) is the separate lemma `window_subset_carrier_of_two_mul_scalar_le`. Hypotheses: scalar curvature bounded above on the closed slab (the form the recursion needs), nothing else; `Φ`, `σ`, completeness, orientation, dimension are absent. Axioms propext/choice/Quot.sound. W-E running.
- 2026-09-06 (Chapter 7 endpoint names, relayed by the Shi-chain session, commit `c34e18d46`): `DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_norm_of_solution` (Thm 7.1) and `…shi_local_all_orders_curvature_scale_of_solution` (Cor 7.2) in `Estimates/Shi/LaplacianInputRegularWindow.lean`, book-exact: `S : SolutionOn (closedOpen α ω _)`, `α < 0 < T < ω`, compact closed `g(0)`-ball of radius `R` about `p` (`riemannianEDistOf`), ball-local `nablaKRm04NormSqIntrinsic S 0 s y ≤ 1` (squared norm) on `Icc 0 T`; conclusion on the half ball for `t ∈ Ioc 0 T`, `√(t^m|∇^m Rm|²) ≤ C`; Cor 7.2 with `|Rm|² ≤ K²` on radius `R/√K`, constants `C·K`, extra `0 ∈ carrier`. No completeness, no sectional hypothesis. Also `Estimates/Shi/SectionalFromCurvatureBound.lean`: `sectionalBoundedBelowAt_of_curvature_bound` (`|Rm| ≤ K` on a ball ⟹ `sec ≥ −K`). Use these for ball-local Shi in §12 from now on. They do not close W-C's terminal-time gap in `GoodPointDerivativeBounds`: the window must end strictly inside the regular part (`T < ω`), and the tree's closed right end is never regular.
- 2026-09-06 (terminal-time limits, agreed reading with the Shi-chain session; owner decision pending): sequence side closed — bad points have interior times in `closedOpen 0 T`, so after `paraSolution S (t_i − 1/Q_i) Q_i` (window `[0,1]`, `1 < ω_i = Q_i(T − t_i)`, only strict positivity needed) the unprimed Thm 7.1 gives all-order bounds at `s = 1` with constants independent of the forward slack; bridge via `SolutionOn.cast` + `paraInterval_closedOpen_carrier/_regular` (as in Cor 7.2's proof). Hence the source half of `GoodPointDerivativeBounds` can be demoted from interface to theorem by a later worker. Limit side is the real gap: (a) `compactnessSol` wants one common open window with `0` interior; (b) regularity of the limit at its closed right end. Route: limit on the open window `(α, 0)` with the existing theorem, then uniform mixed-derivative bounds `∂_t^q ∇^p Rm` (book Prop 7.19/7.20, unstated in the tree; `Compactness/Bounds/RicciComponents.lean` has component-form `mixed_*`) + Arzelà–Ascoli to extend convergence to `s = 0`. Proposed split: Prop 7.19/7.20 in the Chapter 7 lane; `compactnessSol_terminal` (new append-only file under `Compactness/Limits/`, no edits to existing statements) in this lane, its conclusion including all-order convergence at the closed end, which is what W-C's placeholder `IsAncientKappaSolution` (`regular_eq = Iio 0`) lacks for the model's smoothness at `s = 0`. Chapter 10's κ-solution limits at time 0 need the same theorem.

- 2026-09-06 (Codex, `bb498b689`, task 2c): `ModelWitness.lean` now imports `Interfaces` and `Noncollapsing.Predicates`. `PointedFlowSqrtRmNormLeScalar` is a compatibility abbreviation for `PointedFlowRmNormLeScalar`; the scalar-bound and ancient Shi consumers state the latter directly (`eq:red-nonnegative-curvature-bridges`). `PointedFlowNoncollapsedAllScales` uses the native spatial tensor predicate; `pointedFlowNoncollapsedAllScales_iff` identifies it with `PointedFlowSpatiallyKappaNoncollapsed F kappa Set.univ` (`def:red-kappa-solution`, `def:scn-three-noncollapsing-predicates`). The predicates' mathematics and all hypotheses/constants are unchanged; no new interface was introduced and no terminal or limit input was discharged. The four affected public endpoints have only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/ModelWitness.lean`: exit 0, empty output. Sequential targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.<Module>` passed with zero warnings/errors for `ModelWitness`, `LocalPropagation`, `WitnessTransport`, `ScalarComparison`, `GoodPointDerivatives`, `BadPointSelection`, `ModelTheorem`, `RmNormFromEigenvalues`, `WitnessBallCapture`, `ShiUniformConstant`, `ScalarLaplacianJet`. Each run used the prescribed process gates, with only one owned Lean process. Only `ModelWitness.lean` and its note were committed. Task 2c is closed; task 2d uses new oriented selection/model leaves and retains the existing orientation-free API.

- 2026-09-06 (Codex, `a90e275d3`, task 2d selection): new `OrientedBadPointSelection.lean` proves `exists_orientedBadPointSelected` and `eventually_exists_orientedBadPointSelected` (`lem:scn-bad-point-selection`, `eq:scn-bad-selected-basic`, `eq:scn-bad-window-admissible`, `eq:scn-higher-curvature-good`). Both retained badness and the higher-curvature good locus use the same `IsOrientedGoodPoint`; oriented badness is never converted to ordinary badness. `higher_curvature_isGoodPoint` forgets only the good-locus orientation, and `orientedBadPointSelected_trivial_iff` proves exact compatibility with the old selection at the trivial datum. The scalar upper bound on a closed slab is the only curvature hypothesis of the recursion; completeness, PDE, pinching, noncollapsing and dimension are not used. Constants remain the doubling factor 2, displacement `2H/Qhat`, time lower bound `1/2`, ratio `H/Q <= 1/4`, and depth `H = min(sqrt Qhat, Qhat/4)`. No named interface is introduced or consumed; actual orientation realization/transport is not claimed. Four public theorems audited: propext/Classical.choice/Quot.sound only. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/OrientedBadPointSelection.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OrientedBadPointSelection`: exit 0, zero warnings/errors (24s). Only the new leaf/note and its one root import were committed. The oriented model-radius contradiction is next.

- 2026-09-06 (Codex, `7f2a02454`, task 2d endpoint): new `OrientedModelTheorem.lean` proves `exists_orientedModelRadius_of_selectedSequenceEventuallyGood`, the orientation-correct contradiction skeleton for `thm:scn-abstract-model-theorem`. `OrientedModelRadiusWorks` concludes `IsOrientedGoodPoint`; candidate radii are `min(sqrt epsilon, 1/(n+1))`, output `0 < r0 <= sqrt epsilon`, with fixed sigma chosen first (`eq:scn-r0-dependence`, `eq:scn-high-curvature-threshold`, `rem:scn-fixed-sigma-repair`). Source scope and hypotheses remain those of the old endpoint: `closedOpen 0 T`, `1 <= t0 < T`, and `ModelFlowHypotheses` with scalar upper bounds on compact subslabs. The one named input is `OrientedSelectedSequenceEventuallyGood`, the orientation-correct version of the old selected-sequence block, not a proved geometric producer: Chapter 24 buffered canonical neighbourhoods; Chapter 25 bounded-curvature-at-distance, terminal global bound, backward slab and ancient extension; terminal convergence-to-witness and actual orientation transport remain. The refined and old blocks/radius predicates are proved equivalent at the trivial orientation datum; arbitrary oriented badness is never converted to ordinary badness. Four public theorems audited: propext/Classical.choice/Quot.sound only. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/OrientedModelTheorem.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OrientedModelTheorem`: exit 0, zero warnings/errors (23s). Only the new file/note and one root import were committed; existing selection/model files remain unchanged. Task 2d is closed at its requested conditional endpoint; task 3 (new appendix files, not new comparison interfaces) is next.

- 2026-09-06 (Codex, `1617e1109`, task 3 analytic core): new appendix file `Geometry/Comparison/Toponogov/LowerSupportConvexity.lean` proves `convexOn_of_lower_support` (`lem:top-lower-support-convexity`), `convex_quotient_mono` (`eq:top-convex-quotient`) and `convex_endpoint_lower_support` (`eq:top-convex-endpoint-support`, together `lem:top-convex-consequences`). A continuous supported function is enough; smoothness and the second derivative belong to the local lower support, not the function. The endpoint lemma only needs a right derivative of the touching support. `second_deriv_nonpos_of_isLocalMax` is proved from Mathlib's derivative test and local constancy. The proof is the appendix's positive quadratic perturbation, chosen as `eta = (f(y)-ell(y))/(2*(y-a)*(b-y))`; no geometric constants, hypotheses, or new interfaces are introduced. Four public theorems audited: propext/Classical.choice/Quot.sound only. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/LowerSupportConvexity.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.LowerSupportConvexity`: exit 0, zero warnings/errors (16s). Only the new file/note and one root import were committed; no below-lane edits. The note records the real-derivative instance-alignment detail. This closes the one-dimensional appendix lemmas, not the geometric squared-distance support, hinge comparison, RemotePointTriangle or sphere separation; those remain task 3 work.

- 2026-09-06 (Codex, `dbf893d2e`, task 3 angle API): new `Geometry/Comparison/Toponogov/ComparisonAngle.lean` implements `def:top-comparison-angle` and proves the ten elementary statements for `lem:top-comparison-angle-api`: range, cosine quotient, positive scaling, arm symmetry, limit continuity and weak-triangle closure, zero/straight degenerate angles, and metric specialisation. The metric theorem needs only a metric space and positive arms; outer vertices may coincide. Constants are exactly `0`, `pi`, and `2*a*b`. No geometric comparison or new interface is assumed. All ten theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/ComparisonAngle.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle`: exit 0, no warnings/errors (10s leaf). Only the new file/note and own root import were committed. Squared-distance geometric support, the hinge theorem, RemotePointTriangle and sphere separation remain open task 3 work.

- 2026-09-06 (Codex, `185b63597`, task 3 geometric preparation): new `Toponogov/SharpRadialHessian.lean` proves `branchHess_sharp_le_of_minimizing_of_sectional_curvature_nonnegative` and `branchHess_gradient_le_of_minimizing_of_sectional_curvature_nonnegative`, retaining the radial correction needed for `lem:top-squared-distance-support` / `cor:top-squared-distance-convexity`. The bound is exactly `(g(Y,Y) - g(grad r,Y)^2)/L`; its velocity form uses the time-one velocity of norm `L`. The proved native weak Hessian bound is applied to the perpendicular component; private Jacobi/radial-cross/symmetry bridges are duplicated here without editing the native file. Context: complete positive-dimensional smooth boundaryless manifold with compatible metric instances, a minimizing unit radial geodesic, an inverse exponential branch, and nonnegative sectional curvature along the segment. No comparison interface or stronger curvature hypothesis is added. The appendix's local incomplete-manifold support lemma is not claimed. Both public theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/SharpRadialHessian.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.SharpRadialHessian`: exit 0, no warnings/errors (20s leaf). Path-limited commit contains only the new file/note and root import. Next: arbitrarily short Calabi shift, then genuine squared-distance support/convexity, not a new named interface.
  Shared-index incident: the preceding angle-status commit `456c7f1cf` also captured eight concurrently staged Extinction/Surgery documentation files from the other lane; this lane did not edit those files. History is preserved, not rewritten. Subsequent commits explicitly use `git commit --only -- <own paths>`; new files must first be added by exact path. The other lane subsequently made its own `d6bad1e52` documentation commit.

- 2026-09-06 (Codex, `03365bd77`, task 3 geometric preparation): new `Toponogov/CalabiTail.lean` proves `exists_calabiTail_fraction`, the arbitrary-small-shift input for `cor:top-squared-distance-convexity`. Given a minimizing exponential segment of length `r > 0` and any `0 < s <= 1/2`, it produces the existing `CalabiTailData` with exact `left = s*r` and `ell = (1-s)*r`, including a non-conjugate tail and smooth inverse exponential branch. This removes the old fixed-quarter loss without editing `DistanceCalabi.lean`. No curvature assumption or new interface: context is the native complete positive-dimensional boundaryless intrinsic exponential API. It does not yet assert squared-distance convexity or the local incomplete-manifold support theorem. Axiom audit: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/CalabiTail.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.CalabiTail`: exit 0, no warnings/errors (17s leaf). Path-limited commit includes only the new leaf/note and root import. Next leaf combines this actual producer with the sharp radial Hessian bound to produce the smooth distance support.

- 2026-09-06 (Codex, `7c4644aa2`, task 3 support producer): new `Toponogov/SharpDistanceSupport.lean` proves `calabiDist_sharp_hess_support_on`, producing a smooth Calabi upper support for the actual distance with contact value `r`, unit gradient, and Hessian bound `(g(Y,Y)-g(grad rho,Y)^2)/((1-s)*r)` for every `0 < s <= 1/2`. This is geometric input to `cor:top-squared-distance-convexity`, not a new named interface. All inputs are proved producers: fractional Calabi tail, native Calabi smoothness/contact/gradient, and sharp radial Hessian comparison. Hypotheses are complete positive-dimensional smooth boundaryless compatible metric context, nonnegative sectional curvature, and finite positive distance; no extra minimizing or support hypothesis is left to the caller. The appendix's local incomplete-manifold support lemma remains a separate stronger statement. Axiom audit only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/SharpDistanceSupport.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.SharpDistanceSupport`: exit 0, no warnings/errors (17s leaf). Path-limited code commit contains only this leaf/note and root import. The next leaf must prove actual squared-distance convexity, treating zero distance with the affine support and positive distance with arbitrarily small Calabi error.

- 2026-09-06 (Codex, `3a43645e0`, task 3 complete convexity): new `Toponogov/SquaredDistanceConvexity.lean` proves `convexOn_sq_sub_sq_riemannianEDist_intrinsicGeodesic`, the intrinsic-geodesic version of `cor:top-squared-distance-convexity`. On a complete connected smooth boundaryless manifold with nonnegative sectional curvature, the actual function `t^2 - d(p, intrinsicGeodesic g q u t)^2` is convex on every real convex set when `g(u,u)=1`; the geodesic need not be minimizing. Positive finite dimension and compatible bundle metric instances are the native exponential API context. There is no support/convexity interface or error term in the conclusion. Proof: the one-dimensional lower-support argument is proved locally for arbitrarily small negative second derivative; choose `delta=min epsilon 1`, `s=delta/(2+delta)` in the actual sharp Calabi support, obtaining error `-delta`; at zero distance use the affine support `2*t0*t-t0^2`. No cut-point distance derivative is taken. This does not yet prove the stronger local incomplete-manifold realized-connector support theorem or provide an arbitrary interval-geodesic wrapper. Axiom audit only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/SquaredDistanceConvexity.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceConvexity`: exit 0, no warnings/errors (21s leaf). New leaf/note and own root import only, committed by explicit paths. Next: prescribed minimizing-direction distance support, complete hinge/equal-arm comparison, minimizing ray and RemotePointTriangle; sphere separation remains later task 3 work. The note records original-topology continuity and pointwise real-calculus normalization details.

- 2026-09-06 (Codex, `968ddf959`, task 3 prescribed direction): new `Toponogov/PrescribedDistanceSupport.lean` proves `smooth_distance_upper_support_of_minimizing_exp`, the distance-support input to `eq:top-support-first-derivative` needed by `cor:top-hinge-zero`. For a specified nonconstant minimizing intrinsic exponential segment it produces a smooth distance upper support, with exact contact and gradient `r^(-1) * terminalVelocity`; the chosen midpoint fraction `1/2` cancels. No curvature assumption or new interface is used. The native complete positive-dimensional boundaryless context remains; this does not claim the stronger local incomplete-manifold second-derivative support theorem. Public `curveVelocity_affine` is also proved in the ordinary differentiable-curve context, without unnecessary complete-manifold binders. Both public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/PrescribedDistanceSupport.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.PrescribedDistanceSupport`: exit 0, no warnings/errors (12s leaf). Only leaf/note/root import in path-limited commit. The important directional distinction is preserved: an arbitrary Calabi tail at a cut point does not specify the first arm's angle, so the actual input segment is retained through tail reparametrisation. Complete hinge/equal-arm comparison is the next consumer.

- 2026-09-06 (Codex, `b3ee17f6b` plus corrective `dec89d518`, task 3 complete hinge): new `Toponogov/CompleteHinge.lean` proves `complete_hinge_sq` for `cor:top-hinge-zero` / `eq:top-hinge-zero`, and `complete_equal_arm_norm` / `complete_equal_arm_angle` for `cor:top-equal-arm-hinge` / `eq:top-equal-arm-hinge`. In the native complete connected positive-dimensional smooth boundaryless metric context with nonnegative sectional curvature, only the first unit-speed arm is assumed minimizing. Bounds are exactly `d^2 <= a^2+b^2-2*a*b*g(u,v)` and, for equal arms, `d <= a*sqrt(g(u-v,u-v)) = 2*a*sin(arccos(g(u,v))/2)`. No comparison or angle interface remains; the stronger local incomplete-manifold hinge is not claimed. All three declarations audited with only propext/Classical.choice/Quot.sound. The initial code commit preceded discovery of a multi-goal style warning in targeted build output; it was not a zero-warning landing. The path-limited corrective commit explicitly supplies the metric to `inner_gradientFun` and removes the resulting redundant `change`. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/CompleteHinge.lean`: exit 0, empty output. Final targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge`: exit 0, no warnings/errors (14s leaf). Process gates and one-own-Lean limit respected. RemotePointTriangle next needs the minimizing-ray extraction and quantitative intermediate-value argument; these are implementation tasks, not newly assumed interfaces.

- 2026-09-06 (Codex, `73bf462dd`, task 3 minimizing ray): new `Toponogov/MinimizingRay.lean` proves `minimizing_ray_of_tendsto_unit_vectors` and `exists_minimizing_ray_subsequence`, the ray construction in `lem:scn-remote-point-triangle` before `eq:scn-remote-ray-data`. In the native complete positive-dimensional smooth boundaryless compatible-metric context, unit initial vectors with positive minimizing lengths tending to infinity have a unit convergent subsequence whose limit intrinsic geodesic satisfies exact extended distance `ofReal L` at every `L >= 0`. No curvature or connectivity hypothesis and no ray interface are added. The proof passes shorter minimizing-segment distance equalities to the limit using exponential continuity, without assuming global distance finiteness. Both public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Comparison/Toponogov/MinimizingRay.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingRay`: exit 0, no warnings/errors (10s leaf). Only leaf/note/own root import committed by explicit paths. The remaining RemotePointTriangle work is the actual equal-arm plus intermediate-value argument with factor `3/2`, not an assumed ray input.

- 2026-09-06 (Codex, `6a63f0a63`, task 3 remote triangle closed): new `CanonicalNeighborhood/RemotePointTriangle.lean` proves `remote_point_triangle_of_compatible_metric` and `remotePointTriangle`, discharging the existing `RemotePointTriangle I` for `lem:scn-remote-point-triangle` / `eq:scn-remote-triangle`. The public adapter has only the book's boundaryless convention beyond the existing interface hypotheses; the zero-dimensional case is proved by discreteness and connectedness, so no positive-dimension assumption survives. The compatible-metric core even drops noncompactness because the eventual statement is vacuous at sufficiently large distance in the compact case. Actual proof chain: normalized minimizing exponential vectors, compact-unit-sphere subsequence, proved minimizing ray, proved complete equal-arm comparison, continuous distance on ray times `[d,2*d]`, intermediate value, and triangle inequalities. Constants are exactly relative error `<1/2` and final factor `3/2`; the threshold is existential as in the book. No comparison, ray, or remote-triangle interface remains unproved. Both public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/RemotePointTriangle.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RemotePointTriangle`: exit 0, no warnings/errors (16s leaf). New leaf/note and own root import only; explicit-path commit. `CompactPathAvoidance` retains the named proposition as compatibility target; its historical absent-producer text is superseded here. The next task-3 obligations are sphere separation and the ends package, not a collaborator comparison merge.

- 2026-09-06 (Codex, `369104b82`, task 3 finite ends): new `Geometry/Topology/FiniteEnds.lean` implements `HasAtLeastEnds`, `HasExactlyEnds`, and `HasAtMostTwoEnds` for `def:cgs2e-ends` using native `connectedComponentIn` and noncompact ambient closures. `hasAtLeastEnds_homeomorph_iff`, `hasExactlyEnds_homeomorph_iff`, and `hasAtMostTwoEnds_homeomorph_iff` prove `lem:cgs2e-ends-homeomorphism-invariant`; `HasAtLeastEnds.mono`, `not_hasAtLeastEnds_of_compact`, and `hasAtMostTwoEnds_of_not_hasAtLeastEnds_two` prove the elementary count consequences. These statements need only topological spaces (compactness for the compact-space corollary), not unnecessary manifold/connectedness/Hausdorff assumptions. Counts are exactly `k`, `k+1`, and `3`; no geometric constant occurs. All six public theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/FiniteEnds.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.FiniteEnds`: exit 0, no warnings/errors (7.2s leaf). New leaf/note/own root import only, explicit-path commit. This proves the appendix's end predicates and invariance, not sphere separation or the nonnegative-Ricci ends theorem. Native-source searches found no Alexander-duality or Cheeger--Gromoll splitting producer; their mathematics remains explicit task-3 work, not a new assumed interface.

- 2026-09-06 (Codex, `fb53bd92a`, task 3 escaping components): new `Geometry/Topology/EscapingComponent.lean` proves `exists_infDist_gt_of_not_isCompact_closure` and `exists_tendsto_infDist_atTop_of_not_isCompact_closure`, the proper-metric core of `lem:cgs2e-escaping-component` / `eq:cgs2e-escaping-component`. For nonempty compact `K` and noncompact ambient closure of `U`, every real radius is exceeded by `infDist x K` for some `x in U`; the sequence has the explicit lower bound `infDist (x n) K > n` and tends to infinity. No connected-component or manifold assumption is needed in this metric lemma. A complete-manifold consumer still instantiates properness from the native proved Hopf--Rinow theorem; this leaf does not claim that adapter or the two-ends line theorem. No new interface is introduced. Both public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/EscapingComponent.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.EscapingComponent`: exit 0, no warnings/errors (6.8s leaf). New leaf/note/own root import only, explicit-path commit. Next: the actual product-end dichotomy and remaining geometric/topological separation producers.

- 2026-09-06 (Codex, `890d06890`, task 3 product ends): new `Geometry/Topology/ProductLineEnds.lean` proves both alternatives of `lem:cgs2e-product-line-ends`: `hasExactlyEnds_prod_real_of_noncompact` is `eq:cgs2e-noncompact-factor-one-end`, and `hasExactlyEnds_prod_real_of_compact` is `eq:cgs2e-compact-factor-two-ends`. Public supporting declarations are `exists_compact_box_of_isCompact` (`eq:cgs2e-box-containing-C`), `isConnected_compl_prod_Icc` (`eq:cgs2e-box-exterior`), and `hasAtMostTwoEnds_prod_real_of_compact` (arbitrary compact separator). The proof uses only a connected Hausdorff factor; no metric or local manifold assumptions are added. Boxes are exactly `K × [-R,R]` with `R > 0`; the two-end witness is `N × {0}` with points at heights `1` and `-1`. Connected horizontal slices and vertical lines prove exterior connectedness; noncompact ambient closures must meet the exterior, and a finite injection argument counts the components. No product-end interface remains. All five public theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/ProductLineEnds.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.ProductLineEnds`: exit 0, no warnings/errors (7.5s leaf). New leaf/note/own root import only, explicit-path commit. The actual two-ends line producer, Ricci splitting theorem, and sphere-separation topology remain separate task-3 obligations; this product calculation does not claim any of them.

- 2026-09-06 (Codex, `3440c38e2`, task 3 metric line limit): new `Geometry/Topology/MetricLineLimit.lean` proves `dist_eq_sub_of_lipschitzWith_one_of_endpoints` and `exists_isometry_of_two_sided_minimizing_segments`, the metric limiting step in `lem:cgs2e-two-ends-line`. In a proper metric space, globally unit-Lipschitz curves with marked points in one compact set and minimizing endpoints diverging in both time directions produce a native `Isometry` of the whole real line through that compact set. The only Lipschitz constant is exactly `1`; every limiting distance is exact. Proof uses compact pointwise balls and Tychonoff cluster-point compactness, then continuity of each two-time distance; it does not assume a varying-base tangent-bundle compactness interface. Both public theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/MetricLineLimit.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.MetricLineLimit`: exit 0, no warnings/errors (6.9s leaf). New leaf/note/own root import only, explicit-path commit. Crossing-segment production from two ends and smooth Riemannian geodesic identification remain separate obligations; the metric limiting lemma alone is not the full geodesic-line theorem.

- 2026-09-06 (Codex, `047243756`, task 3 two ends to metric line): new `Geometry/Topology/TwoEndsMetricLine.lean` proves `exists_riemannian_metric_line_of_two_ends`, the actual all-time Riemannian-distance conclusion of `lem:cgs2e-two-ends-line`. Its public hypotheses are the complete connected smooth boundaryless manifold context and `HasAtLeastEnds M 2`; zero dimension is handled by discreteness and connectedness, without a positive-dimension restriction. Native Hopf--Rinow properness and normalized minimizing exponential vectors discharge the private segment input. The minimizing segments must cross the compact separator; shifting to a crossing yields marked points in that separator and both endpoint lengths greater than `n`. The metric line limit then gives exact `riemannianEDistOf g (gamma s) (gamma t) = ofReal |s-t|` for all real `s,t`, with constant `1` and no error or interface. The public theorem audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/TwoEndsMetricLine.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.TwoEndsMetricLine`: exit 0, no warnings/errors (10s leaf). New leaf/note/own root import only, explicit-path commit. Native `Topology/FiberBundleT2` supplies bundle Hausdorffness. Smooth unit-speed geodesic identification of the metric line is not asserted; Ricci splitting, the curvature ends theorem, and sphere separation remain separate obligations.

- 2026-09-06 (Codex, `9ccc68029`, task 3 Busemann basics): new `Geometry/Topology/BusemannBasic.lean` defines `busemannApprox` and `busemann` for a native isometric ray `NNReal -> X`, with the exact book sign `t - d` (`def:cgs-busemann`, `eq:cgs-approximate-busemann`, `eq:cgs-busemann`). Ten public theorems prove all four conclusions of `lem:cgs-busemann-basic`: monotonicity, finite two-sided bounds, convergence to the supremum, Lipschitz constant exactly `1`, calibration, and compact-uniform convergence for nonnegative real times. `tendsto_busemannApprox_of_tendsto` also proves the moving-point limit used in `eq:cgs-coray-calibration`, over an arbitrary filter. Only a metric space and isometric ray are required; no completeness, curvature, compact confinement, or geometric interface is assumed. The directed-index Dini theorem proves compact-uniform convergence directly. All ten theorems audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/BusemannBasic.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.BusemannBasic`: exit 0, zero warnings/errors (7.2s leaf). New leaf/note/own root import only, explicit-path commit. Coray construction and its smooth lower support, support maximum principle, Ricci splitting, and sphere-separation topology remain separate actual proofs to produce, not new named interfaces.

- 2026-09-06 (Codex, `7dab96609`, task 3 calibrated coray): new `Geometry/Topology/CalibratedCoray.lean` proves `lipschitzWith_one_intrinsicGeodesic`, `exists_calibrated_intrinsic_ray`, and `exists_intrinsic_coray_distance_support`, the ray-production, exact calibration, and global support/contact parts of `lem:cgs-coray-support` (`eq:cgs-coray-calibration`, `eq:cgs-coray-support`). In the native complete positive-dimensional smooth boundaryless compatible metric context, every point admits an intrinsic geodesic with unit initial velocity whose entire NNReal restriction is an isometry and whose Busemann values are exactly `b(p)+s`. No curvature, coray existence, or calibration input is assumed; smoothness of the input metric ray is unnecessary. Explicit times are `n + dist p (c 0) + 1`, minimizing lengths are at least `n+1`, and all Lipschitz constants are exactly `1`. The actual compact-unit-sphere subsequence, exponential continuity, exact subsegment distances, and moving-point Busemann limit prove the construction. All three public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalibratedCoray.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalibratedCoray`: exit 0, zero warnings/errors (11s leaf). New leaf/note/own root import only, explicit-path commit. The last assertion of the book lemma, smoothness of the actual distance support near contact, is not asserted by this leaf: it requires the nonconjugacy and unique-minimizing-segment distance-germ argument. That proof is next, not a named interface.

- 2026-09-06 (Codex, `f7da05c2b`, task 3 distance germ): new `Geometry/Topology/DistanceGerm.lean` proves `tendsto_minimizing_vectors_of_unique` and `contMDiffAt_dist_of_unique_minimizing_exp`, the local distance-expression step in the last paragraph of `lem:cgs-coray-support`. Any selected family of actual minimizing exponential vectors converges at an endpoint with a unique minimizing vector. A nonzero nonconjugate unique minimizing vector therefore identifies actual distance with the smooth inverse-branch radius on a neighborhood. This is a proved implication, with uniqueness and nonconjugacy explicit; the coray application must discharge them, not assume them as an endpoint interface. It generalizes the mathematical proof of `CGTWhiteheadBigon.intrExt_minVec_mem` by duplication in a new owned file, without editing that specialized pullback-metric leaf. No curvature/connectedness assumption or approximation constant is introduced; the germ equality is exact. Both public declarations audited with only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/DistanceGerm.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.DistanceGerm`: exit 0, zero warnings/errors (11s leaf). New leaf/note/own root import only, explicit-path commit. The native `broken_minimizer_velocity_match`, `VolumeComparison.segDom_no_conj`, and `conjVec_reverse` provide the next coray-specific route for eliminating the two geometric conditions.

- 2026-09-07 (Codex, `b8343ef27`, task 3 full coray support): new `Geometry/Topology/CoraySmoothSupport.lean` proves `exists_open_smooth_dist_from_intrinsic_ray`, its pointwise corollary `contMDiffAt_dist_from_intrinsic_ray`, and `exists_smooth_intrinsic_coray_support`, completing `lem:cgs-coray-support`. The final theorem constructs an actual intrinsic unit-speed coray with exact Busemann calibration and, for every `s > 0`, the book's global lower support `b(p) + s - dist(x, alpha(s))`, contact at `p`, and C-infinity regularity on one common open neighborhood. Uniqueness and nonconjugacy are discharged using a length-`2*s` ray segment, `segDom_no_conj`, `conjVec_reverse`, and `broken_minimizer_velocity_match`; no geometric interface remains in this lemma. Hypotheses are native complete positive-dimensional smooth boundaryless compatible metric data, with no curvature or connectedness assumption. Constants: speed/Lipschitz constant `1`, auxiliary extension factor `2`; no approximation loss. Important API distinction: pointwise `ContMDiffAt infinity` alone does not expose a common smooth neighborhood, so the inverse-branch radius and exact minimizing-vector germ are used directly to prove `ContMDiffOn infinity` on an open set. All three public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CoraySmoothSupport.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CoraySmoothSupport`: exit 0, zero warnings/errors (12s leaf), process-count gates respected. Only the new leaf/note and own root import were committed with explicit paths. Next: prove the appendix's sharp smooth-distance Laplacian comparison and apply it to these actual coray supports; the support maximum principle, Ricci splitting, and sphere-separation topology remain genuine proof work, not newly named assumptions.

- 2026-09-07 (Codex, `f50b73119`, task 3 sharp Laplacian comparison): new `Geometry/Topology/SmoothDistanceLaplacian.lean` proves `laplacian_dist_le_of_ricci_nonneg` for `lem:cgs-smooth-laplacian-comparison` / `eq:cgs-laplacian-comparison`, `intrinsic_ray_support_laplacian_ge` for `eq:cgs-support-laplacian`, and `exists_busemann_support_laplacian_gt` for the actual Busemann case of `eq:cgs-calabi-hypothesis`. Two supporting local calculus theorems, `laplacian_sub_of_contMDiffAt` and `laplacian_le_of_smooth_upper_support`, avoid the lower subtraction API's global differentiability hypothesis. The native Jacobi mean and branch trace bound retain `d/tail.ell`, with `d = ((finrank Real E - 1 : Nat) : Real)`; truncations `1/(2*(k+1))` tend to zero and yield the exact `d/dist(p,x)`, not the existing factor-two weakening. The regular-point theorem explicitly assumes actual-distance C-infinity regularity at the evaluation point instead of a cut-locus predicate; the ray and Busemann endpoints discharge it using `CoraySmoothSupport`. The final producer retains a common open C-infinity neighborhood and a global lower-support inequality, with no cut-locus, smooth-support, or Laplacian interface. Native complete positive-dimensional boundaryless compatible metric hypotheses remain; Ricci nonnegativity is the only curvature condition, no connectedness assumption. The explicit time `s = d/epsilon + 1` yields `Delta phi(p) > -epsilon`. All five public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/SmoothDistanceLaplacian.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.SmoothDistanceLaplacian`: exit 0, zero warnings/errors (12s leaf), process gates respected. Explicit-path commit of new leaf/note/own root import only. The Hopf-Calabi maximum principle, Ricci splitting, and sphere separation remain actual proof obligations; no named interface was introduced for them.

- 2026-09-07 (Codex, `c2ef069e5`, task 3 Calabi compact perturbation): new `Geometry/Topology/CalabiMaximumPerturbation.lean` proves `exists_pos_perturbation_lt_on_compact`, `exists_interior_max_of_boundary_perturbation`, and `false_of_positive_laplacian_boundary_perturbation`, the boundary choice and interior-maximum contradiction paragraphs of `lem:cgs-calabi-maximum`. The first two require only a topological space and compactness, not Hausdorffness; compact subtype restriction handles the closed nonnegative-perturbation locus. The coefficient is `(m - max_S f)/(max B 0 + 1)` in the nonempty case, and `1` otherwise. At the interior maximum `z`, choose support error `epsilon = delta * Delta h(z)/2`; pointwise positive Laplacian suffices, no uniform lower bound is assumed. The geometric contradiction uses native boundaryless smooth metric data and local C-infinity lower supports, as supplied by the actual Busemann producer; it is not yet the book's full C2-support maximum principle. An explicit perturbing function is an argument of this proved analytic lemma, not a named interface. Its chart-polynomial and positive-Laplacian exponential construction remain actual next work. All three public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalabiMaximumPerturbation.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalabiMaximumPerturbation`: exit 0, zero warnings/errors (11s leaf), after the other lane's Surgery/Extinction build ended. One own worker and process gates respected; new leaf/note/own import only, explicit-path commit.

- 2026-09-07 (Codex, `cd5df10d7`, task 3 explicit Calabi polynomial): new `Geometry/Topology/CalabiPhase.lean` defines the actual polynomial `calabiPhase v a x = a*inner(v,x) - norm(x)^2 + inner(v,x)^2` and proves `calabiPhase_zero`, `calabiPhase_contDiff`, `calabiPhase_fderiv_unit`, and `exists_calabiPhase_negative_on_sphere`, the Euclidean content of `eq:cgs-calabi-rho` in `lem:cgs-calabi-maximum`. For unit `v`, the directional derivative is exactly `a`; on compact `V` in the radius-`r` sphere omitting `r*v`, the maximum height `k < r` gives `a = (r-k)/2 > 0` and strict negativity on all of `V` (empty case `a = 1`). No finite dimension, curvature, completeness, or manifold hypothesis is needed for these pure inner-product-space facts. This is polynomial separation of a compact sphere subset, not the topological embedded-sphere separation theorem. No interface remains in the polynomial step; actual chart transport, cutoff extension, exponential positivity, and connectedness still remain for the maximum principle. All four theorems audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalabiPhase.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalabiPhase`: exit 0, zero warnings/errors (9.1s leaf), process-count gates respected, one own worker. Explicit-path commit of new leaf/note/own root import only.

- 2026-09-07 (Codex, `1f5823a42`, task 3 exponential barrier): new `Geometry/Topology/CalabiExponential.lean` proves `laplacian_exp_mul_sub_one`, exactly `eq:cgs-calabi-exponential`, and `exists_positive_laplacian_exponential`, the compact coefficient choice in `lem:cgs-calabi-maximum`. For an actual globally smooth phase whose gradient is nonzero on compact `K`, let `m = min_K |grad rho|^2 > 0` and `A <= Delta rho` on `K`; `lambda = (max(-A,0)+1)/m` makes the exponential barrier's Laplacian positive everywhere on `K` (empty case `lambda = 1`). No curvature, completeness, or connectedness assumption is needed; the compact argument uses native boundaryless Hausdorff finite-dimensional smooth metric data. Actual chart transport and cutoff extension still must produce the input phase; no named interface asserts their existence. Both declarations audited: only propext/Classical.choice/Quot.sound. Final serial `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalabiExponential.lean`: exit 0, empty output. Final serial `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalabiExponential`: exit 0, zero warnings/errors (initial leaf compile 15s; final repeat up-to-date). Coordination correction: a subsequent focused check had initially been dispatched while the first build completion acknowledgment was pending; this did not establish the one-worker protocol, so the focused check and targeted build were repeated serially with explicit completion and both process counts zero before the final build. No collaborator process was stopped. Only the new leaf/note and own root import were committed, using explicit paths.

- 2026-09-07 (Codex, `53c14d97e`, task 3 actual compact smooth extension): new `Geometry/Topology/CompactSmoothExtension.lean` proves `exists_contMDiff_extension_near_compact`, the cutoff globalization needed for the local phase in `lem:cgs-calabi-maximum`. A scalar function C-infinity on an open neighborhood of compact `K` is extended to a globally C-infinity function with equal full germs at every point of `K`; no regularity outside the input open set is assumed. Mathlib's smooth closed-set separation gives a cutoff one near `K` and zero near the complement. Hypotheses: finite-dimensional Hausdorff normal sigma-compact smooth manifold, no curvature/completeness/boundarylessness assumption. No numerical approximation constant or extension interface remains. Public theorem audited: only propext/Classical.choice/Quot.sound. Final serial `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CompactSmoothExtension.lean`: exit 0, empty output. Final targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CompactSmoothExtension`: exit 0, zero warnings/errors (8.8s leaf); an earlier build-only multi-goal warning was fixed by specifying the zero function's type, followed by renewed audit/check/build. Explicit completion and process gates respected before the next worker. New leaf/note/own root import only, explicit-path commit. Actual chart-phase transport and connectedness still remain for the support maximum principle.

- 2026-09-07 (Codex, `69ebb0e18`, task 3 actual chart barrier): new `Geometry/Topology/CalabiChartPhase.lean` proves `gradient_calabiPhase_chart_ne_zero` and `exists_calabi_boundary_perturbation_of_chart`, constructing the actual chart perturbation in `lem:cgs-calabi-maximum` from `eq:cgs-calabi-rho` and `eq:cgs-calabi-exponential`. A genuine centered C-infinity chart, a compact coordinate ball, and a prescribed nonmaximum sphere point give a compact manifold region and a globally smooth function zero at the center, negative on the boundary maximum set, and with positive Laplacian throughout the region. The chart differential's actual continuous linear equivalence transfers the nonzero polynomial derivative; `CompactSmoothExtension` preserves full germs and `CalabiExponential` supplies positivity. No new chart/phase existence interface is introduced. Constants remain `a = (r-k)/2`, directional derivative `a`, and `lambda = (max(-A,0)+1)/m`. Hypotheses: boundaryless Hausdorff normal sigma-compact finite-dimensional smooth metric context, finite-dimensional inner-product coordinate space; no curvature, completeness, or connectedness assumption. The original model needs only a normed-space structure. Both declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalabiChartPhase.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalabiChartPhase`: exit 0, zero warnings/errors (15s leaf), serial completion and process-count gates respected. New leaf/note/own root import only, explicit-path commit. Next consumer must construct the centered chart, choose a nonmaximum point from nonopenness of the maximum set, and apply connectedness; the full C2-support formulation remains distinct from the current C-infinity-support route.

- 2026-09-07 (Codex, `30f93cdb3`, task 3 actual smooth-support maximum principle): new `Geometry/Topology/CalabiMaximum.lean` proves `eq_of_smooth_lower_support_at_global_max`, the C-infinity-support case of `lem:cgs-calabi-maximum`. The centered Euclidean chart is constructed from the native extended chart, translation, and a finite-dimensional continuous linear equivalence; no inner-product structure on the original model norm is assumed. Nonopenness of the maximum set produces an actual nonmaximum coordinate point, radius, and direction; the proved chart barrier and compact perturbation contradiction establish openness, and preconnectedness finishes. No maximum-principle, harmonicity, chart, or barrier-existence interface remains. Exact scope: the supported function is continuous, the lower supports are locally C-infinity with `Delta phi > -epsilon`; the book's broader C2-support formulation still requires a separate regularity-conversion proof and is not claimed. The existing actual Busemann supports satisfy this proved version. Hypotheses: boundaryless Hausdorff normal sigma-compact preconnected finite-dimensional smooth metric data, no curvature/completeness/positive-dimension assumption. Coordinate radius is halved; polynomial/exponential/perturbation constants are inherited exactly, with no new loss. Public theorem audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CalabiMaximum.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CalabiMaximum`: exit 0, zero warnings/errors (16s leaf), serial completion and process gates respected. Explicit-path commit of new leaf/note/own import only. Next: the zero sum of opposite Busemann functions; its differentiability, coray uniqueness, Ricci splitting, and sphere separation remain further proof work.

- 2026-09-07 (Codex, `d1171c7e8`, task 3 opposite Busemann sum): new `Geometry/Topology/OppositeBusemann.lean` proves `opposite_busemann_sum_nonpos` and `opposite_busemann_sum_eq_zero`, corresponding to `eq:cgs-opposite-sum-nonpositive` and `eq:cgs-opposite-busemann-zero` in `lem:cgs-opposite-busemann-sum`. The first uses only the triangle inequality for an actual metric line; the second adds the actual smooth lower supports with errors epsilon/2 and applies the proved smooth-support maximum principle. Hypotheses for zero sum: complete compatible positive-dimensional boundaryless smooth Riemannian manifold, sigma compactness, preconnectedness, and nonnegative Ricci curvature. No smoothness of the original metric line, harmonicity, or support/max-principle interface is assumed. Differentiability, unit gradient, unique coray, smooth concatenated line, Ricci splitting, and sphere separation remain further proof work. Both declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/OppositeBusemann.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.OppositeBusemann`: exit 0, zero warnings/errors (16s leaf). Explicit serial completion and process gates respected. **Commit-boundary incident:** although only the two owned leaf paths and root file were selected, the root file had acquired five collaborator import lines (AncestryCore, EssentialClass, CanonicalClass, DiskVariation, Backward); those imports were inadvertently included with the owned import. No collaborator source/note was committed or edited by this lane. The user was informed immediately after verification of the commit contents. An attempted guarded correction stopped before mutation because collaborator commit `e6be1e337` had advanced the branch; no history, index, or working-tree content was rewritten. Future root-import commits must stage only the exact owned hunk in an isolated index and use an atomic expected-parent check, never commit the entire shared root file.

- 2026-09-07 (Codex, `c7bccd5ac`, task 3 Busemann differentiability): new `Geometry/Topology/BusemannDifferentiability.lean` proves `mdifferentiableAt_of_support_sandwich`, `gradientFun_eq_of_differentiable_lower_support`, `opposite_busemann_mdifferentiable`, and `opposite_busemann_gradient_neg`. These close the differentiability and contact differential step of `lem:cgs-opposite-busemann-sum`, `eq:cgs-support-sandwich`, `eq:cgs-sandwich-differential`, and the sign identity only of `eq:cgs-opposite-gradients`. The scalar gap has a local minimum and zero first derivative; first-order little-o domination proves differentiability in the actual extended chart, with no Taylor/elliptic-regularity input. Generic sandwich: boundaryless C1 manifold, differentiable touching supports; no continuity hypothesis on the supported function is needed. Actual Busemann consumers retain the complete compatible positive-dimensional boundaryless sigma-compact preconnected nonnegative-Ricci smooth context of the zero-sum theorem. The supports are taken at time one, with no constant loss and no new geometric interface. Unit gradient, uniqueness/concatenation of corays, Hessian vanishing, Ricci splitting, and sphere separation remain further proof work. All four public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/BusemannDifferentiability.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.BusemannDifferentiability`: exit 0, zero warnings/errors (22s leaf); serial completion and process gates respected. Commit built in an isolated index, checked to contain exactly the new leaf/note and one owned root-import line, then installed with an atomic expected-parent check. Shared index synchronized only for owned paths/import; no collaborator content included. Windows detail: feed the import patch as explicit UTF-8/LF through redirected standard input; the ordinary PowerShell text pipeline appends CR and makes Git patch context fail.

- 2026-09-07 (Codex, `bf14e5c6d`, task 3 actual coray gradients): new `Geometry/Topology/CorayGradient.lean` proves `gradient_intrinsic_ray_distance_support`, `gradient_busemann_eq_of_calibrated_intrinsic_ray`, and `opposite_busemann_gradient_unit`. The first identifies the actual lower distance-support gradient with the unit ray's initial vector; the second identifies every calibrated intrinsic coray's initial vector with the differentiable Busemann gradient; the third closes the unit-norm assertion in `eq:cgs-opposite-gradients`, completing that equation with the prior sign identity. Reverse the specified minimizing segment and compare actual differentiable distance with the previously constructed direction-preserving smooth upper support. No cut-locus or gradient-estimate interface is assumed. Hypotheses for the first two: complete compatible positive-dimensional boundaryless sigma-compact smooth Riemannian data, no curvature/preconnectedness; the actual opposite-Busemann producer adds preconnectedness and Ricci nonnegativity and uses the proved differentiability. Constants: reversal factor `-s` and normalization `1/s` cancel exactly for every `s > 0`; the Busemann consumer takes `s = 1`. All three declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/CorayGradient.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.CorayGradient`: exit 0, zero warnings/errors (22s leaf); serial completion and process-count gates respected. Isolated-index commit with exactly the new leaf/note and one owned import, atomic expected-parent check; no collaborator content included. Next: actual all-real-time calibrated intrinsic line and unique-coray endpoint, then Hessian vanishing/splitting and sphere separation.

- 2026-09-07 (Codex, `2d7d69f7c`, task 3 unique corays and actual calibrated line): new `Geometry/Topology/BusemannLine.lean` proves `existsUnique_calibrated_intrinsic_ray`, `opposite_busemann_unique_corays`, and `opposite_busemann_gradient_line`, closing the remaining unique-coray/concatenation assertions of `lem:cgs-opposite-busemann-sum` and `eq:cgs-line-calibrated-at-p`. Actual corays are constructed, their initial vectors are the opposite Busemann gradients, and native scaling identifies their two halves. Calibration holds at every real time; it and the two exact unit-Lipschitz bounds give a full real-line isometry. The endpoint explicitly includes global smoothness, native geodesic equation, and the basepoint. Hypotheses match the earlier complete compatible positive-dimensional boundaryless sigma-compact preconnected nonnegative-Ricci context; the original metric line need not be assumed smooth. The generic unique-coray theorem uses pointwise Busemann differentiability and no curvature/preconnectedness, while the actual consumers obtain differentiability from its proved producer. Reversal factor -1, both Lipschitz constants 1, exact calibration, no interface left in these assertions. All three declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/BusemannLine.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.BusemannLine`: exit 0, zero warnings/errors (22s leaf). Earlier target attempts were deferred by nonzero Lake counts; no unrelated workers stopped, and explicit serial completion respected. Isolated-index commit: new leaf/note and one owned import only, atomic expected-parent check. The horospherical Hessian limit, geodesic affinity/smoothness, Ricci splitting, and sphere separation remain further proof work.

- 2026-09-07 (Codex, `ab69abebb`, task 3 approximate-support convexity): new `Geometry/Topology/ApproximateSupportConvexity.lean` proves `convexOn_of_approximate_lower_support`, the exact C2 statement `lem:cgs-approximate-support-convexity`. For a continuous function on any convex subset of the real line, touching C2 lower supports with second derivative greater than `-epsilon` for every positive epsilon imply convexity. No differentiability of the supported function, manifold, or curvature assumption is added. The proof is duplicated from the closest private native real-variable argument as required by lane ownership; no lower file is generalized. At a violated chord point `y` between `a` and `b`, choose `delta = (f(y)-chord(y))/(2*(y-a)*(b-y))`; the perturbation has second derivative `2*delta`, contradicting the second derivative test at the actual interior maximum. No interface remains. Public theorem audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/ApproximateSupportConvexity.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.ApproximateSupportConvexity`: exit 0, zero warnings/errors (15s leaf). Earlier target attempts deferred by nonzero Lake counts; final process gates and serial completion respected. Isolated-index commit contains exactly the new leaf/note and one owned root import, with atomic expected-parent installation. The distinct broader C2 Hopf-Calabi maximum-principle formulation is still not claimed by this real-variable convexity result.

- 2026-09-07 (Codex, `85d383a39`, task 3 proved local Hessian support order): new `Geometry/Topology/SupportHessianOrder.lean` proves `hessFun_sub_diagonal_on`, `hessFun_neg_diagonal_on`, `hessFun_le_of_smooth_upper_support`, and `hessFun_add_nonpos_of_zero_contact`, the actual local comparison steps behind `eq:cgs-hessian-monotone` and `eq:cgs-opposite-hessian-bound`. Test arbitrary tangent vectors on native intrinsic geodesics and use the existing local second-derivative/Hessian identity and the real second-derivative test. Common open C-infinity neighborhoods are retained. No curvature/preconnectedness hypothesis or new interface is added. The native testing-geodesic route requires complete compatible positive-dimensional boundaryless sigma-compact smooth Riemannian data; completeness/positive dimension are implementation restrictions for these local helpers, satisfied by the book application. Exact subtraction and negation, no numerical loss. All four public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/SupportHessianOrder.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.SupportHessianOrder`: exit 0, zero warnings/errors (15s leaf); process gates and explicit serial completion respected. The isolated-index commit contains exactly the new leaf/note and one owned import and was atomically installed. The shared-index synchronization was initially refused by an existing zero-byte `.git/index.lock`; no lock was removed or bypassed. On the owner's resume instruction the lock was already absent. The two owned files were verified byte-for-byte against HEAD and synchronized, together with only the SupportHessianOrder import hunk. All 39 collaborator root imports and their staged files were preserved. The working files and committed tree remain intact. The Hessian limit is not yet claimed.

- 2026-09-07 (Codex, `089d0d2ea`, task 3 actual line-distance supports): new `Geometry/Topology/LineDistanceSupport.lean` defines the actual `lineDistanceSupport` of `eq:cgs-line-distance-supports`. Eleven theorems are checked: `lineDistanceSupport_mono`, `lineDistanceSupport_on_line`, `lineDistanceSupport_reverse_on_line`, `lineDistanceSupport_opposite_sum_nonpos`; `exists_open_smooth_lineDistanceSupport`, `exists_open_smooth_reverse_lineDistanceSupport`; `lineDistanceSupport_laplacian_ge`, `reverse_lineDistanceSupport_laplacian_ge`; `lineDistanceSupport_hessian_mono`, `reverse_lineDistanceSupport_hessian_mono`; and `lineDistanceSupport_opposite_hessian_nonpos`. These prove the common-open smoothness and both-family `eq:cgs-hessian-monotone` and `eq:cgs-opposite-hessian-bound` for the actual native unit-speed minimizing line. Metric assertions need only an isometry; geometric assertions use complete compatible positive-dimensional boundaryless sigma-compact smooth Riemannian data with no preconnectedness assumption. Only the Laplacian bounds add Ricci nonnegativity. Constants are exactly `-(n-1)/(R-s)` and `-(n-1)/(S+s)` with precise one-sided endpoint inequalities, no loss or geometric interface. Definition plus all eleven theorems audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/LineDistanceSupport.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.LineDistanceSupport`: exit 0, zero warnings/errors (16s leaf); earlier nonzero-Lake attempts deferred, final gates passed and all own workers explicitly completed serially. The shared index lock was already absent on resume; no lock was removed or bypassed. The unchanged Lean source was landed after the recorded successful checks. The isolated-index commit contains exactly the new leaf/note and its one root import, installed with an expected-parent check; collaborator staging was preserved. SupportHessianOrder synchronization and its status record are complete (`a660d7855`). Next mathematical frontier remains the actual Hessian limit, local uniform convergence, and Bochner/Riccati zero-limit proof; native candidates and a possible quantitative positive-form Cauchy estimate are recorded in `LineDistanceSupport.md`, not claimed as proved.

- 2026-09-07 (Codex, `9fa4a1d59`, task 3 actual Hessian limits): new `Geometry/Topology/HorosphereHessianLimit.lean` proves four public declarations. `exists_lineDistanceSupport_hessian_limits` constructs both finite symmetric bilinear limits of the actual native line-distance supports, from diagonal monotonicity/boundedness and polarization. `exists_lineDistanceSupport_opposite_hessian_limits` proves `eq:cgs-opposite-hessian-limits`: the limits are negatives and have zero metric trace in every genuine orthonormal basis. `exists_lineDistanceSupport_hessian_limit_rate` proves exact component errors `(n-1)/(R-s)` and `(n-1)/(R+s)`. `exists_lineDistanceSupport_hessian_limits_locally_uniform` proves actual `TendstoUniformlyOn` on every `[-A,A]`, in any choice of metric-orthonormal bases, hence also a parallel orthonormal frame. This closes finite limits and local uniformity inside `lem:cgs-horosphere-hessian-zero`, but NOT the vanishing assertion `eq:cgs-hessian-limit-zero`. The finite-limit theorem needs no curvature; the other three add nonnegative Ricci. All use complete compatible positive-dimensional boundaryless sigma-compact smooth Riemannian data and an actual native unit-speed minimizing line, with no preconnectedness or new interface. Quantitative alternative to the book's Dini step: `Lplus-H_R_plus` is positive semidefinite, its trace is at most `(n-1)/(R-s)`, and every orthonormal coefficient is bounded by that trace; both errors are at most `(n-1)/(R-A)` on `[-A,A]`. No limiting-continuity hypothesis is inserted. Important native distinction: `Operator.traceFun` is a coordinate-basis sum, not generally the metric trace; the proof instead uses `lap_eq_hess_on` and an actual orthonormal basis. All four endpoints audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/HorosphereHessianLimit.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.HorosphereHessianLimit`: exit 0, zero warnings/errors (23s leaf). Process gates and serial completion respected. Isolated-index commit contains exactly the new leaf/note and one owned root import; no lower file changed. Next: actual distance eikonal identity on common open neighborhoods, then Bochner/Riccati and zero-limit rigidity.

- 2026-09-07 (Codex, `8f0822cef`, task 3 actual eikonal input): new `Geometry/Topology/DistanceEikonal.lean` proves `gradient_dist_normSq_eq_one`, `gradient_const_sub_dist_normSq_eq_one`, `exists_open_lineDistanceSupport_eikonal`, and `gradient_lineDistanceSupport_on_line`, the actual geometric inputs to `eq:cgs-riccati-trace`. Native Hopf--Rinow gives a minimizing exponential vector at any differentiability point away from the center; the specified smooth upper support and contact-gradient identity give its normalized terminal velocity, whose squared metric norm is exactly one. The line-support producer retains a common open smoothness neighborhood with the eikonal identity at every point, not just along the line. The line gradient is exactly the intrinsic line velocity, by shifting the already proved coray calculation. No curvature, preconnectedness, nonconjugacy assumption, or new interface is used. Hypotheses are the native complete compatible positive-dimensional boundaryless sigma-compact smooth metric context; constants are exactly one and a cancelling normalization by the positive segment length. All four public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/DistanceEikonal.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.DistanceEikonal`: exit 0, zero warnings/errors (22s leaf), with process gates and explicit serial completion. Isolated-index commit contains exactly the leaf/note and its one root import; no lower file changed. The Riccati trace identity, integrated Hessian estimate, and zero-limit rigidity remain next; `LineSupportRiccati.md` records the native smooth-germ/Bochner route.

- 2026-09-07 (Codex, `755658d25`, task 3 actual Riccati and energy): new `Geometry/Topology/LineSupportRiccati.lean` proves five public declarations. `bochner_eikonal_on` transfers native Bochner through a global smooth germ of the actual locally smooth function and kills the squared-gradient Laplacian on its open eikonal neighborhood. `hasDerivAt_lineDistanceSupport_laplacian` proves `eq:cgs-riccati-trace` with the actual scalar Laplacian derivative and metric-weighted `chartHessFrobeniusSq`. `continuousOn_lineDistanceSupport_hessianNorm` and `lineDistanceSupport_hessianNorm_nonneg` supply actual continuity and nonnegativity before the endpoint. `integral_lineDistanceSupport_hessianNorm_le` proves `eq:cgs-hessian-L2` by the one-sided FTC comparison applied to minus the Laplacian. Only the integrated inequality needs nonnegative Ricci; its endpoint condition is merely `a ≤ b < R`, weaker than the book's endpoint slack, and its constant is exactly one. The line hypotheses are the native complete compatible positive-dimensional boundaryless sigma-compact smooth metric context with a unit-speed minimizing intrinsic line; no preconnectedness, global smoothness of the distance support, derivative-integrability input, or geometric interface is added. All five endpoints audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/LineSupportRiccati.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.LineSupportRiccati`: exit 0, zero warnings/errors (19s leaf), process gates passed, own workers completed serially. The note records the scalar-tangent `@Eq ℝ` fix and the local little-o normalization at the real-module FTC boundary; no global instance was changed. Isolated-index commit contains exactly the new leaf/note and one owned root import. Next: use the zero trace limits for a quantitative vanishing energy bound, then prove the actual Hessian limit is zero; `eq:cgs-hessian-limit-zero` remains unclaimed.

- 2026-09-07 (Codex, `8d9e09931`, task 3 vanishing energy): new `Geometry/Topology/HessianEnergyDecay.lean` proves four actual producers between `eq:cgs-hessian-L2` and `eq:cgs-hessian-limit-zero`. `lineDistanceSupport_laplacian_nonpos` uses monotonicity and the already constructed trace-free limit in a genuine metric-orthonormal basis. `tendsto_lineDistanceSupport_laplacian_zero` squeezes the actual Laplacian between `-(n-1)/(R-s)` and zero. `lineDistanceSupport_hessian_energy_bounds` proves the explicit bound `0 ≤ integral_[a,b] |H_R|² ≤ (n-1)/(R-b)` for `a ≤ b < R`. `tendsto_lineDistanceSupport_hessian_energy_zero` gives full real-parameter energy convergence, not just a subsequence. Hypotheses are unchanged complete compatible positive-dimensional boundaryless sigma-compact smooth metric data, nonnegative Ricci, and an actual unit-speed minimizing intrinsic line; no preconnectedness, limiting tensor, or integrability interface is added. All four public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/HessianEnergyDecay.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.HessianEnergyDecay`: exit 0, zero warnings/errors (28s leaf); process gates passed and own workers explicitly completed serially. Only the new leaf/note and one owned root import were committed through the isolated-index expected-parent protocol. Energy decay is NOT yet pointwise Hessian vanishing. Next, `HorosphereHessianZero.md` records the local positivity route: a positive finite-support diagonal persists locally in a smooth vector field and for every later endpoint, contradicting the actual energy decay via tensor Cauchy--Schwarz. This supplies the integral-to-pointwise step without assuming limiting continuity or replacing Ricci nonnegativity by sectional nonnegativity.

- 2026-09-07 (Codex, `31530b375`, task 3 actual horospherical rigidity): new `Geometry/Topology/HorosphereHessianZero.lean` closes `lem:cgs-horosphere-hessian-zero` / `eq:cgs-hessian-limit-zero` together with `LineDistanceSupport`'s actual open smoothness. Three public declarations: `lineDistanceSupport_hessian_nonpos` proves every finite positive support Hessian is nonpositive along the line; `tendsto_lineDistanceSupport_hessian_zero` proves both actual Hessian families converge pointwise to zero on all tangent-vector pairs for the full real endpoint parameter; `tendstoUniformlyOn_lineDistanceSupport_hessian_zero` proves both families converge uniformly to zero on every `[-A,A]` in any actual metric-orthonormal bases, hence in a parallel orthonormal frame. The integral-to-pointwise step is proved, not assumed: extend a putatively positive diagonal vector to an actual smooth field, use support smoothness and endpoint monotonicity to preserve positivity locally, and use native tensor Cauchy--Schwarz to force `(b-a)c^2 ≤ C^2 integral |H_S|^2`, contradicting the proved energy decay. Here only proof-local `c = B(R,s)/2 > 0` and `C = |G(s)|+1 > 0` appear. The nonpositive limiting form has zero metric trace and is therefore zero; the opposite limit is its negative. This is a local-positivity version of the book's continuity/Fatou argument, with unchanged complete compatible positive-dimensional boundaryless sigma-compact smooth metric hypotheses, nonnegative Ricci, and an actual unit-speed intrinsic minimizing line. No preconnectedness, stronger sectional-curvature sign, limiting-continuity hypothesis, or new interface is added. All three public endpoints audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/HorosphereHessianZero.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.HorosphereHessianZero`: exit 0, zero warnings/errors (34s leaf); process gates passed, own workers completed serially. Only the new leaf/note and one owned root import were committed through the isolated-index expected-parent protocol, preserving collaborator staging. Next: `lem:cgs-busemann-affine` / `eq:cgs-busemann-hessian-zero` using the actual calibrated line through each point, the proved support Hessian limits and approximate-support convexity; then smooth normal-coordinate affinity and product splitting. The full Ricci two-ends and sphere-separation theorems, terminal-time compactness, and Chapter 24-dependent canonical-model endpoints remain separate, unclosed work.

- 2026-09-07 (Codex, `5d47dd6c7`, task 3 geodesic affinity): new `Geometry/Topology/BusemannAffinity.lean` proves four public declarations for the geodesic part of `lem:cgs-busemann-affine`. `exists_busemann_support_hessian_gt` constructs actual globally lower supports, smooth near contact with exact equality there and Hessian diagonal greater than any prescribed `-epsilon`; its endpoint is chosen from the actual zero-Hessian limit along the gradient-calibrated line. `busemann_comp_geodesic_convex` and `opposite_busemann_comp_geodesic_convex` compose these supports with a full smooth native geodesic and use the actual second-derivative/Hessian identity and approximate-support convexity. `busemann_comp_geodesic_affine` proves the exact full-time formula `b(c(t)) = b(c(0)) + t * (b(c(1))-b(c(0)))` from convexity of both opposite functions. The test geodesic need not be unit speed or globally minimizing; all full intrinsic geodesics and their subintervals are covered. The input metric line need not be assumed smooth. Native hypotheses are complete compatible positive-dimensional boundaryless sigma-compact smooth metric data, preconnectedness, and nonnegative Ricci; no geometric or regularity interface is inserted. The affine formula has no error or added constant. All four declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/BusemannAffinity.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.BusemannAffinity`: exit 0, zero warnings/errors (26s leaf); gates passed and own workers completed serially. Isolated-index commit contains only the leaf/note and one owned import. This does NOT yet assert manifold smoothness or `eq:cgs-busemann-hessian-zero`. Next new leaf `BusemannSmooth` uses the existing C-infinity `stdBranch.fixedPD` exponential inverse, rather than the older C1 exponential chart, to prove the normal-coordinate affine formula, actual smoothness, and zero Hessian.

- 2026-09-07 (Codex, `c8c1f2ba7`, task 3 Busemann regularity): new `Geometry/Topology/BusemannSmooth.lean` closes the full `lem:cgs-busemann-affine` with the previous geodesic-affinity leaf. `busemann_expMapIntrinsic_affine` proves `eq:cgs-normal-coordinate-affinity` for every tangent vector under completeness, not just a normal ball; the coefficient is the already proved actual differential, identified through the scalar curve chain rule. `busemann_contMDiff` uses the native C-infinity `stdBranch.fixedPD` inverse to prove actual smoothness. `busemann_hessian_eq_zero` obtains diagonal vanishing from the native geodesic second derivative identity and full bilinear vanishing by symmetry/polarization. `opposite_busemann_smooth_hessian_zero` proves smoothness and zero actual Hessian for both ends, `eq:cgs-busemann-hessian-zero`. Hypotheses remain complete compatible positive-dimensional boundaryless sigma-compact smooth Riemannian data, preconnectedness, nonnegative Ricci, and an actual metric line; no stronger sectional sign, smoothness assumption on the input line, extra tangent-bundle separation assumption, new interface, or geometric constant is added. All four declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/BusemannSmooth.lean`: exit 0, empty output. Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.BusemannSmooth`: exit 0, zero warnings/errors (26s leaf, 9204 jobs), run through the external `E:/testdifferential-geometry/scripts/lake-locked.ps1` wrapper from the dev cwd with `-NoLakeLock -LeanThreads 1`, after the active Soul task explicitly confirmed an exclusive window. Process gates passed; the completed window was released and the peer notified. No source was copied between checkouts. Isolated-index commit contains only the new leaf/note and one owned import. Next is the general `lem:cgs-affine-function-splitting`: actual complete gradient flow, regular zero hypersurface, and global isometric product/inverse, all in new files. These, the full Ricci two-ends/sphere-separation consumers, terminal-time compactness, and Chapter 24-dependent endpoints are not claimed by this landing.

- 2026-09-07 (Codex, `86b73e4f7`, task 3 complete affine gradient flow): new `Geometry/Topology/AffineFunctionFlow.lean` proves the gradient-flow and set-bijection parts of `lem:cgs-affine-function-splitting`, not its full metric product conclusion. `cov_gradient_eq_zero_of_hessian_eq_zero` derives the actual parallel gradient without completeness or unit norm. `affineGradientFlow` / `_zero` use the existing full intrinsic geodesic with initial gradient; `hasDerivAt_affineFunction_flow` / `affineFunction_flow_eq_add` prove the exact derivative 1 and all-real-time shift `eq:cgs-flow-shifts-busemann`. The proof uses the native second-derivative/Hessian identity, so it needs no general bounded-vector-field extension or parallel-transport interface. `affineGradientFlow_velocity` identifies actual velocity with actual gradient using their unit norms and scalar product 1; `_isMIntegralCurve` supplies Mathlib's native global integral-curve predicate; `_add` supplies the exact flow law by native uniqueness. `affineFunctionZeroLevelEquiv` is the actual underlying bijection in `eq:cgs-affine-product-map`, with inverse `x -> (flow(x,-b(x)),b(x))`. Hypotheses are precisely a smooth unit-gradient, zero-Hessian function on the native compatible complete positive-dimensional boundaryless sigma-compact smooth Riemannian manifold; preconnectedness and curvature signs are unnecessary for these conclusions. The normalization constants are 1 and 0, with no errors or new named interfaces. All nine public declarations audited: only propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFunctionFlow.lean`: exit 0, empty Lean output (20.2s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFunctionFlow`: exit 0, zero warnings/errors (18s leaf, 3904 jobs). Checks/build used the external shared wrapper from the dev cwd with `-NoLakeLock -LeanThreads 1`. Soul's agreed exclusive build/audit window was respected and explicitly released; before this build that task was idle/completed, with its claims released, no other workers or elaboration/build locks, and the binding process gates passed. Isolated-index landing contains only this new leaf/note and one own root import, preserving Soul's intervening commit and all unrelated edits. Remaining in the splitting lemma: actual joint flow smoothness/time-slice diffeomorphisms, preservation of the metric, the regular zero hypersurface with induced metric, product isometry and completeness/connectedness of the factor. The note identifies the native compact-orbit/local-flow route for smooth dependence and the actual `DifferentialGeometry/Topology/Morse/LevelSet.lean` chart API. Full Ricci splitting/two-ends, sphere separation, terminal-time compactness and the Chapter 24-dependent model consumers remain unclosed.

- 2026-09-07 (Codex, `e93308e96`, task 3 affine-flow regularity): new `Geometry/Topology/AffineFlowRegularity.lean` proves six public declarations for `lem:cgs-affine-function-splitting` / `eq:cgs-affine-product-map`. `affineGradientFlow_contMDiff` identifies the existing explicit intrinsic gradient flow with native complete integral curves by uniqueness, then reuses Soul's newly landed `contMDiff_curveAt_joint` (`57b358b85`); the general smooth-dependence proof is not duplicated. `affineGradientFlow_slice_contMDiff` and `affineGradientFlowDiffeomorph` give actual smooth time slices and their negative-time inverses. `affineFunctionZeroLevelHomeomorph` upgrades the existing explicit product bijection to a homeomorphism with the book's inverse; `affineFunctionZeroLevel_connectedSpace` proves connectedness of the factor when M is connected. `affineFunctionZeroLevel_completeSpace` proves only completeness for the ambient subtype metric, under continuity of b; this is not yet induced Riemannian completeness. The other hypotheses remain the native compatible complete positive-dimensional boundaryless sigma-compact smooth metric context, actual smooth unit gradient and actual Hessian zero. No curvature sign, extra constant, smooth-dependence assumption or named interface is added. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFlowRegularity.lean`: exit 0, empty Lean output (13.5s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFlowRegularity`: exit 0, no warnings/errors (10s leaf, 4118 jobs). Fresh-import audit of all six public declarations: only propext/Classical.choice/Quot.sound (12.3s). Checks used the external shared wrapper from the dev cwd with `-NoLakeLock -LeanThreads 1`, after Soul explicitly released its exclusive window; fresh shared status/locks and process gates passed, own workers ran serially. The isolated-index commit contains only the new leaf/note and one own root import. Remaining: actual metric preservation, regular zero hypersurface with induced metric, global smooth isometric product and induced-metric factor completeness; full Ricci splitting/two-ends, sphere separation, terminal-time compactness and Chapter 24-dependent endpoints are not asserted.

- 2026-09-07 (Codex, `39df2807c`, task 3 actual isometric flow): new `Geometry/Topology/AffineFlowIsometry.lean` closes the flow-isometry step of `lem:cgs-affine-function-splitting`. `affineGradientFlow_differential_parallel` proves the actual time-slice differential is parallel along each orbit, using the smooth variation `flow(exp_p(s*v),t)`, native torsion-free covariant-derivative commutation, actual flow velocity, and the already proved parallel gradient. The variation field's actual total-space smoothness supplies chart differentiability. `affineGradientFlow_preserves_metric` applies native metric compatibility to the moving-base inner product and fixes the constant at time zero. `affineGradientFlow_isometry` proves actual ambient distance preservation from the path-length infimum in both directions; `affineGradientFlowIsometryEquiv` packages the same maps as the actual time-slice diffeomorphism, with inverse at negative time. The short path-infimum proof is duplicated locally, not generalized in the lower dimension-three surgery consumer. Hypotheses remain the native compatible complete positive-dimensional boundaryless sigma-compact smooth metric context with actual smooth unit gradient and zero Hessian; no curvature sign, assumed variation equation, parallel transport, isometry interface or new constant is added. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFlowIsometry.lean`: exit 0, empty output (16.8s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFlowIsometry`: exit 0, no warnings/errors (14s leaf, 4119 jobs). All four public declarations freshly imported and audited: only propext/Classical.choice/Quot.sound (15.5s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; the resumed Soul task explicitly confirmed an exclusive refresh/audit window and all process/lock gates passed. Isolated-index commit contains only the new leaf/note and one own root import. Next is the actual zero-level hypersurface atlas/induced metric and smooth isometric product. Live inspection found `Morse/RegularSublevel` requires analytic-order `IsManifold I (top : WithTop ENat) M`; do not strengthen the book's C-infinity hypothesis to consume it. New `AffineFunctionNormalForm` will instead prove general zero-Hessian geodesic affinity and the actual C-infinity exponential kernel normal form. Full Ricci splitting/two-ends, sphere separation, terminal-time compactness and Chapter 24-dependent endpoints remain unclosed.

- 2026-09-07 (Codex, `ac5baf0c2`, task 3 affine normal form): new `Geometry/Topology/AffineFunctionNormalForm.lean` proves six public declarations for the regular-level step of `lem:cgs-affine-function-splitting` and the mechanism of `eq:cgs-normal-coordinate-affinity`. `affineFunction_differential_surjective` gives the explicit scalar preimage `a * grad b`; `affineFunction_kernel_finrank` proves kernel dimension plus one equals ambient dimension. Neither needs completeness or boundarylessness. `affineFunction_comp_intrinsicGeodesic` proves the exact affine formula along every complete intrinsic geodesic from zero actual Hessian and identifies its slope with the actual initial differential; no unit speed, minimizing property, unit gradient or curvature sign is needed. `affineFunction_expMapIntrinsic` specializes it to the full exponential map. `affineFunction_normalCoordinate_formula` and `_level_iff` identify the actual level through p with the actual differential kernel on the existing C-infinity fixed exponential inverse branch. Only the native compatible complete positive-dimensional boundaryless sigma-compact smooth metric context is used for full geodesics; no analytic manifold hypothesis or regular-level interface is added. Normalizations are gradient squared norm 1 for surjectivity/codimension and Hessian 0 for affinity; there are no errors or new constants. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFunctionNormalForm.lean`: exit 0, empty output (16.2s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFunctionNormalForm`: exit 0, no warnings/errors (13s leaf, 3940 jobs). All six public declarations freshly imported and audited: only propext/Classical.choice/Quot.sound (14.7s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; Soul's intervening refresh window was respected, and a separate explicit exclusive window was obtained for this leaf's build/audit. Gates passed, own workers ran serially. Isolated-index commit includes only the leaf/note and one own import. Next `AffineZeroLevelCharts` will assemble the actual subtype's C-infinity atlas from the proved normal form, using a reference differential kernel and continuous linear identifications of the codimension-one kernels. The general embedded-slice definition belongs to the active Soul lane and will not be duplicated. Induced metric, global smooth product/isometry, full Ricci two-ends/sphere separation, terminal-time compactness and Chapter 24 consumers remain unclosed.

- 2026-09-07 (Codex, `3ba0ac17d`, task 3 actual zero-level hypersurface): new `Geometry/Topology/AffineZeroLevelCharts.lean` proves thirteen public declarations for the regular-level step of `lem:cgs-affine-function-splitting`. The carrier is the actual subtype `b^{-1}(0)` with its existing subspace topology; the common model is the actual differential kernel at a reference level point. The actual exponential logarithm, kernel projection and continuous linear kernel identifications construct open partial homeomorphisms, all inverse/domain laws and smooth coordinate transitions. `affineZeroLevelChartedSpace` and `affineZeroLevel_isManifold` assemble its C-infinity atlas; `affineZeroLevel_inclusion_contMDiff` and `affineZeroLevel_corestrict_contMDiff` prove actual inclusion and smooth factorization without assuming regular-level or factorization interfaces. `affineZeroLevel_isEmbeddedSlice` also proves the same subset satisfies the Soul lane's native `IsEmbeddedSlice` predicate with dimension exactly `finrank Real E - 1`, reusing `4145f96d6` rather than duplicating that hierarchy. Hypotheses remain the native compatible complete positive-dimensional boundaryless sigma-compact smooth metric context and a smooth unit-gradient zero-Hessian function. No analytic-order manifold hypothesis, curvature sign, error constant or new geometric interface is added. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineZeroLevelCharts.lean`: exit 0, empty output (29.2s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineZeroLevelCharts`: exit 0, no warnings/errors (27s leaf, 3942 jobs). All thirteen declarations freshly imported and audited: only propext/Classical.choice/Quot.sound (20.4s). External shared wrapper from dev cwd with `-NoLakeLock -LeanThreads 1`; Soul was live-confirmed idle/completed at revision 18 after its explicit release. Fresh gates passed and own workers ran serially. Isolated-index landing contains only the new leaf/note and one own root import. Next is the actual global smooth product using the already proved joint flow and new smooth corestriction. The induced metric, metric product identity, induced-metric factor completeness, full Ricci two-ends/sphere separation, terminal-time compactness and Chapter 24 consumers remain unclosed.

- 2026-09-07 (Codex, `bbbda18ad`, task 3 actual smooth product): new `Geometry/Topology/AffineFunctionProduct.lean` proves ten public declarations for `eq:cgs-affine-product-map` in `lem:cgs-affine-function-splitting`. `affineZeroLevelRetraction` is the actual `flow(x,-b(x))` in the actual zero-level subtype; its evaluation, fixed-point identity and smoothness are proved using the exact flow shift and the preceding corestriction theorem. `affineFunctionZeroLevelDiffeomorph` upgrades the existing explicit set equivalence to an actual global C-infinity diffeomorphism, with the exact flow and retraction/function inverse formulas. Differentiating the actual retraction identity gives `affineZeroLevel_inclusion_mfderiv_leftInverse` and `_injective`; differentiating the actual zero-level equation gives `_mvfderiv_eq_zero`. Thus the forthcoming induced metric consumes proved inclusion smoothness, immersion and tangency, not new interfaces. Hypotheses remain the native compatible complete positive-dimensional boundaryless sigma-compact smooth metric context with actual smooth unit gradient and zero Hessian. No curvature sign, analytic regularity, new error constant or added geometric hypothesis is used. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFunctionProduct.lean`: exit 0, empty output (25.5s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFunctionProduct`: exit 0, no warnings/errors (21s leaf, 4123 jobs); the named build also refreshed SoulFlow and AffineFlowRegularity. Fresh-import audit of all ten declarations: only propext/Classical.choice/Quot.sound (20.4s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; fresh gates passed and Soul remained live-confirmed idle/completed at revision 18 with released claims. Own workers were serial. Isolated-index commit contains only the new leaf/note and one own import. This proves a smooth product, not a distance isometry for the default Cartesian maximum metric. Next is the actual induced smooth metric and the Riemannian product inner-product formula, then induced-metric completeness. Full Ricci two-ends/sphere separation, terminal-time compactness and Chapter 24 consumers remain unclosed.

- 2026-09-07 (Codex, `7368312a1`, task 3 actual Riemannian product identity): new `Geometry/Topology/AffineZeroLevelMetric.lean` proves seven public declarations for `lem:cgs-affine-function-splitting`. `affineZeroLevelMetric` constructs the actual smooth induced metric along the actual inclusion, using its proved differential injectivity for positivity and native finite-dimensional positive-form boundedness; this includes zero-dimensional factors. Its smoothness proof reuses native tangent-map/bundle evaluation machinery and the existing `localPullInner`, with a private proof in the new leaf rather than changing the lower local-diffeomorphism API. `_inner` gives exact evaluation; `_inclusion_orthogonal_gradient`, `affineGradientFlow_preserves_differential` and `_flow_orthogonal_gradient` prove initial and transported orthogonality from actual db and the exact flow shift. `affineFunctionZeroLevelDiffeomorph_mfderiv` computes the full differential of the actual global product diffeomorphism; `_preserves_product_metric` proves `Phi^*g((v,a),(w,c)) = g_N(v,w) + a*c` for all pairs, with cross terms zero and real-line coefficient exactly 1. Hypotheses remain native compatible complete positive-dimensional boundaryless sigma-compact smooth ambient metric data and a smooth unit-gradient zero-Hessian function; no factor-positive-dimension, stronger curvature, immersion or metric-preservation input is added. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineZeroLevelMetric.lean`: exit 0, empty output (22.7s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineZeroLevelMetric`: exit 0, no warnings/errors (16s leaf, 4129 jobs), also refreshing AffineFlowIsometry. Fresh-import audit of all seven declarations: only propext/Classical.choice/Quot.sound (17.2s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; fresh gates passed and Soul remained live-confirmed idle/completed at revision 18 with released claims. Own workers were serial; isolated-index commit contains only the new leaf/note and one own import. Next is identification of the induced Riemannian distance with the ambient subtype distance and induced-metric completeness, via the actual norm-nonincreasing retraction and path-length infima. The full Ricci splitting/two-ends and sphere-separation consumers, terminal-time compactness and Chapter 24 consumers are not claimed by this landing.

- 2026-09-07 (Codex, `ee82269c6`, task 3 induced factor completeness): new `Geometry/Topology/AffineZeroLevelCompleteness.lean` proves five public declarations completing the metric-factor part of `lem:cgs-affine-function-splitting`. `affineZeroLevelRetraction_metric_decomposition` differentiates the actual inverse product map and proves `g(v,v) = h(dr(v),dr(v)) + db(v)^2`; `_metric_le` gives exact contraction constant 1. Mapping actual C1 paths by inclusion and retraction proves `affineZeroLevelMetric_edist_eq`: the actual induced Riemannian distance equals the ambient subtype distance. `_isRiemannianManifold` registers genuine native compatibility; `_complete` proves the native `RiemannianMetricComplete` predicate using the induced emetric structure and its closed isometric inclusion into complete M. This is not merely a completeness claim for an unrelated subtype metric. The full earlier actual atlas, connectedness, smooth product and bilinear metric identity now complete the general affine-function splitting chain. Hypotheses remain the native complete compatible positive-dimensional boundaryless sigma-compact smooth ambient context, smooth b, unit gradient and zero Hessian; no connectedness is needed for this leaf, no curvature sign or extra interface is added, and all comparison constants are exactly 1. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineZeroLevelCompleteness.lean`: exit 0, empty output (21.5s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineZeroLevelCompleteness`: exit 0, no warnings/errors (18s leaf, 4130 jobs). Fresh-import audit covered all five declarations plus actual connectedness, embedded-slice, diffeomorphism and product-metric endpoints: only propext/Classical.choice/Quot.sound (15.4s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; fresh gates passed, Soul remained live-confirmed idle/completed at revision 18 with released claims, and own workers were serial. Isolated-index commit contains only the new leaf/note and one own import. Next is the assembled book-facing affine splitting endpoint with its reference zero-level point constructed rather than assumed, followed by marked Busemann specialization and actual curvature inheritance. The full Ricci Cheeger--Gromoll theorem, two-ends/sphere separation, terminal-time compactness and Chapter 24 consumers are not yet asserted.

- 2026-09-07 (Codex, `0c2e1c8e3`, task 3 general affine splitting CLOSED): new `Geometry/Topology/AffineFunctionSplitting.lean` proves the assembled native endpoint `affineFunction_splitting` for the complete `lem:cgs-affine-function-splitting` / `eq:cgs-affine-product-map`, checked against current `master05a.tex` lines 5987--6048. From native complete connected compatible positive-dimensional boundaryless sigma-compact C-infinity ambient data and an actual smooth unit-gradient zero-Hessian function, it constructs a reference zero-level point internally and proves the actual zero level is connected, an embedded hypersurface of exact codimension one, and complete for its actual induced smooth metric. It supplies the actual global smooth product diffeomorphism with the exact flow map and retraction/function inverse, and proves the full bilinear pullback identity `Phi^*g = h + dt^2`. No level-point, atlas, immersion, isometry, completeness, curvature sign or analytic-order regularity interface is assumed. The coefficient is exactly 1 and the cross terms exactly zero. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/AffineFunctionSplitting.lean`: exit 0, empty output (14.3s). Targeted `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.AffineFunctionSplitting`: exit 0, no warnings/errors (14s leaf, 4131 jobs). Fresh-import audit of the assembled endpoint: only propext/Classical.choice/Quot.sound (12.8s). External shared wrapper from dev cwd, `-NoLakeLock -LeanThreads 1`; fresh gates passed, Soul remained live-confirmed idle/completed at revision 18, own workers were serial. Isolated-index commit contains only the new leaf/note and one own import. Next prioritize the actual at-most-two-ends consequence needed by this lane, using the already proved two-ends metric line, smooth unit Busemann function and product-end dichotomy. The full marked Ricci splitting theorem additionally needs factor curvature inheritance; that separate assertion is not claimed here. Sphere separation, terminal-time compactness and Chapter 24 consumers remain open.

- 2026-09-07 (owner scope override): continue Chapter 25 without implementing Chapter 24. Accurately state missing Chapter 24 and earlier upstream theorems, with actual hypotheses and book labels, as explicit `sorry` obligations and leave their proofs to the collaborator. Only already-near-complete upstream proofs should be finished here; the assembled Ricci end-count consequence is the current exception, not a mandate for further factor-curvature or appendix work. This supersedes the old appendix-first/no-sorry directives and the requirement to finish all terminal compactness infrastructure before Chapter 25 work. Keep Chapter 25's own bounded-curvature-at-distance, terminal-bound, first-backward-slab and ancient-extension arguments separate from upstream obligations: `SelectedSequenceEventuallyGood` bundles both and must not be relabelled as a pure Chapter 24 gap. Report consumers as conditional whenever an upstream `sorryAx` remains. `HANDOFF_CODEX.md` now records this binding boundary.

- 2026-09-07 (Codex, `e4e487ac3`, near-complete upstream exception CLOSED): `Geometry/Topology/RicciTwoEnds.lean` proves `hasAtMostTwoEnds_of_nonnegative_ricci` and `hasExactlyTwoEnds_of_nonnegative_ricci`, the end-count conclusions of `thm:cgs2e-two-ends`. Actual two-end metric line, smooth unit affine Busemann data, the actual connected zero-level product homeomorphism and the compact/noncompact product end dichotomy close the proof, with no splitting or ends interface. The public theorem has the book's complete connected smooth boundaryless nonnegative-Ricci hypotheses and native sigma-compact/Hausdorff context; dimension zero is proved internally. No noncompactness, orientation or dimension-three hypothesis is required. Counts are exactly 2 and 3, with no geometric constant. Focused `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Topology/RicciTwoEnds.lean`: exit 0, empty output (52.4s). Named `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Topology.RicciTwoEnds`: exit 0, no warnings/errors (18-second leaf, 9264 jobs). Fresh-import audit of both publics: propext/Classical.choice/Quot.sound only (18.1s). External wrapper, serial single-threaded checks, fresh process gates and Soul's explicitly confirmed exclusive build/audit window; root/leaf/audit claims and window released. One isolated-index code commit with only leaf/note/own import. Per the new owner boundary, now return to Chapter 25; no factor-curvature or new appendix campaign. Sphere separation's nonseparating-sphere covering argument, terminal compactness and Chapter 24 consumers are not claimed.

- 2026-09-07 (Codex, `cbcb0b2c8`, authorized upstream STATEMENT, not proof): new `UpstreamModelCurvature.lean` states `chapter23_modelCurvatureBoundNearBase`, the existing exact `ModelCurvatureBoundNearBase` with explicit dimension 3, boundaryless convention and positive kappa. One `sorry` is deliberately left for the collaborator under the latest owner directive. Quantifiers: one K >= 0 before every native ancient model normalized by R(p,0)=1; rmNormSq <= K^2 on the actual closed h(0)-ball of radius 3 over [-4,0]. Book source is the fixed-window consequence of `thm:ksol-fixed-kappa-compactness`, not literally the old shorthand `thm:ksol-universal-derivative-estimates` (which is a same-point curvature-scale bound). Native ancient-model identification with `def:red-kappa-solution` still belongs upstream. Focused `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/UpstreamModelCurvature.lean`: exit 0, 34.1s, exactly one expected sorry warning, NOT empty output. Named `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UpstreamModelCurvature`: exit 0, 16-second leaf, same warning, no errors. Fresh-import audit (20.2s): propext/sorryAx/Classical.choice/Quot.sound. No proof completion is claimed. One isolated-index leaf/note/own-import commit. External wrapper, serial one-thread checks, fresh gates and Soul-confirmed exclusive refresh; window and aggregate/audit claims released. The Chapter 25 closed-open derivative-to-propagation consumer is source-written and awaits its focused check; Chapter 24 has not been touched.

- 2026-09-08 (Codex, `3f320f319`, Chapter 25 closed-open local propagation): new `ClosedOpenPropagation.lean` supplies `exists_goodPointBoundsOn_closedOpen_of_modelBound` and `exists_closedOpenLocalPropagation_of_modelBound` for `lem:scn-good-point-derivatives`, `lem:scn-local-propagation`, `eq:scn-local-propagation-cylinder` and `eq:scn-local-propagation-bound`. It consumes the existing Chapter 23 fixed-window model-curvature bound, without the older stronger arbitrary-interval derivative interface. Actual native three-dimensional boundaryless source flows on [0,T), IsSolutionOn, admissible Phi, epsilon in (0,1/4], pinching and higher-curvature goodness remain explicit; the entire window is in the regular interval, and source completeness is not needed. Constants: epsilonStar = 1/4; c = 1/(20(CStar+1)), 0 < c <= 1/20; tensor coefficient 4 sqrt 3. The actual cylinder has radius c/sqrt L and depth c/L, with -6 Phi(0)/Q <= Rbar <= 4L and |Rmbar| <= 4 sqrt 3 (L + (Phi(4QL)+Phi(0))/Q). CStar is chosen before all source manifolds/flows; its inherited formula in terms of the model K and native uniform Shi constants is recorded in the leaf note. Focused `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/ClosedOpenPropagation.lean`: exit 0, empty output, 21.0s before the pause; unchanged source. Named `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedOpenPropagation`: exit 0, 103-second leaf, 11445 jobs, no leaf diagnostics; replayed the one expected UpstreamModelCurvature sorry warning. Fresh-import split audit (42.3s) confirms only propext/Classical.choice/Quot.sound on both input-explicit producers, and additionally sorryAx on `exists_closedOpenLocalPropagation`, solely through the authorized upstream Chapter 23 adapter. This last consumer is conditional, not a proved endpoint. No own Chapter 25 finite-horn, cone-exclusion or ancient-extension argument was moved into an upstream obligation. External wrapper from dev cwd, one thread, serial own workers; other lanes recorded paused/completed, exclusive named refresh recorded in WORKING_STATUS.md and fresh process/lock gates checked. Isolated-index landing contains only leaf/note/one own import. The latest owner Markdown/scripts-first coordination rule is also recorded in HANDOFF_CODEX.md. Chapter 24 remains untouched.

- 2026-09-08 (Codex, `3c5559344`, exact parabolic witness transport CLOSED): new `WitnessParabolicTransport.lean` proves `rescaledMetric_paraSolution`, the actual `KappaModelWitness.parabolic` and `.ofParabolic` constructions, and `isGoodPoint_paraSolution_iff` / `isOrientedGoodPoint_paraSolution_iff`. These are the goodness-invariance step of `lem:scn-recentered-source-bound` at `eq:scn-recentered-flow`, with `def:scn-kappa-model-witness` and `def:scn-good-bad-points`. Q/A normalization after an A-rescaling equals the original Q-normalized smooth metric family at every real time. The entire admissible backward window is transported, not just the base time. Both directions retain the identical ancient model, embedding, finite-jet comparison and existing abstract orientation datum. Hypotheses: native finite-dimensional complete model-space smooth source context, arbitrary actual SolutionOn interval, A > 0 and an admissible recentering time. No dimension-three, curvature, PDE, source completeness, source T2/sigma-compactness or new orientation API assumption is added. Epsilon and kappa are unchanged, with no tolerance loss or auxiliary constant. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/WitnessParabolicTransport.lean`: exit 0, empty output, 107.4s. Named `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessParabolicTransport`: exit 0, 35-second leaf, 10548 jobs, no warnings/errors. All five public declarations freshly imported and audited (42.3s): only propext/Classical.choice/Quot.sound. No sorry, remaining interface or Chapter 24 dependency in this leaf. External shared wrapper, one-thread serial workers and Markdown-recorded exclusive window; isolated-index commit contains only leaf/note/one own root import. This is not the full recentered-source-bound proof: next assemble its actual recentered source inputs, while finite-horn/cone exclusion and terminal/ancient compactness remain open.

- 2026-09-08 (Codex, `a93572f50`, recentered source inputs CLOSED, full curvature bound OPEN): new `RecenteredSourceInputs.lean` proves eight declarations for the source-verification paragraph of `lem:scn-recentered-source-bound`, `eq:scn-recentered-B`, `eq:scn-recentered-flow` and the transported `eq:scn-higher-curvature-good`. `recenterScale_bounds` gives the strict thresholds for B=max(A+1,3). `paraTime_mem_recenteredWindow` maps the entire [-B(H+s),0] interval into [-H,0]; `recenteredDepth_ge_half` and `tendsto_recenteredDepth` prove B(H+s)>=BH/2 and divergence uniformly over moving times in the upper half. `rescalePinchingFunction_rescale` and `recentered_noncollapse_scale` give the exact double-scaling identities Phi_(BQ) and sqrt(BQ)*sigma. `isGoodPoint_recentered_of_two_le` transports actual higher-curvature witnesses; `recenteredSource_inputs` assembles the normalized anchor Rtilde(w,0)=1, its actual model witness, the admissible full window, all higher-curvature witnesses, geometric pinching and spatial tensor noncollapsing. Hypotheses: native smooth SolutionOn on an arbitrary actual interval, B>2, a source slab inside its carrier, source pinching/noncollapsing and threshold-2 goodness, and an actual B-level anchor. No source PDE, dimension-three, completeness, new orientation or model-curvature input is added; source T2/sigma-compactness is confined to the geometric assembly. Epsilon/kappa are unchanged; depth coefficient is 1/2 and scale factors are exact. Finding the B-level anchor on a counterexample path, producing the quantitative derivative buffer, finite-horn/cone exclusion and C(A,D) remain separate obligations, not new upstream assumptions. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/RecenteredSourceInputs.lean`: exit 0, empty output, 36.3s. Named `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceInputs`: exit 0, 30-second leaf, 10549 jobs, no warnings/errors. Fresh audit of all eight declarations (30.3s): only propext/Classical.choice/Quot.sound. No sorry or named geometric interface in this leaf. Soul resumed during this work; its explicit exclusive-window confirmation and our request/acceptance/release were exchanged only through WORKING_STATUS.md, with actual wrapper locks and fresh process gates. Serial one-thread verification; one isolated-index code commit with only leaf/note/own import, then this separate log commit. All own claims and the window released after landing. Scope reminder from the current book: `rem:scn-finite-horn-endpoint-status` explicitly keeps seven finite-end theorem cards distinct and untranslated; these are Chapter 25 obligations and must not be hidden inside the deferred Chapter 24 canonical-tuple theorem. Native neck/cap/collar vocabulary is still absent, so no competing Chapter 24 hierarchy was introduced. Next work should keep the terminal cone calculation and these finite-horn obligations separate from the collaborator's geometric vocabulary.

- 2026-09-08 (ownership correction and first Chapter 23 landing): the owner clarified that Chapters 22, 23 and 25 belong to this task; Chapter 24 remains external. The supplied old branch at fbf766dc1 has substantial Chapter 22/P2 work but no dedicated Chapter 23 compactness implementation, so the active lane is now `../KappaSolutions/KAPPA_COMPACTNESS_PLAN.md`. `SpatialPointSelection.lean` proves the full `lem:ksol-spatial-point-selection`, `eq:ksol-pointpick-escape` and `eq:ksol-pointpick-control` for the actual scalar curvature and Riemannian distance. Five public declarations, constants `r_i <= 1/2`, `R <= 4 Q_i`, and all required divergences; no new interface or positive-dimension assumption. Final focused check empty (19.4s), named leaf build clean (16s / 3929 jobs), fresh five-declaration audit standard axioms only (16.9s). Source was included in the externally advanced shared commit `05b77506c`; own scoped registration/note commit `be71d3264`. The guard stopped before any unintended commit, verified source identity and preserved shared history. Full declaration-to-label, hypotheses, command and ownership evidence is in the Chapter 23 plan and same-name note. The Chapter 23 model-curvature bound remains an explicit sorry: point selection alone is not fixed-kappa compactness. Existing Chapter 25 obligations and the Chapter 24 boundary remain unchanged.

- 2026-09-09 (`78c82ccd4`, analytic support for `lem:scn-cone-terminal-exclusion`): TerminalJetLimits proves finite uniform-Cauchy jet identification, left-endpoint time-Cauchy control, and an actual terminal metric-coefficient consumer. Four public theorems, standard-only in fresh audit2 (16.96s); focused3 EMPTY (17.74s), named1 clean (22.55s). Receipts: `E:/lean-tools/chapter25-terminal-local-20260909/`. This proves the identification step with explicit Cauchy input, not its flow-dependent production or the cone obstruction. Serial one-thread verification in the explicit Chapter25 03:30--04:30 window; own import only. The remaining source-written terminal/ray leaves in section9.6 are being verified separately.

- 2026-09-09 (`f80b2cf53`, compact bounds for `lem:scn-cone-terminal-exclusion`): TerminalCarrierBounds derives two-sided metric comparison from carrier continuity and positive definiteness on the compact reference unit tangent set, then bounds the actual moving curvature via fixed-norm continuity and tensor comparison. Both public theorems are standard-only in fresh audit1 (17.47s); focused7 EMPTY (20.67s), named1 clean (23.42s), receipts in the same external directory. No terminal jet or derivative bound is assumed. Expected-type elaboration of the norm-continuity composition timed out even at800000 heartbeats; inferring the composition first and normalizing Function.comp_apply checks at the default limit. No option override remains. Own import only; same serial exclusive window. Sliding Shi/local-buffer production is next.

- 2026-09-09 (`690f56b19`, local analytic input for `lem:scn-cone-terminal-exclusion`): TerminalLocalBounds proves two-way fixed spatial-buffer capture, actual fixed-duration shifted Shi control, and one relatively compact neighborhood with all moving curvature derivative bounds as regular times approach the terminal slice. Its five public theorems are standard-only in fresh audit1 (31.16s); focused3 EMPTY (33.80s), named1 clean (53.11s/11407 jobs). The original flow is not assumed complete or regular at its endpoint; only an auxiliary reference metric uses completeness to choose a compact ball. All native Shi applications stay strictly inside regular times. Receipts: `E:/lean-tools/chapter25-terminal-local-20260909/`. Fixed-background covariant/time control and actual terminal Ricci RHS continuity are still separate obligations; no Chapter25 cone slot closed yet. Shared claim242fa631 retained for other owned files; own import only and serial window unchanged.

- 2026-09-09 (`40290984b`, fixed-background input for `lem:scn-cone-terminal-exclusion`): TerminalCovariantBounds adapts native arbitrary-order covOrder_Ico_tail and actual solnTowerSwap_reg to a relatively compact open region. Moving Ricci bounds come from the checked curvature tower trace, initial bounds from compactness, and metric comparison from the closed carrier slab. Two public theorems standard-only in fresh audit1 (31.48s); focused2 EMPTY (33.01s), named1 clean (47.70s/11408 jobs), same external receipts. The local producer uses an actual earlier flow slice as its reference metric and bounds every order on one compact neighborhood over a half-open time interval. No endpoint regularity or original-flow completeness added. The full terminal RHS and cone theorem are still open. Own root import only; claime3639bad released after landing.

- 2026-09-09 (`dd3733053`, time control for `lem:scn-cone-terminal-exclusion`): TerminalMetricTimeControl proves uniform time Lipschitz control of every actual fixed-background metric derivative on one local compact neighborhood. The proof uses native ric_bound_const and timeLipschitz_of_hasDerivAt, with actual evolution only at strict regular times; its local producer derives all comparison/curvature inputs from the original flow. Two public theorems standard-only in fresh audit1 (30.60s); focused2 EMPTY (32.99s), named1 clean (50.82s/11409 jobs). Same external receipts and serial exclusive window. Claim5f027595 released after landing. Actual coordinate terminal convergence is being checked next; the Ricci RHS and cone slot remain open.

- 2026-09-09 (`2a4dd851a`, actual terminal Gram jets for `lem:scn-cone-terminal-exclusion`): TerminalChartJets proves solution_chartGram_jets_tendsto_terminal from the original IsSolutionOn closed-carrier/open-regular slab assumptions. One fixed chart neighborhood works for every spatial derivative order, with uniform convergence of actual Gram coefficients to the actual terminal metric's jets. The checked carrier/local/covariant/time chain supplies its inputs; no terminal regularity, flow completeness, chosen limit metric or Cauchy hypothesis is added to this endpoint. Fresh endpoint audit1 standard-only (30.74s); focused2 EMPTY (31.89s), named1 clean (47.34s/11411 jobs). Same external receipts; own root import only. Claimea0f667a released. This settles this flow's terminal metric jets, not the cross-model common-map spacetime convergence interface. Actual Ricci/Hessian RHS convergence is next, and cone_terminal_exclusion remains open.

- 2026-09-09 (`23ba4921e`, actual terminal Ricci jets for `lem:scn-cone-terminal-exclusion`): TerminalRicciJetOperators proves native jet2 stability, same-chart Christoffel/Ricci smooth convergence, and full-family actual terminal Ricci-jet convergence uniformly on compact subsets of one common chart neighborhood. The proof consumes the checked terminal Gram endpoint, uses native finite-jet formulas with chartModelBasis, and recovers the full time filter through the existing sequence criterion. Four public theorems standard-only in fresh audit1 (31.83s); focused4 EMPTY (35.36s), named1 clean (47.96s/11412 jobs). No new filtered composition calculus or terminal regularity assumption. Product properness is assembled from finite-dimensional continuous-linear-map factors to avoid deep Module search. Same external receipts and own root import; claim9e15a5a1 released. Actual Ricci covariant Hessian reconstruction/RHS continuity and cone_terminal_exclusion remain open.

- 2026-09-09 (`4de02c1f9`, finite-horn deep-end quantifier correction): finite_horn_ray_approximation now selects a positive common deep cutoff before the pair/arm data, and EndAngles.monotone supplies a positive pairwise local cutoff. Arbitrary outer extensions need not retain the deep-end connector geometry. Full arms, all cross-connectors and the independent two-variable angle limit remain. Focused1 passed (38.37s) with exactly11 original placeholder warnings; named1 passed (52.27s/10611 jobs), fresh12-public audit1 confirms all original endpoints remain sorryAx-dependent. No horn theorem is counted as closed. EndRayLocality verification and downstream consumer refresh are separate pending steps. Same external receipt directory and shared claim242fa631; no other lane source edit.

- 2026-09-09 (`6218a8ec4`, actual terminal Ricci Hessian): TerminalRicciHessian proves the local-frame formula for one covariant derivative, reconstructs the actual Ricci covariant Hessian from fixed-chart jets, and obtains its tensor/evaluation continuity at the original terminal slice. Three public declarations are standard-only in fresh audit1 (30.65s); focused5 EMPTY (36.50s), named1 clean (50.19s/11419 jobs). Explicit native tensor-basis typing and finite reconstruction preserve the bundle fiber topology; the native model equivalence handles evaluation. No terminal regularity or original-flow completeness added. Same external receipts; source/root commit above, claimde0e884f released. RHS and original cone endpoint are next and remain unverified at this checkpoint.

- 2026-09-09 (`72e9a421f`, actual terminal Ricci evolution): TerminalRicciRHS derives continuity of the full native Ricci evolution expression from actual Hessian continuity and carrier-continuous inverse metric/Ricci/Riemann terms. The original equation therefore extends to the terminal left derivative without an extra continuity, regular-time or completeness premise. Both public theorems are standard-only in fresh audit1 (30.82s); focused3 EMPTY (32.07s), named1 clean (44.62s/11421). Same external receipts, own root import and serial exclusive window. Claimd7ecbf2d released. The original cone contradiction is now being checked; no original slot is counted closed before that verification.

- 2026-09-09 (`d32e339de`, local nonflat-cone obstruction): ConeTerminalExclusion restricts the original flow to the actual open neighborhood returned by ConeChart.exists_concurrentField. Past sectional nonnegativity makes the radial Ricci pairing nonnegative, the terminal cone makes it zero, and its now-proved terminal left derivative equals twice scalar curvature. The local contradiction has no completeness, terminal regularity or source-convergence premise. Focused2 EMPTY (34.19s), named1 clean (48.10s/11515), fresh endpoint audit1 standard-only (31.98s), same external receipts. Claimfd23c318 released; own root import only. The original Chapter25FiniteHorn wrapper is being instantiated and must pass its own verification before its slot is counted closed.

- 2026-09-09 (`00bd34ae3`, original cone slot CLOSED): Chapter25FiniteHorn.cone_terminal_exclusion instantiates the actual local flow theorem with its original closed carrier/open regular interval and existing mathematical assumptions. Focused3 passed (40.33s) with exactly10 remaining original placeholder warnings; named2 passed (55.45s/11519), fresh12-public audit2 (30.78s) makes the original cone endpoint standard-only. All other11 public declarations in that leaf still inherit sorryAx. The unused openness binder is marked _hU, with its premise retained; no existing named-argument calls were found. Same external receipts and shared source242fa631. Original own-slot census is now36/39 remaining (92.3% by slots), with one of the three filled slots still a conditional assembly; see section9.7.

- 2026-09-09 (`e3ca28ebe`, local end-ray representatives): EndRayLocality proves restriction/germ equivalence, comparison-angle control near the endpoint, zero angle iff eventual equality, and the exact quotient-fiber criterion from a given EndAngles package. One definition and eight theorems are standard-only in fresh audit1 (32.00s); focused3 EMPTY (30.18s), same source hash, named1 clean (45.68s/11520). Same external receipts and own root import. This is a checked consumer of local angle data, not an EndAngles/global-tube producer and not another original slot closure. Shared claim242fa631 released after this final leaf; unchanged Extension/Theorems refreshes follow in the same serial window.

- 2026-09-09 (downstream verification after `00bd34ae3` and `e3ca28ebe`): unchanged Chapter25Extension passed focused1 (36.82s, exactly11 original warnings) and named1 (52.12s/11536); unchanged Chapter25Theorems passed focused1 (40.62s, exactly12 original warnings) and named1 (55.79s/11637). Fresh downstream audit1 (31.32s) confirms good-point derivatives, local propagation, ancient extension, countersequence exclusion, abstract model theorem and final canonical-neighborhood assembly all still depend on sorryAx. No whole-chapter closure is claimed. Final source/artifact hashes, exact attempts and audits are reconciled in `E:/lean-tools/chapter25-terminal-local-20260909/cone-completion.json`; all four new leaves passed the forbidden-token scan, and root imports are unique. All own source claims are released; final root/window handback is recorded in WORKING_STATUS.md.

- 2026-09-09 (`18389a1d1`, quantitative path shortening): CollarShortening proves exact concatenation length, the two-crossing lower bound, an actual replacement preserving finite outer pieces with a strict saving, and no-return for every sufficiently nearly minimal path. Four public theorems have focused2 EMPTY (15.84s), named1 clean (25.86s/4075), and fresh audit1 standard-only (17.52s). Receipts: `E:/lean-tools/chapter25-terminal-local-20260909/`. The actual C0/transverse-geometry producer is being checked separately; no original finite-horn card is counted closed. Source/root and this log are separate commits, one compiler/thread in the accepted exclusive window, no other-lane edits.

- 2026-09-09 (`9d073c722`, actual collar metric control): CollarMetricControl proves cross-model upper/lower path-length transport, axial displacement control, actual cylinder C0 curve bounds, and a universal transverse shortcut producer from the compact connected unit round sphere. Its reference-family hypothesis identifies only time zero, covering both the static family in FiniteHorn.cylindrical_tail and the shrinking-cylinder family. Eight public theorems have focused7 EMPTY (41.09s), named1 clean (76.45s/10612), fresh audit1 standard-only (29.88s), same external receipt directory. No complete ambient metric, ambient no-shortcuts, or global tube conclusion is inferred. Native tangent-vector types are retained through product-derivative rewrites; the sphere constant uses the actual intrinsic distance function directly.

- 2026-09-09 (`6bbe4f659`, fixed long-collar shortening): CollarNoReturn proves addition of actual metric length, the two-crossing lower bound for a contained return, and a universal fixed depth yielding a genuine transverse replacement with saving greater than one half of normalized length. The depth is fixed before the error (any error at most one half works); there is no arbitrary-depth precision-times-depth requirement. Three publics have focused1 EMPTY (34.86s), named1 clean (33.16s/10613), fresh audit1 standard-only (21.56s). Same external receipts. Inferring such contained crossings for arbitrary ambient curves remains a first-exit/global-separation obligation, not a conclusion of this leaf.

- 2026-09-09 (`2d19f3b8d`, neck-side repair integrated): user-requested side task supplied actual global product-tube/cross-section data and common closure-buffered whole arms/connectors in Chapter25FiniteHorn. Parent preserved its frozen source SHA1C877A66 and completed named3 (44.23s/11519) after side focused4 (43.96s, only10 original placeholders). Fresh18-public NeckRepair audit1 (23.39s) makes all6 new geometric helpers and the original cone endpoint standard-only; the other11 original publics retain sorryAx. Actual tube/cross-section production is now required of the still-open horn constructor, not assumed delivered. Arbitrary ambient frontier escape remains false from the raw ambient fields. Side source fixture/receipt: `E:/lean-tools/chapter25-neck-side-20260909/`; parent refresh/full audit in the existing external directory. Downstream current-interface verification follows before final handback.

- 2026-09-09 (`358545bae`, actual finite-horn collar consumer): FiniteHornCollar instantiates the fixed-depth theorem with the exact time-constant/scalar-normalized comparison returned by the updated FiniteHorn.cylindrical_tail. Its actual curve stays in a fixed subcollar of any sufficiently long recorded collar, and the replacement stays on the whole central sphere. Focused2 EMPTY (25.11s), named1 passed (34.09s/11522; only earlier replayed placeholders), fresh endpoint audit1 standard-only (22.75s), actual dependency SHA1C877A66. No SigmaCompactSpace premise is needed for this local consumer. The four new own leaves now contribute16 verified public theorems; the original own-slot count remains36/39 unfilled. Current-interface downstream verification is the remaining integration check for this batch.

- 2026-09-09 (final current-horn downstream verification): unchanged EndRayLocality passed focused4 EMPTY (24.09s), named2 (33.51s/11520), and fresh audit2 (22.07s); all nine public declarations remain standard-only. Unchanged Chapter25Extension passed focused2 (28.03s, exactly11 original warnings) and named2 (37.35s/11536); unchanged Chapter25Theorems passed focused2 (29.00s, exactly12 original warnings) and named2 (39.37s/11637). Fresh six-endpoint downstream audit2 (22.51s) confirms that good-point derivatives, local propagation, ancient extension, countersequence exclusion, abstract model theorem and final canonical-neighborhood assembly still depend on sorryAx. All stages use the integrated finite-horn source SHA1C877A66. The four new own leaves'16 public theorems remain standard-only; exact final attempts and source/artifact hashes are reconciled in `E:/lean-tools/chapter25-terminal-local-20260909/collar-completion.json`. This completes this batch's integration checks, not the remaining original Chapter25 arguments. File/root claim release and the explicit early compiler-window return are recorded in WORKING_STATUS.md.

## 5. Terminal-time compactness (scoping result, 2026-09-06; owner decision pending)

Needed by: the bridge from tree convergence to `KappaModelWitness` (closeness up to the terminal slice
`s = 0`), `prop:scn-terminal-limit-global-bound`, `prop:scn-first-backward-slab`,
`prop:scn-ancient-extension`, and Chapter 10's κ-solution limits at time 0.

**Load-bearing uses of "base time interior" in the `compactnessSol` chain** (read-only audit):
`Limits/Hamilton.lean:42-62` needs only `0 ∈ carrier`; `Shi/Local.lean:1468-1478` (`movingShi_open`),
`:1517-1526` (`atZeroGeomOpen`) need `Ioc α ψ ⊆ X.D.regular` with `ψ > 0`; `Shi/Local.lean:677,1044`
(`hpsiReg : ψ ∈ D.regular`, then `exists_Icc_regular` gives strict forward slack) and `:91-139`
(`metric_pde_start`, two-sided `HasDerivAt` at `ψ`) — essential as implemented;
`Fields/CanonicalCompatibility.lean:176-200` needs the whole compact window incl. 0 inside `regular`;
`Fields/Open/Basic.lean:389-395` (`exists_openConv_raw`, `t₀ ∈ Ioo a b`) uses `t₀` only through
`a < t₀ ≤ b`; `CompleteInput`/`CurvBoundInput` (`Foundations/Defs.lean:114-138`) quantify over
`carrier` (fine for `Ioc α 0`); `FlowLimitData.conv` (`Limits/Upgrade.lean:78-88`) already ranges over
`Icc a b ⊆ carrier`, so `b = 0` is admitted. Target-side regularity at a closed right end is cheap:
`MetricFamilySmoothOn` (`Geometry/Metric/Family/Basic.lean:471-491`) needs smoothness only on
`D.regular` and continuity on `D.carrier`; `isSolutionOn_of_reg`, `flowOfMetric`
(`Limits/Construction.lean:40-120`) are `D`-generic. `RealTimeInterval.openClosed α 0 0`
(`Analysis/TimeInterval.lean:443-454`, carrier `Ioc α 0`, regular `Ioo α 0`) is the common interval;
`openWindow a 0 0 n = Icc (a + (0−a)/(n+2)) 0` (`:295-302`) is already the terminal exhaustion.

**Rejected**: shifting the base slice to `−η` (moves `X.atZero`, the static compactness, the injectivity
bound and `FlowLimitData.hL0` to the wrong slice; no uniform `η`); per-term windows (unnecessary:
`Solution/Restriction.lean` `timeRestrict`/`isSoln_timeRestrict` put every member on the common `D`).

**Recommended route (c′) "common terminal interval + per-term forward slack"**, new files only:
1. `Compactness/Foundations/TerminalWindow.lean` (~200): window lemmas under `a < t₀ ≤ b`, `openClosed`
   simp lemmas, `Ioc a 0 = ⋃ n, openWindow a 0 0 n`.
2. `Compactness/Shi/Terminal.lean` (~500): `ForwardSlack X α : Prop` (`∀ i, ∃ c > 0, IsSolutionOn` of the
   member restricted to `openInterval α c 0`, as a `PointedFlowData` with the same `M`/`S.base` — helper
   `PointedFlowData.retime`, `retime_metric` rfl); `CurvBoundInput.movingShi_terminal`,
   `CurvBoundInput.atZeroGeomTerminal` = copies of `Shi/Local.lean:1417-1560` with `ψ := 0`, regularity
   from the slack; constants `shiOpenConst`/`rmOpenBound` are index-independent, so bounds are uniform
   up to and including `t = 0` although the slack is not.
3. `Compactness/Foundations/WindowEquivalenceTerminal.lean` (~120): mirror of `metricEquiv_open`.
4. `Compactness/Fields/Terminal/Upgrade.lean` (~450): mirror of `Fields/CanonicalCompatibility.lean:30-401`
   with `hregular n` from the slack and `hD : X.D = openClosed α 0 0 _`; reuses `exists_openConv_raw`,
   `OpenConvOut.isSolution`.
5. `exists_openConv` with `a < t₀ ≤ b`: the report proposes weakening `ht₀` in `Analysis/TimeInterval.lean`
   and `Fields/Open/Basic.lean`; **this lane will duplicate (~150 lines) instead** — both files sit at the
   bottom of the tree and an edit would trigger a large rebuild cone in the shared checkout.
6. `Compactness/Limits/Terminal.lean` (~120): `compactnessSol_terminal`, same shape as `compactnessSol`
   with `hD : X.D = openClosed α 0 0 _` and `ForwardSlack`; conclusion `SmoothCGHConverges` + completeness
   at every `t ∈ Ioc α 0`.
7. Optional `Compactness/Limits/TerminalDeriv.lean` (~80): one-sided flow equation of the limit at `s = 0`
   (`hasDerivWithinAt_Iic_of_tendsto_deriv`, mirroring the private `deriv_Ici_start`).
Total ≈ 1400–1600 lines, mostly mechanical mirrors. No Chapter 7 brick: the metric's mixed bounds of all
orders already come from `Compactness/Metric/AllTimesBounds.lean` layer inputs and
`Bounds/RicciComponents.lean` `mixed_*`; the only window condition (`regular_on_window`) is met per member
after the parabolic shift.

**Diagonal step** (`Compactness/Limits/Ancient.lean`, ~350): `FlowUpgrade` re-run on each `(α_k, 0]` with
the same `mc` (depends only on `X.atZero`; `L_k.M = mc.limit.M` for all `k`); `flowLimit_agree_on_overlap`
from `conv` at `p = 0` + `limit_inner`/`pullback_inner` (`Foundations/PointedMaps.lean:615-668`) +
`source_exhausts`; `PointedFlowData.glue_Iic` on `infiniteClosed 0 0` via `isSolutionOn_of_reg`; diagonal
subsequence by composition. Risk to check first: whether `metricDerivNormSupOn` is an `sSup` needing a
boundedness side condition before pointwise bounds can be extracted.

**Other risks**: threading the per-term enlarged interval through `movingShi_of_bound` (implicit `D` in
`PointedFlowData D`); `Limits/Regularity.lean` (21 `openWindow` uses) not fully audited for hidden
`0 ∈ Ioo a b` assumptions inside `OpenConvOut.isSolution`.

**Decision requested from the owner**: implement now in this lane (new files under `Compactness/`,
≈ 2 workers × 1 lean.exe, appendix-style), or keep `compactnessSol_terminal` as a named interface and
continue §12.8–12.11 against it.
- 2026-09-06 (W-F landed): `CompactPathAvoidance.lean` — `lem:scn-compact-path-approximation` proved (`exists_partition_eventually_rectifiable_path_avoiding_ball`), pure metric geometry; length-space hypothesis `IsApproxLengthSpace` = for all `v w η`, a `Path v w` with `eVariationOn γ.extend (Icc 0 1) < ofReal (dist v w + η)`; rectifiable = `BoundedVariationOn γ.extend (Icc 0 1)`; upstream candidates `eVariationOn_extend_trans_le`, `dist_start_lt_of_eVariationOn_lt`, `exists_path_of_chain` (move to a metric layer when a second consumer appears). `RemotePointTriangle I` (`lem:scn-remote-point-triangle`) is an interface: no minimizing-ray construction and no Toponogov equal-arm hinge (`eq:top-equal-arm-hinge`) in the tree; wait for the collaborator's comparison theorems. `lem:scn-open-nonnegative-sphere-separation` not stated (embedded-sphere/ends vocabulary absent). Axioms propext/choice/Quot.sound. W-E still running.
- 2026-09-06 (W-G dispatched, `WitnessTransport.lean`): the transport half shared by W-C's `GoodPointDerivativeBounds`, `BlowUpLimitNonnegativeCurvature` and the future convergence→witness bridge. Tree facts found: `Compactness/Bounds/Uniform/CurvatureSupremum.lean` `riemannDiff_gJet_le` (pointwise `|Rm_{g₁}−Rm_{g₂}|_{g₂} ≤ riemannDiffC Λ Λ' Λ''` from `MetricUniformEquivalentOn` + `MetricCovDerivOrderBoundOn` at orders 1, 2; `riemannDiffC → 0` with the jet bounds), first-derivative analogues in `CurvatureJetOne/JetDifference/PalatiniDifference`, restriction to the embedding's source domain via `HCGCompactness.SourceDomain`. W-G: T1 vocabulary bridge from `cm_close` (`∇_h h = 0`, so orders ≥ 1 of `jet 0` and of `F^*ĝ` coincide), T2 Riemann transport, T3 scalar/Rm at the source with explicit constants, T4a `∇R` transport in `scalarDifferential` form, T4b `∂_t R` via the flow equation (stretch). Model half of `GoodPointDerivativeBounds` still waits on closed-end regularity of the ancient model (§5).
- 2026-09-06 (W-E landed): `LocalPropagation.lean` — `lem:scn-local-propagation`: `scalar_le_of_good_locus` (Claim A, unrescaled scale-invariant first-crossing at three levels `2Q → 3QL` spatially, `3QL → 4QL` in time, goodness threshold `2Q` on both legs), `neg_six_mul_phi_zero_le_scalar` (`R ≥ −6Φ(0)`, book constant exact in the tree's convention), `sqrt_rmNormSq_le_of_scalar_le`, `exists_pinching_error_lt` (limit clause), `local_propagation_paraSolution` (the book's rescaled display through `frozenBackwardCylinder`), packaged `exists_local_propagation_constants` with `c = 1/(20(C_*+1))`, `ε₀ = ε_*(κ)`, `C = 2C₃`. Window required in `D.regular` (so the `deriv` that `GoodPointDerivativeBounds` bounds exists). Interfaces: `GoodPointDerivativeBounds` (W-C, consumed unfolded as `GoodPointBoundsOn`); `RmNormLeOfCurvatureOperatorBounds` (dim 3: `|K_j| ≤ a ⟹ |Rm| ≤ C₃ a`, the tree has only the opposite direction; W-C's `RmNormBoundedByScalarCurvature` is its `a = R/2` case); `AlmostMinimizingCurvesOn` (a `C¹` curve of speed `≤ r + η` from the centre to any point of the closed `g`-ball: the geodesic theory is stated for the ambient `riemannianEDist` under `IsMetricNorm g`, not for `riemannianEDistOf g` of a slice metric; `edistOf_iInf` gives the infimum over `C¹` paths but no extraction/reparametrisation). API traps recorded in the note: state `R^{-1/2}`/`R^{-1}` bounds over a plain real or elaboration times out; use `CurveDerivative.hasDerivAt_comp_mfderiv_along` with `realTangentOne`. Axioms propext/choice/Quot.sound. Follow-up W-H: discharge both new interfaces (arclength form from `edistOf_iInf`, crossing lemma integrating the speed; dim-3 eigenbasis expansion `|Rm|² = 4ΣK_j²`).
- 2026-09-06 (W-H dispatched): discharge W-E's two interfaces — Part 1 edits `LocalPropagation.lean`: `AlmostMinimizingCurvesOn` replaced by a proved arclength-form lemma from `Geometry/Metric/DistanceScaling.lean:42` `edistOf_iInf` (valid for every slice metric, no `IsMetricNorm`/completeness), spatial leg of the crossing argument integrates the speed; Part 2 new `RmNormFromEigenvalues.lean`: `RmNormLeOfCurvatureOperatorBounds` proved in dim 3 (`|Rm|² = 4ΣK_j²`, `C₃ = 2√3`) via `DimensionThree/RiemannFromRicci` / Kulkarni–Nomizu, plus the dim-3 instance of `RmNormBoundedByScalarCurvature`. Wiring of the unfolded theorem to the `def` in `LocalPropagation.lean` is the reviewer's one-line step after both build. Running with W-G (2 lean.exe in this lane).
- 2026-09-06 (W-G landed): `WitnessTransport.lean` — restriction mechanism `openPullbackMetric` (`Diffeomorph.pullbackMetric` of `g.restrictOpen` through `PartialDiffeomorph.toOpensDiffeo`, i.e. `ballPullbackMetric` de-specialised; positivity free), bridges `metricCovDeriv_self_eq_zero`, `tensor02CovDeriv_sub_metricTensorField`, `openPullback_metricCovDerivNorm` (`tensor02CovDeriv` and `metricCovDeriv` are the same recursion `metricCovDerivStep`); T1 `modelComparison_metricUniformEquivalentOn` / `modelComparison_metricCovDerivOrderBoundOn` on `witnessWindow`; T2 `modelComparison_riemannOp_sub_sq_le/_norm_le/_norm_le` with `witnessRiemannC ε = riemannDiffC (Λ ε) ε ε ≤ 20ε` for `ε ≤ 1/4`, `→ 0`; T3 `openPullbackMetric_scalar` (pullback invariance of the scalar curvature) and `modelComparison_ricciTensor_sub_le` (`|Ric₁ − Ric₂| ≤ n·witnessRiemannC ε`, basis-free trace). Interfaces (two-metric comparison facts with an explicit constant function): `ScalarCurvatureComparison I scalarC` (scalar = metric trace of Ricci; the tree lacks an inverse-metric/trace comparison under `MetricUniformEquivalentOn`) feeding `modelComparison_scalar_sub_le`; `ScalarGradientComparison I gradC` (T4a; `uniformRmOpOne_of`/`uniformPalatini1_le` are `Set.univ` with merged constants, and `nablaRm_split`/`palatiniJet1At` go through the private `extSec1`/`extSec` of `Compactness/Bounds/Uniform/CurvatureJetOne.lean` — a hard blocker unless that file exposes them; the localized separated-constant ancestors `connectionDifference_gJet_le`, `covDerivConnectionDifference_gJet_le`, `covDConnectionDifference2_gJet_le` exist) feeding `modelComparison_scalarDifferential_sub_le/_le`. T4b named: one missing Laplacian comparison `|Δ_{g₁}f − Δ_{g₂}f|` under equivalence + jet bounds. Proposal (note §7, not applied): carry the witness pullback as a `SmoothRiemannianMetric` on `⟨F.source, _⟩`. Follow-ups deferred until the `_terminal` decision, since the model half of `GoodPointDerivativeBounds` waits on closed-end regularity.
- 2026-09-06 (W-I dispatched, `GoodPointDerivatives.lean`): `lem:scn-good-point-derivatives` with the Chapter 10 input reduced to one interface `ModelCurvatureBoundNearBase I κ` (curvature bound of a normalised ancient κ-solution on the model ball of radius 3 × `[−4, 0]`; the κ-uniformity is `thm:ksol-universal-derivative-estimates`, collaborator's Chapter 10). Route: `ε_* = 1/4` via `isGoodPoint_mono`; W-G's `modelComparison_riemannOp_norm_le` transports the model bound to `|Rm_ĝ| ≤ K₀(n,K)` on the source cylinder; the unprimed Theorem 7.1 (`shi_local_all_orders_curvature_scale_of_solution`) applied to the shifted rescaled source flow `paraSolution S (t − 2/Q) Q` presented on `closedOpen` via `paraInterval_closedOpen_carrier/_regular` + `isSolutionOn_cast` (Cor 7.2's device) gives `|∇Rm|, |∇²Rm|` at the good point; trace + scalar evolution give `GoodPointBoundsOn` after unscaling. This route needs neither the gradient comparison (W-G's `ScalarGradientComparison`) nor closed-end regularity of the model. Deliverable: the `closedOpen 0 T` form of `GoodPointDerivativeBounds` with `ε_* = 1/4`. Running with W-H.
- 2026-09-06 (W-H landed): `LocalPropagation.lean` — `AlmostMinimizingCurvesOn` deleted; `exists_path_lintegral_speed_lt_of_mem_closedBall` proved for every slice metric (`riemannianEDistOf` is Mathlib's `Manifold.riemannianEDist` under `let : RiemannianBundle := ⟨g.toRiemannianMetric⟩`, then `Manifold.exists_lt_locally_constant_of_riemannianEDist_lt` + `pathELength_eq_lintegral_mfderiv_Icc`; needs `attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup/NormedSpace in`), `abs_sub_le_of_hasDerivAt_of_lintegral_le` (integral mean value inequality); the spatial leg integrates the speed, same constants; the packaged theorem no longer mentions curves. `RmNormFromEigenvalues.lean` — `normSq0S_eq_four_mul_sum_sq_orderedSectionalCurvaturesAt` (`|Rm|² = 4ΣK_j²` in any orthonormal frame, via `inner0S_algebraic_eq_four_mul_operatorInner` and Frobenius = ℓ² of eigenvalues by the spectral theorem), `exists_rmNormLeOfCurvatureOperatorBounds` (`C₃ = 2√3`, sharp on round `S³`), `sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg`, `rmNormBoundedByScalarCurvature_of_finrank_three` (`|Rm| ≤ √3 R`; W-C's interface is stated for all dimensions, the theorem carries `finrank = 3`). All five wave-2 leaves now built (targeted build, 1 worker). Remaining interface in `exists_local_propagation_constants`: `GoodPointDerivativeBounds` only (W-I running).
- 2026-09-06 (wiring, `bac4ba56e`): `RmNormFromEigenvalues.lean` now imports `Interfaces`/`LocalPropagation` and provides `rmNormLeOfCurvatureOperatorBounds : RmNormLeOfCurvatureOperatorBounds I` (`C₃ = 2√3`) and `rmNormBoundedByScalarCurvature_dim_three (hdim : finrank = 3) : RmNormBoundedByScalarCurvature I`. `exists_local_propagation_constants` is conditional on `GoodPointDerivativeBounds` only. W-J dispatched: `ModelTheorem.lean`, the endpoint `thm:scn-abstract-model-theorem` stated in the tree's vocabulary with its contradiction skeleton over `eventually_exists_badPointSelected`, against one interface `SelectedSequenceEventuallyGood` standing for the Chapter-11-dependent block (`thm:scn-bounded-curvature-at-distance`, `prop:scn-terminal-limit-global-bound`, `prop:scn-first-backward-slab`, `prop:scn-ancient-extension`, convergence→witness bridge) so that block's exact input is fixed.
- 2026-09-06 (W-J landed): `ModelTheorem.lean` — `thm:scn-abstract-model-theorem` as `exists_modelRadius_of_selectedSequenceEventuallyGood` (`∃ r₀ ∈ (0, √ε]`, `ModelRadiusWorks`: every flow on `closedOpen 0 T` with `ModelFlowHypotheses` (isSolution, `1 ≤ T`, `RiemannianMetricComplete` slices on `Ico 0 T`, scalar bounded above on every `Icc 0 T'` with `T' < T` — the weakest form W-D consumes —, `PhiAlmostNonnegative` on `Ico 0 T`, `SpatiallyKappaNoncollapsedBelowScale κ σ`; `σ` before `r₀` per `rem:scn-fixed-sigma-repair`) and `1 ≤ t₀ < T`, `R(x₀,t₀) ≥ r₀⁻²` has `(x₀,t₀)` `ε`-good), proved from the single interface `SelectedSequenceEventuallyGood I ε κ σ Φ orient` (selected sequences with `depth → ∞`, `Q → ∞`, `∀ᶠ BadPointSelected` are eventually oriented-good) via `r₀(n) = min(√ε, 1/(n+1))`, a bundled `ModelTheoremCounterexample`, and `eventually_exists_badPointSelected`. Finding: the tree's goodness is not oriented (the book's witness carries orientation), so the endpoint concludes plain goodness and orientation sits in the interface's conclusion (`OrientationDatum`, `IsOrientedGoodPoint`; at `trivialOrientationDatum` the interface is literally `∀ᶠ IsGoodPoint`); an oriented endpoint needs an orientation-refined selection lemma (mechanical re-run of W-D). Of the block the interface bundles, only `lem:scn-local-propagation` exists; the rest waits on Chapter 11 and the terminal-time compactness (§5). Traps: `∀ᶠ i, False` is stuck (use `(h₁.and h₂).exists`); `push_neg` deprecated; `letI` in proofs trips `linter.style.haveILetI`. Axioms propext/choice/Quot.sound.
- 2026-09-06 (W-K dispatched, `ScalarComparison.lean`): discharge W-G's `ScalarCurvatureComparison` — `R_{g₁} − R_{g₂} = tr_{g₁}(Ric₁ − Ric₂) + (tr_{g₁} − tr_{g₂})Ric₂`; the second term multiplies `|Ric₂|`, which the interface as stated does not bound, so W-K must determine whether the interface needs a `g₂`-curvature hypothesis (likely yes; then prove the corrected general theorem, the witness specialisation using the model's curvature bound, and record the corrected definition for the reviewer to apply in `WitnessTransport.lean`).
- 2026-09-06 (W-K landed): `ScalarComparison.lean`. **Finding: W-G's `ScalarCurvatureComparison` is false as stated** — `g₁ = (1+ε)g₂` has zero `g₂`-jets (`metricCovDeriv_self_eq_zero`) and satisfies the equivalence with `Λ(ε)`, yet `|R_{g₁} − R_{g₂}| = (ε/(1+ε))|R_{g₂}|` is unbounded over `(M', g₂, K)`; the inverse-metric perturbation lemma proposed in `WitnessTransport.md` §5 cannot exist. Corrected and proved: `abs_metricScalarAt_sub_le_of_jetBounds` (extra hypothesis `|Ric_{g₂}| ≤ Kb`; `|R_{g₁}−R_{g₂}| ≤ n²Λ·riemannDiffC + n(Λ−1)Kb`), `ScalarCurvatureComparisonOfRicciBound` + `scalarCurvatureComparison` with `scalarComparisonC n ε Kb = n²Λ(ε)·witnessRiemannC ε + n(Λ(ε)−1)Kb ≤ 27n²(ε + εKb)` for `ε ≤ 1/4`, `→ 0`; witness specialisations `modelComparison_scalar_sub_le_of_ricciBound` / `_of_riemannBound` (fed by the squared Rm bound in the `hKb` shape of `modelComparison_riemannOp_norm_le`). Device: `exists_diagInv_of_metricUniformEquivalentOn` gives one frame `g₂`-orthonormal and `g₁`-diagonal with `μ_i ∈ [Λ⁻¹, Λ]`, so both traces are computed in the same frame. Upstream candidates: `metricScalarAt_eq_sum_ricciTensor{,_diagonal,_orthonormal}`, `ricciTensor_sub_le_of_jetBounds`, `abs_ricciTensor_le_of_riemannOp_le`, `exists_orthoFrame_finrank`. Verification note: `lake env lean` does not apply the package `leanOptions` (Mathlib standard linter set); W-K re-ran with `-Dweak.linter.mathlibStandardSet=true` and caught a `linter.style.docString` warning — targeted `lake build` before committing remains the reviewer's check. To do after W-I lands: delete `ScalarCurvatureComparison` and `modelComparison_scalar_sub_le` from `WitnessTransport.lean` (referenced nowhere else) and rebuild the cone.
- 2026-09-06 (W-I landed): `GoodPointDerivatives.lean` — `goodPointBoundsOn_of_modelCurvatureBound`: `∃ C_*` before the manifold, for flows on `closedOpen 0 T` and `ε ≤ 1/4`, the two inequalities of `GoodPointBoundsOn`; `inverseCurvatureDerivatives_of_goodPointBounds` = `eq:scn-inverse-curvature-derivatives`. Proved: T2 transport of the model curvature bound to the source (`witnessSourceCurvature`, with `rmNormSq_restrictOpen`, `rmNormSq_openPullbackMetric` via `PullbackNaturalityLocal.metricRm04StdAt_pullback_localDiffeo` — the `Rm04` naturality W-G's note flagged), the `|Rm|²`↔operator dictionary, `dR(v) = Σ(∇_v Rm)(e_i,e_k,e_k,e_i)`, `|dR| ≤ n²|∇Rm||v|`, the rescaled-window construction and Shi application, unscaling. Constants `sourceCurvatureBound n K = n²(10+2K)+1`, `goodPointConst = max (n²C₁K₀) (c_lap C₂K₀ + 2n⁴K₀²)`. Interfaces: `ModelCurvatureBoundNearBase` (Chapter 10, as briefed); `WitnessSourceBallCapture` (compact closed balls — no Hopf–Rinow for `riemannianEDistOf` — plus the `F`-distance comparison outside the window and the Grönwall slice comparison to the shifted time `−2`); **`LocalShiUniformConstant`** — `shi_local_all_orders_curvature_scale_of_solution` quantifies `∃ C` *after* the flow (`shiAllOrdersBound n T eps m` with unbounded cutoff errors from `exists_shiFixedCutoff_ball_of_solution`), so through the rescaling the constant would depend on the good point; the interface is Theorem 7.1 with `∃ C` in front, a Chapter 7 fix (relayed to the Shi-chain session); `ScalarLaplacianCurvatureJetBound` (`|ΔR| ≤ c_n|∇²Rm|`: no second-order `nablaRm04_apply`, contracted Bianchi only as in-frame component predicates; first-order analogue proved). Scope: `closedOpen 0 T` only (`paraInterval_closedOpen_*` exist only for that shape).

- 2026-09-06 (Codex, `00d9d4425`): new `WitnessBallCapture.lean` discharges `WitnessSourceBallCapture` verbatim (`witnessSourceBallCapture`, the metric input to `lem:scn-good-point-derivatives`). Stronger `witnessSourceBallCapture_on_window` covers every `s ∈ [-4,0]`, not just `s = -2`. `closedBall_subset_image_of_metric_lower` proves the first-exit/path-lifting capture behind `eq:scn-model-source-capture`; `metric_inner_antitoneOn_of_ricci_nonnegative_interior` and `ancientModel_metric_zero_le` supply `h(0) ≤ h(s)` using the PDE only in the regular interior and continuity at time 0. Constants: `ε = 1/4`, model radius `2`, source radius `1`, lower metric factor `3/4`, inverse length factor `3/2`, strict margin `1 < 4/3`. No added hypotheses, curvature-bound interface, source completeness, source flow equation, or source sigma-compactness in the full-window theorem; no interface remains in this leaf. Correction to the old W-I note: native `RiemannianMetricComplete.closedEBall_isCompact` already supplies the required Hopf–Rinow step; model nonnegative Ricci replaces the proposed Grönwall/curvature-bound route. Five public declarations audited: exactly propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/WitnessBallCapture.lean`: exit 0, empty output. `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture`: exit 0, no warnings/errors, only this new leaf compiled (124s); both process counts were zero before the build. Only the new file/note and its root import were committed. Remaining for the closed-open good-point derivative endpoint: `ModelCurvatureBoundNearBase` (Chapter 23, collaborator's uniform model bound) and `ScalarLaplacianCurvatureJetBound` (this lane's next new file, scalar trace/Hessian identification); `LocalShiUniformConstant` is separately wired in `01679e88c`. Upstream candidates and full label crosswalk are in `WitnessBallCapture.md`.

- 2026-09-06 (Codex, `d76dbf1f7`): new `ScalarLaplacianJet.lean` discharges `ScalarLaplacianCurvatureJetBound` with the explicit non-sharp constant `c_n = n^6`. `exists_iterCov_metricTrace` / `iterCov_metricTrace_normSq_le` extend the native `RicciTowerTrace.exists_ric_trace` induction to arbitrary rank; `iterCov_zeroTensor_one_eq_duSec` / `_two_eq_hessianSec` identify rank-zero derivatives with the native differential/Hessian; `abs_laplacian_scalar_le_second_curvature` proves the static estimate at every time of a smooth metric family, with no flow equation or time-membership assumption. `goodPointBoundsOn_of_modelBound` now supplies all three tree-owned inputs of `lem:scn-good-point-derivatives` / `eq:scn-good-curvature-derivatives` (capture, Shi uniformity, Laplacian bound). Its sole named input is `ModelCurvatureBoundNearBase`, Chapter 23's uniform model bound; the source interval remains `closedOpen 0 T` and `epsilon_* = 1/4`. It does not claim the arbitrary-interval `GoodPointDerivativeBounds` interface or the book's extra all-order mixed-derivative assertion. Constants: `K0 = n^2(10+2K)+1`, `Cj = shiLocalUniformBound n j (K0*2) (sqrt K0)`, `CStar = max (n^2 C1 K0) (n^6 C2 K0 + 2 n^4 K0^2)`. Seven public declarations audited: exactly propext/Classical.choice/Quot.sound. Final `LEAN_NUM_THREADS=1 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/ScalarLaplacianJet.lean`: exit 0, empty output. `LEAN_NUM_THREADS=1 lake build +DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarLaplacianJet`: exit 0, zero warnings/errors, new leaf compiled in 18s. Before importing `ShiUniformConstant` its targeted build was also completed (15s, zero warnings); `WitnessBallCapture` was already built. Only the new file/note and its root import were committed. The note records the native trace route, exact scope, and the dependent zero-arity elaboration fix. Tasks 2a and 2b are closed; task 2c remains next, only in a verification-free window.

## 6. State at the end of 2026-09-06 (for the owner)

Historical snapshot. Under the 2026-09-08 owner correction, Chapter 10 here
is the new Chapter 23 and belongs to this task; Chapter 11 is the new
Chapter 24 and remains external. Later closures and proof-debt qualifications
are recorded in §4. In particular, the Chapter 23 model-bound sorry is now
our upstream target, not an indefinitely delegated external proof.

Landed in `Perelman/CanonicalNeighborhood/` (all leaves registered in the root, every file `lake env lean`-clean and built by targeted Lake builds with no warnings, axioms propext/Classical.choice/Quot.sound throughout):
`Predicates` (W-A, in `Noncollapsing/`), `PinchingDatum` (W-B), `Interfaces` + `ModelWitness` (W-C), `BadPointSelection` (W-D), `LocalPropagation` (W-E, W-H), `CompactPathAvoidance` (W-F), `WitnessTransport` (W-G), `RmNormFromEigenvalues` (W-H), `GoodPointDerivatives` (W-I), `ModelTheorem` (W-J), `ScalarComparison` (W-K).

Proved without interface: §12.2 predicates and bridges; §12.4 (`prop:scn-HI-to-Phi` first assertion, `lem:scn-admissible-Phi-majorant`, `lem:scn-Phi-scaling`); §12.5 frozen cylinder, witness restriction; §12.7 `lem:scn-bad-point-selection`, `lem:scn-local-propagation` modulo `GoodPointDerivativeBounds`; §12.8 `lem:scn-compact-path-approximation`; the dimension-three bridges `|Rm| ≤ 2√3 max|K_j|`, `|Rm| ≤ √3 R`; the curvature transport through a witness (Riemann, Ricci, scalar with a model Ricci bound).

Remaining interfaces, grouped by what closes them:
- **Chapter 10 (collaborator)**: `ModelCurvatureBoundNearBase` (`GoodPointDerivatives`).
- **Chapter 11 (collaborator)**: `lem:scn-good-point-buffered-canonical` (not stated), and through it `SelectedSequenceEventuallyGood` (`ModelTheorem`), which also bundles §12.8–12.10 (`thm:scn-bounded-curvature-at-distance`, `prop:scn-terminal-limit-global-bound`, `prop:scn-first-backward-slab`, `prop:scn-ancient-extension`).
- **Chapter 7 (Shi-chain session, relayed)**: `LocalShiUniformConstant` (Theorem 7.1 with its constant before the flow).
- **Terminal-time compactness (§5, owner decision)**: `NoncollapsePassesToLimit`, `BlowUpLimitNonnegativeCurvature` (limit passage), `GoodSetOpen`'s smooth-dependence half, the convergence→witness bridge, the diagonal step.
- **Comparison route closed in this lane**: `RemotePointTriangle` is proved by `remotePointTriangle` in `RemotePointTriangle.lean` (`6a63f0a63`), using the new complete hinge and minimizing-ray producers. Only the book's boundaryless convention is added; no collaborator merge is required for this result. Sphere separation and the ends package remain task 3 work.
- **Tree gaps this lane can close next**: `WitnessSourceBallCapture` (compact closed balls for `riemannianEDistOf` + `F`-distance comparison + Grönwall slice comparison), `ScalarLaplacianCurvatureJetBound` (`|ΔR| ≤ c|∇²Rm|`), `ScalarGradientComparison` (needs `Compactness/Bounds/Uniform/CurvatureJetOne.lean` to expose its private `extSec`), the `ModelWitness` tidy (import `Interfaces`, collapse `PointedFlowRmNormLeScalar`/`PointedFlowSqrtRmNormLeScalar`, identify `PointedFlowNoncollapsedAllScales` with `Predicates`), the orientation-refined selection lemma.

- 2026-09-06 (Shi-chain session, W31 dispatched): `LocalShiUniformConstant` confirmed as a quantification artefact (`shi_local_all_orders_sq_of_laplacianInput` chooses per-radius cutoff errors from `exists_shiFixedCutoff_ball_of_solution`; every constant in the chain is explicit). W31 adds `shiLocalUniformBound (d m : ℕ) (T R : ℝ)`, re-states both endpoints with it (old names kept as corollaries), and provides `shi_local_all_orders_uniform_constant I m hT hK hR : ∃ C ≥ 0, ∀ (M : Type u) …` with the instance list and hypothesis order aligned to `GoodPointDerivatives.lean` `LocalShiUniformConstant`; wiring will be `LocalShiUniformConstant I := fun m T K R hT hK hR => shi_local_all_orders_uniform_constant I m hT hK hR`. Cor 7.2's constant is `shiLocalUniformBound d m (K·T) R`. They touch only `Estimates/Shi/*` and `Analysis/Calculus/CutoffProfile.lean` (append-only).

## 7. Book numbering after the 2026-09-06 reorganisation (`master05a.tex` + `master05b.tex`)

The book is now two volumes with continuous chapter numbers (`master05a.tex` Chapters 1–23,
`master05b.tex` Chapters 24–42; both untracked at the repository root, copies in the session
scratchpad `bp2/`). Content is unchanged: every `scn-*`, `red-kappa-*`, `ksol-*`, `top-*`, `app-*`,
`cgs2e-*` statement block is byte-identical to the `book25.tex` snapshot except two typographical
edits (`lem:scn-good-point-buffered-canonical` display re-set with `gathered`;
`thm:shi-closed-short-time-input` retitled "established input"). Labels remain the reference; the
chapter names in this plan and in the file notes ("Chapter 12", "Chapter 7", …) follow the old
numbering and map as follows:

| old | new | file:line | content |
|---|---|---|---|
| App A–H | Ch 3–12 | `master05a` 2333–11757 | Toponogov 3 (`cor:top-equal-arm-hinge` L2736), Bishop–Gromov 4, sphere separation 5 (`thm:app-sphere-separation` L3675), SvK 6, Cheeger–Gromoll 7 (`thm:cgs2e-two-ends` L6620), Sharafutdinov 8, Ehresmann 9, Synge 10, soul 11, Poincaré–Hopf 12 |
| — | Ch 13–16 | `master05a` 11757–16318 | topological reconstruction, weak maximum principle, curvature evolution (Uhlenbeck), Hamilton–Ivey |
| Ch 7 Bando–Shi | Ch 17 | `master05a` 16318–18015 | `eq:shi-Theta-closes` L17126 |
| — | Ch 18–20 | `master05a` 18015–23474 | strong maximum principle/splitting, gradient solitons, 3D shrinking solitons |
| Ch 8 Harnack | Ch 21 | `master05a` 23474–24929 | |
| Ch 9 reduced geometry | Ch 22 | `master05a` 24929–28151 | `def:red-kappa-solution` L26805 |
| Ch 10 κ-compactness | Ch 23 | `master05a` 28151–30949 | `thm:ksol-universal-derivative-estimates` L30491 |
| Ch 11 neck–cap | Ch 24 | `master05b` 4–3647 | `thm:ncs-kappa-canonical-neighborhood` L2410 |
| **Ch 12 this lane** | **Ch 25** | `master05b` 3647–6610 | sections unchanged: §2 predicates L3731, §3 entropy engine L3810, §4 pinching L4172, §5 witnesses L4314, §6 maximal point L4447, §7 selection/propagation L4497, §8 finite horn L4761, §9 terminal compactness L5394, §10 ancient extension L5519, §11 model theorem L5964, §12–13 fixed smooth-flow theorem and κ-solution geometry transfer L6052–6322 |
| Ch 13 standard solution | Ch 26 | `master05b` 6610–10805 | |

Scratch index of all Chapter 25 statements: session scratchpad `ch25_statements.txt`.
- 2026-09-06 (W31 landed in the Bando–Shi lane, `8e8b4d4c9`; wired): `ShiUniformConstant.lean` — `localShiUniformConstant I : LocalShiUniformConstant I := fun m _ _ _ hT hK hR => shi_local_all_orders_uniform_constant I m hT hK hR`; the constant is `shiLocalUniformBound n m (K·T) R`. Consumers pass it for the `hshi` argument of `goodPointBoundsOn_of_modelCurvatureBound`, which is now conditional on `ModelCurvatureBoundNearBase` (Chapter 23), `WitnessSourceBallCapture` (Codex, in progress: `WitnessBallCapture.lean`) and `ScalarLaplacianCurvatureJetBound`.

## 8. Full Chapter 25 audit and implementation plan (2026-09-08)

### 8.1 Scope, evidence and counting convention

Requested outcome: inspect completed work before further implementation; estimate
the remaining Lean declarations; determine whether the whole skeleton exists;
identify missing theorem inputs. This is a source-and-verification-record audit,
not a new compilation or an endpoint-completion claim.

Checkout: `E:/differential-geometry-dev`, branch
`codex/gradient-ricci-solitons`; observed HEAD `9c970de34687` during the audit.
Chapter 23 is being changed concurrently, so its current plan and source must be
refreshed before a consumer is implemented. No branch was merged or copied.
Book source: local `master05b.tex`, Chapter 25, lines 3647–6609 at this snapshot;
labels below are the stable identifiers. Read-only topology comparisons used
local remote refs, not a fresh remote fetch.
Reproducible source census (statement labels, per-file counts, hashes, unique
imports and artifact timestamps):
`E:/lean-tools/chapter25-audit-20260908/source-census.json`.

- The book has **37 formal statements**: 22 lemmas, 7 theorems, 5 propositions
  and 3 corollaries. There are also 6 definitions and 3 remarks.
- The finite-horn proof explicitly lists **7 additional theorem cards**. These
  are nested sub-obligations of a formal statement, not 7 independent chapter
  endpoints. Track 37 statements plus these 7 cards; do not convert the combined
  44 nodes into a completion percentage.
- `CanonicalNeighborhood/` has **21 Lean files, 187 public named theorems**
  (229 including 42 private theorems), 9 public structures, 71 public definitions
  and one abbreviation. `Noncollapsing/Predicates.lean` adds 20 public theorems.
  Thus these 22 files contain **207 public theorems**, mostly helpers and
  conditional consumers, not 207 independently completed book results.
- All 21 canonical-neighborhood leaves are tracked and clean at the snapshot,
  each has one root import, and each has an artifact at least as new as its
  source. This is artifact-freshness evidence, not a substitute for compilation
  and `#print axioms`. Existing notes/commit receipts establish prior checks;
  this planning turn ran no Lean process.
- The canonical-neighborhood directory has one actual `sorry`, in
  `UpstreamModelCurvature.lean`. That does **not** mean one remaining proof:
  large conditional interfaces and unstated producers account for much of the
  remaining work. Earlier dependencies can also contribute `sorryAx`.

### 8.2 Statement-by-statement coverage

Status is coverage of the **full book statement**. `Matched` means a native
proof covers the relevant statement according to source and existing records;
`Partial` includes narrower results or conditional assembly; `Skeleton` means
the conclusion/outer reduction exists without its main producer; `Missing`
means no complete native statement-and-producer pair was found. None of these
labels claims a fresh axiom audit in this planning turn.

| Book label | Status | Current native coverage or precise remaining work |
| --- | --- | --- |
| `lem:scn-noncollapsing-scaling` | Matched | `Noncollapsing/Predicates.lean`: all three predicates and parabolic scaling. |
| `lem:scn-mu-Sobolev-relaxation` | Partial | Smooth-positive W-functional/cutoff machinery exists; exact Sobolev-infimum relaxation and mu interface need alignment. |
| `thm:scn-mu-monotonicity-interface` | Partial | `Entropy/W` monotonicity and uniform lower-W machinery; exact mu formulation is not yet supplied. |
| `lem:scn-cutoff-entropy-doubling` | Partial | `CutoffFunctional`, `CutoffEnergy`, `CollapseScale` prove substantial cutoff/doubling estimates with different constants and hypotheses. |
| `lem:scn-local-entropy-volume` | Partial | `FlowBallFunctional.exists_sel_w_bound` and downstream volume estimates; adapt to terminal spatial curvature control. |
| `lem:scn-early-slab-volume` | Partial | `EarlyTime.early_vol_low` / `early_ball_low` retain an extra `r^2 <= t` restriction. |
| `thm:scn-smooth-no-local-collapsing` | Partial | `EarlyTime.no_local_open` proves a 3D parabolic-tensor version, not the book's spatial-tensor statement in all dimensions at least 2. |
| `cor:scn-parabolic-noncollapse-injectivity` | Partial | Spatial-to-parabolic implication and CGT `flowInjOfVol` exist; assemble the exact corollary. |
| `thm:scn-strong-scalar-no-local-collapsing` | Skeleton | Strong scalar predicate is defined; scalar-only entropy/volume producer is absent. |
| `lem:scn-noncollapse-passes-to-limit` | Partial | Reuse Ch23 `PointedNoncollapse`; its current theorem assumes all-scale source noncollapse and inherits volume-naturality debt. Expanding available scales and flow-time adaptation remain. |
| `lem:scn-admissible-Phi-majorant` | Matched | `PinchingDatum.lean`: admissible majorant construction. |
| `lem:scn-Phi-scaling` | Matched | `PinchingDatum.lean`: scaled datum and curvature pinching. |
| `prop:scn-HI-to-Phi` | Partial | HI-to-datum and numerical eigenvalue-limit work exist; actual pointed curvature-operator nonnegativity needs a correctly stated bridge. |
| `lem:scn-model-witness-stability` | Partial | Exact witness restriction and transport exist; `GoodSetOpen` is still an interface, not a produced openness theorem. |
| `lem:scn-good-point-derivatives` | Partial | `ScalarLaplacianJet.goodPointBoundsOn_of_modelBound` is proved with an explicit Ch23 model bound. Instantiated consumer inherits the upstream `sorry`. |
| `prop:scn-maximal-point-singularity-model` | Partial | Scalar normalization and pointed-limit assembly exist. Current extraction needs a common open window; terminal and ancient limit production remain. |
| `lem:scn-bad-point-selection` | Matched | Ordinary and orientation-refined selection in `BadPointSelection` / `OrientedBadPointSelection`. |
| `lem:scn-local-propagation` | Partial | `ClosedOpenPropagation.exists_closedOpenLocalPropagation_of_modelBound` proves the conditional argument; book time-domain/terminal adaptation and Ch23 bound remain. |
| `lem:scn-good-point-buffered-canonical` | Missing | Must consume Ch24 geometric tuples, preserve strict reserves and transfer the same finite tuple through the actual witness. |
| `lem:scn-cone-terminal-exclusion` | Missing | Actual smooth cone curvature/null-plane contradiction with the appropriate terminal maximum principle. |
| `lem:scn-compact-path-approximation` | Matched | `CompactPathAvoidance.exists_partition_eventually_rectifiable_path_avoiding_ball`. |
| `lem:scn-finite-horn-produces-cone` | Missing | All seven cards in §8.3 require explicit native contracts and producers. Compact path approximation is already available. |
| `thm:scn-bounded-curvature-at-distance` | Missing | Depends on the finite-horn obstruction; no producer for the full uniform distance bound. |
| `prop:scn-terminal-limit-global-bound` | Missing | Terminal extraction plus null-rank and positive-curvature alternatives; local bounds alone do not imply the global bound. |
| `prop:scn-first-backward-slab` | Missing | Produce the actual common backward slab and compatible terminal limit. |
| `lem:scn-recentered-source-bound` | Partial | `RecenteredSourceInputs.recenteredSource_inputs` prepares scaled data assuming an anchor with scalar curvature B; it does not find the crossing or prove C(A,D). |
| `lem:scn-uniform-moving-slice-propagation` | Missing | Uniformity for moving source slices/basepoints, with the required quantifier order. |
| `lem:scn-remote-point-triangle` | Matched | `RemotePointTriangle.remotePointTriangle`: actual equal-arm hinge/ray producer. |
| `lem:scn-open-nonnegative-sphere-separation` | Missing | Native Ricci two-ends theorem is available; construct the nonseparating-sphere cover and the three-ends contradiction. Appendix C only covers the Euclidean-ambient case directly. |
| `lem:scn-far-point-separating-neck` | Missing | Needs the sphere-separation argument and actual buffered neck/collar geometry. |
| `prop:scn-ancient-extension` | Missing | Compatible extension through all negative times, completeness, uniform curvature bounds and the required noncollapse. |
| `thm:scn-abstract-model-theorem` | Skeleton | `exists_orientedModelRadius_of_selectedSequenceEventuallyGood` assumes the large `hblock` described in §8.4. |
| `thm:scn-closed-flow-models` | Missing | Apply the abstract model theorem with the correctly produced fixed-flow noncollapse/pinching and time normalization. |
| `cor:scn-arbitrary-high-curvature-blowup` | Missing | Actual arbitrary-sequence convergence/model conclusion, not merely selected bad-sequence contradiction. |
| `lem:scn-buffered-canonical-pullback` | Missing | Transfer exact subsets/collars/basepoint and compact alternatives; distinguish approximate roundness from exact roundness. |
| `thm:scn-smooth-canonical-neighborhood` | Missing | Native final witness definition plus the closed-flow and pullback producers. |
| `cor:scn-high-curvature-derivatives` | Missing | All spatial/time orders and the smaller-neighborhood statement with pointwise curvature scale. |

This conservative classification gives **6 Matched, 14 Partial, 2 Skeleton,
15 Missing** formal statements. It measures statement coverage, not elapsed
effort or the percentage of Lean code already written. In particular, several
Partial rows contain substantial checked proofs.

### 8.3 Finite-horn obligations must remain visible

The book itself marks these seven cards as provisional, untranslated proof
obligations. They belong to Chapter 25, not to the missing Ch24 input package.
Their exact Lean statements should be settled before revising the effort estimate.

| Book card | Required mathematical content |
| --- | --- |
| `PC-F-RF-FINITE-HORN-END-RAYS` | Cofinal nested subends, an actual completion endpoint, intrinsic/ambient distance agreement, frontier escape, and minimizing end-rays with the asserted equalities. |
| `PC-F-RF-FINITE-HORN-END-RAY-APPROXIMATION` | Whole minimizing arms and connectors in the same smooth tube, with parameter and distance convergence. |
| `PC-F-RF-FINITE-HORN-END-ANGLE` | Local Toponogov monotonicity, limiting angles, symmetry and triangle inequality, and the zero-angle metric quotient. |
| `PC-F-RF-FINITE-HORN-DIRECTION-COMPACTNESS` | Total boundedness, compact completion and distinct directions. |
| `PC-F-RF-FINITE-HORN-CONE-CONVERGENCE` | Full compact-annulus correspondences with vanishing distortion, preserving the marked point and radial function. |
| `PC-B-RF-FINITE-HORN-TWO-SCALE-COMPARISON` | Positive finite lower/upper curvature-to-distance scale ratio, barriers and nested cross-sections; reuse the proved compact-path avoidance lemma. |
| `PC-B-RF-FINITE-HORN-SMOOTH-CONE-PATCH` | Use the same source embeddings to identify a terminal smooth patch with `dr^2 + r^2 gSigma`. A metric-space cone with an unrelated smooth structure is insufficient. |

### 8.4 Why the skeleton is not complete

The outer contradiction and much of the selection/transport machinery exist.
However, `OrientedSelectedSequenceEventuallyGood` in `OrientedModelTheorem.lean`
asserts that selected normalized bad sequences eventually have actual oriented
model witnesses. `exists_orientedModelRadius_of_selectedSequenceEventuallyGood`
takes this assertion as `hblock`; there is no producer. It hides the bounded
curvature-at-distance, terminal-global-bound, backward-slab, ancient-extension
and convergence-to-witness chain, including its Ch24 consumers.

Three contract issues must be resolved before filling proofs:

1. `Interfaces.BlowUpLimitNonnegativeCurvature` quantifies over arbitrary `Phi`
   without admissibility or an equivalent sublinear bound, although the intended
   proof needs `Phi(s)/s -> 0`. Do not try to discharge this overstrong interface.
   Use a correctly scoped producer with explicit admissibility, as in the
   numerical `PinchingDatum.nonneg_of_rescaledCurvatureTendsto`, and deliberately
   reconcile its consumers.
2. The current oriented radius skeleton uses `closedOpen0T` and `1 <= t0 < T`;
   the book abstract statement includes the terminal time on `[0,T]`. Terminal
   compactness/regularity is a real obligation, not a notation change.
3. `OrientationDatum` is an arbitrary family of propositions. The book needs
   actual manifold orientations and orientation-preserving maps through the
   same exhaustion embeddings. `trivialOrientationDatum := True` does not supply
   that geometric conclusion.

The final `scn-canonical-neighborhood-witness` definition also lacks a complete
native realization. Its exact neck/cap, ball sandwich, compact component and
approximate-round alternatives must match the incoming Ch24 types.

### 8.5 Upstream inputs: available, partial and missing

| Input family | Current evidence and remaining obligation |
| --- | --- |
| Soul / Sharafutdinov | General Soul, native positive-soul/Ch11 and the main Sharafutdinov retraction/level-map/diameter chain are proved. Reuse `Topology/Soul` endpoints; the main Sbr chain has 36 verified leaves / 148 standard-only public declarations with current-hash receipts at `E:/lean-tools/soul-audits-20260907/SbrCompletionEvidence-20260908.json`. This does not by itself produce Ch23's outward-neck comparison. |
| Ch23 fixed-kappa model curvature bound | `UpstreamModelCurvature.chapter23_modelCurvatureBoundNearBase` is still an explicit `sorry`. Prioritize the seed-volume / normalized bounded-distance route in §9.4: it gives one bound chosen before all normalized ancient models, on the actual radius-3 time-zero ball over `[-4,0]`, without waiting for full fixed-kappa compactness. The seed chain and earlier terminal-Harnack debt are not closed; pointwise estimates for one model are insufficient. |
| Ch23 geometry packages | Fixed-kappa compactness/universal derivatives, the required terminal rank-one product, `lem:ksol-neck-outward-subsequence` and `prop:ksol-outward-neck-comparison` (constant 144) are not yet available as completed consumers for this chapter. Refresh `KAPPA_COMPACTNESS_PLAN.md` before implementation; do not duplicate the active lane's work. |
| Ch23 pointed noncollapse | `PointedNoncollapse.tensor_noncollapsed_of_pointed_canonical_convergence` is a real partial producer, verified at `67c0a84bd`, with earlier volume-naturality `sorryAx`. Adapt its all-scale source hypothesis to expanding available scales and the same-map flow setting. `PointedFlowSlices` (`3a866bfe8`) supplies time-slice identities, not limit existence. |
| Earlier distance, Harnack and splitting | Explicit unresolved inputs already exist in Ch23: `UpstreamAdditiveDistance.ricciFlow_additive_distance_bound_of_ricci_upper`, `UpstreamTerminalHarnack.hamilton_ancient_trace_harnack_at_terminal`, and `UpstreamAncientSplitting.ancient_fixed_universal_cover_product_of_null_plane`. The last is for bounded ancient flows; it is not automatically the locally bounded terminal version needed here. |
| Earlier local compactness and terminal estimates | Ch23 also exposes `UpstreamLocalMetricCompactness.exists_local_pointed_metric_compactness` and `UpstreamTerminalShi.shi_local_curvDerivNorm_terminal_inclusive`, both with explicit `sorry`. These retain the actual canonical maps and terminal-inclusive jet bounds respectively; open-time extraction does not discharge them. The untracked `UpstreamScalarZeroPropagation.scalar_slice_zero_of_nonnegative_slab` is an additional source-only scalar maximum-principle obligation; it is not the terminal curvature-operator splitting theorem. |
| Earlier volume naturality | `UpstreamVolumeNaturality.volumeMeasurePreserving_pullbackMetric` is explicit debt inherited by the current pointed-noncollapse route. Preserve that dependency in consumer reports. |
| Ch24 canonical geometry | No complete native package was found here for `thm:ncs-kappa-canonical-neighborhood`, `def:ncs-local-canonical-neck`, `def:ncs-local-canonical-cap`, `lem:ncs-cap-truncation-sandwich`, or `lem:ncs-ordered-middle-tube`. Require actual finite tuples, central spheres/collars, strict radial reserve `b <= (2-zeta)a`, and the no-return/shortening conclusion. These are upstream inputs; the Ch25 pullback is this chapter's own proof. |
| Sphere separation | Local remote ref `origin/codex/appendix-c-sphere-separation-20260903` at `d9cab8a5b` contains actual `SourceTheorems` proofs for Jordan–Brouwer, bicollar sides/order and nested disjoint spheres. They require an ambient diffeomorphism to Euclidean 3-space. A native adapter is needed; they do not directly prove separation in every open nonnegative-curvature 3-manifold. Native `RicciTwoEnds` supplies the at-most-two-ends ingredient for the general covering argument. |
| Smooth Schoenflies in dimension 3 | Local remote ref `origin/codex/smooth-schoenflies-three` at `01b615649` contains `smooth_schoenflies_three` with an explicit `sorry`. The branch supplies a statement, not a proof. Track this honestly wherever ball recognition/separator exclusion uses it. |

In the terminal-global-bound argument, Soul/Sharafutdinov feed the positive-curvature
branch through Ch23's outward-neck geometry and comparison. The other branch
needs the appropriate terminal null-rank/splitting input. Neither branch follows
from the local curvature bound alone.

The entropy/spatial/strong-scalar noncollapse adaptation, seven finite-horn cards,
general sphere-cover argument, terminal extraction, recentered `C(A,D)` bound,
ancient extension and final transfer are **Chapter 25 work**. Do not relabel these
as upstream Ch24 assumptions to make an endpoint appear closed. Earlier missing
results may be exposed by accurately stated `sorry` declarations during later
implementation, as authorized by the user; their consumers remain conditional.

### 8.6 Initial theorem budget and implementation order

Estimate **about 100–180 additional public Lean theorems**, beyond the existing
207 in the counted files. This is a rough planning range, not a target for helper
proliferation, a cap on work, or a percentage estimate. It excludes proving the
missing Ch22–24 theorems and a full independent Schoenflies development, but
includes Chapter 25 adapters and its own compactness/geometry arguments. Existing
verified machinery should be reused rather than redeclared. The finite-horn
contracts and terminal regularity are the largest sources of uncertainty.

| Work package | Approximate additional public theorems |
| --- | ---: |
| Statement alignment; entropy, spatial and strong-scalar noncollapse | 12–22 |
| Terminal compactness, noncollapse/sign in limits, orientation and actual witness extraction | 20–35 |
| Seven finite-horn cards, cone exclusion and bounded curvature at distance | 35–60 |
| Terminal global bound, first slab, recentered `C(A,D)`, moving slices and ancient extension | 25–45 |
| Abstract model closure, fixed-flow/arbitrary blowups, final canonical transfer | 10–20 |

The component ranges sum to 102–182; 100–180 is the rounded estimate. Reestimate
after the seven finite-horn contracts have precise Lean statements and the
current Ch23/24 producer types are fixed.

Execution order:

1. Align full statements and actual geometric types: admissible pinching, closed
   terminal time, same-map convergence/orientation, and the Ch24 tuple. Expose
   exact earlier inputs; replace the single large `hblock` in the work plan with
   the visible Chapter 25 obligations above, without claiming they are proved.
2. Close the reusable analytic bridges: adapt the existing cutoff chain to
   spatial curvature control, remove the early-slab radius restriction, develop
   scalar-only selection, and reuse Ch23 pointed noncollapse for growing scales.
   Establish the correctly scoped geometric curvature-limit bridge.
3. Prove the seven finite-horn cards, smooth cone exclusion and then bounded
   curvature at distance. Settle terminal compactness interfaces in parallel
   as mathematical dependencies, without starting duplicate Ch23 work.
4. Build terminal global bounds and the first backward slab; upgrade recentered
   input preparation to `C(A,D)`; prove moving-slice propagation and the
   far-point separator argument; assemble a compatible complete ancient flow.
5. Produce `OrientedSelectedSequenceEventuallyGood` with actual witnesses;
   close the abstract model theorem and its fixed-flow/arbitrary-blowup
   consequences; transfer Ch24 geometry to the final native canonical witness
   and all-order derivative package, respecting the book's constant order.

First concrete proof batch after planning: the spatial noncollapse adaptation
and the admissible curvature-limit bridge, using existing native machinery.
Neither requires pretending the Chapter 23 uniform model bound is proved.
Before any compiler work, refresh ownership and the verification window in
`WORKING_STATUS.md`; this planning audit requested no such window.

Local verification setup at this snapshot: the dev checkout has no
`scripts/lake-locked.ps1`; the existing wrapper is
`E:/testdifferential-geometry/scripts/lake-locked.ps1`, run with the dev checkout
as working directory. Do not copy the wrapper or reuse artifacts across divergent
checkouts. Focused checks, targeted refreshes and endpoint axiom audits still
follow the current shared-workspace coordination rules.

### 8.7 Scalar noncollapse checkpoint (2026-09-08 20:09 UTC)

Three new leaves, eleven public theorems, no new proof placeholders:

- `ScalarCutoff.lean` (5): scalar control passes to smaller concentric balls,
  even when scalar curvature is negative; scalar-only dyadic selection preserves
  the original normalized volume; a smooth positive normalized test function
  satisfies the W bound. The constant is
  `scalarCollapseWConst n = 400 * 2^(n+1) + 1 - (n/2)*log(4*pi) - n`.
  No backward time slab, Ricci lower bound or Ch23/24 input is used.
- `EarlySlabVolume.lean` (1): `family_early_slab_volume` proves
  `lem:scn-early-slab-volume` in arbitrary dimension, at all radii below a fixed
  positive bound. Keep one spatial radius independently of time in the finite
  normal-chart argument, then use volume monotonicity for larger bounded radii.
  The former `r^2 <= t` hypothesis is absent.
- `ScalarNoncollapse.lean` (5): `scalar_noncollapse_of_lowerW` proves the
  dimension-independent entropy-to-volume implication; `early_slab_ball_lower`
  supplies the actual native balls; `strongScalarNoLocalCollapsing_of_lowerW`
  completes the early/late argument with a precise uniform lower-W input.
  `strongScalarNoLocalCollapsing_three` and `spatialNoLocalCollapsing_three`
  instantiate the available native 3D entropy producer. They cover every time
  in `[0,omega)`, including zero, and every bounded positive scale; strong scalar
  includes every smaller concentric ball. Neither endpoint assumes Ch23/24 data.

Verification: final focused outputs EMPTY (43.3s, 28.3s, 25.6s respectively);
named lint-clean builds (36s, 22s, 27s). Fresh external `NoncollapseAxioms.lean`
audit (28.4s) checks all eleven public declarations: only `propext`,
`Classical.choice`, `Quot.sound`. Evidence and current source hashes:
`E:/lean-tools/chapter25-audit-20260908/noncollapse-completion.json`.
Three root imports added in one owned hunk; no lower-file API was changed.

Scope accounting: the early-slab formal statement is now covered; the general
strong-scalar statement has its full Chapter25 proof with an explicit entropy
input, and both strong-scalar/spatial theorems are fully instantiated in 3D.
Do not claim an unconditional all-dimensional entropy theorem or full Chapter25
completion. The next own-chapter target is the second-derivative kernel identity
used in the finite-horn cone-terminal contradiction, followed by its geometric
realization. Upstream integration remains deferred at the user's request.

### 8.8 Differentiated kernel identity (2026-09-08)

`KernelSecondDerivative.lean` proves, for a locally symmetric C2 operator field
and a C2 vector field with `A(t)v(t)=0` on a neighborhood,
`<A''v,v> = 2<A v',v'>`. It actually differentiates the kernel identity twice;
the derivative identities are not assumed. Two further theorems sum over a
finite family with common operator/vector base values and deduce strict
positivity from a nonnegative operator and one positive variation direction.
These are the one-direction, trace and sign parts of
`eq:scn-cone-Laplacian-kernel` / `eq:scn-cone-positive-Laplacian`.

Final focused14.4s EMPTY; lint-clean named build12s; fresh external audit13.0s
checks all three public declarations with standard axioms only. Evidence:
`E:/lean-tools/chapter25-audit-20260908/kernel-completion.json`.

Still required for `lem:scn-cone-terminal-exclusion`: actual cone metric/radial
connection identities; a smooth radial bivector kernel field; identification of
the directional derivatives in parallel trivializations with the native rough
Laplacian; and the terminal curvature evolution/one-sided derivative argument.
The tree has tensor inner-product Laplacian rules in
`Geometry/Operator/TensorInnerLaplacian.lean` and curvature-operator parallel
transport in `Geometry/Connection/ParallelTransport/AlgebraicCurvatureOperatorCone.lean`.
No native warped/cone metric constructor was found. The general product
curvature identity in Ch23's `UpstreamRiemannianProduct` is still an earlier
explicit obligation, not a proved cone formula. Develop the actual Chapter25
cone geometry without disguising any of these own arguments as an input.


## 9. Full Chapter25 skeleton and proof continuation (2026-09-08)

The requested skeleton milestone is complete. This milestone
means coverage of the book's37 formal statements and7 finite-horn cards, with
accurate actual geometric data and named obligations. It does NOT mean that the
chapter's proofs or upstream integration are complete. Earlier ownership/scope
paragraphs remain historical. Chapter23/24 implementation and integration remain
deferred by the user. The subsequent continuation fills Chapter25's own proofs;
its current checked checkpoint is section9.3.

Six new leaves now form the complete statement/data skeleton. Their final
verification and proof-debt counts are recorded below:

- `Chapter25Geometry`: actual tangent orientations, smooth compact domains,
  shrinking-cylinder maps, exact ball/projective cap core and tube equations,
  four canonical alternatives, metric-compatible cone charts.
- `Chapter25Entropy`: genuine weak-gradient W12 tests, extended-real entropy
  infima, exact book cutoff constant, arbitrary-dimensional statements and the
  separate earlier entropy/CGT obligations. Existing proved3D noncollapse is reused.
- `Chapter25Convergence`: varying CLOSED backward source intervals; normalized
  sources only assume goodness above2; native terminal exhaustion maps; actual
  all-scale metric noncollapse and same-map spacetime convergence.
- `Chapter25FiniteHorn`: intrinsic completion versus ambient completion; shortest
  end-rays on a sufficiently deep subend; zero-angle quotient; full two-sided
  compact-annulus correspondences; global barriers; distance/curvature scale
  ratio; realized horn/source provenance; smooth radial cone patch.
- `Chapter25Extension`: terminal-inclusive derivative/propagation adapters,
  strict buffered tuples, signed transverse paths, terminal global bound,
  first backward slab, recentered/moving-slice estimates, general nonnegative
  sphere separation, far separating necks and ancient closure.
- `Chapter25Theorems`: closed-terminal abstract radius, actual oriented selection
  adapter, explicit selected-sequence assembly, fixed-flow/arbitrary blow-ups,
  buffered pullback and final canonical assembly, actual Ricci-corrected mixed jets.

The former `hblock` is not an input of the new abstract theorem. Its proof calls
four separately named geometric producers and the convergence-to-witness adapter.
Likewise, the finite-horn assembly calls the construction, end, angle, annular,
scale and smooth-patch nodes. A body containing `sorry` is an OWN Chapter25
obligation unless explicitly placed in the `Chapter25.Upstream` namespace.

Source correspondence corrections that must remain visible:

1. `BlowUpLimitNonnegativeCurvature` in the older interface lacks admissibility
   of Phi. The new geometric statement explicitly requires it.
2. Closed source terminal times are included. The older closed-open proofs are
   reused as partial producers; their interval adapters are explicit own debts.
3. Orientation uses `TangentOrientationSection` and the invertible differential
   on the actual embedding domain. No `True` orientation instantiation.
4. Openness is stated for strict witness comparisons; the older nonstrict
   `GoodSetOpen` is not asserted to be open by simply renaming it.
5. The approximate-round tag compares a STATIC terminal metric with its round
   reference; it does not assert small time jets against a stationary round flow.
   The volume lower bound is absent exactly in this tag.
6. All final constants C1,C2 precede kappa and the flow. Model tolerance may
   depend on kappa; curvature thresholds may depend on the fixed flow.
7. Mixed time jets use the Ricci slot correction and actual one-sided derivatives
   on the source interval. Their tensor realization is a separate own obligation.
8. `WindowedModelWitness` keeps the existing ancient model/normalization,
   metric norms, maps and source capture, but requires time-jet identities only
   on the actual finite comparison window. The older all-real-time jet condition
   could constrain arbitrary source values outside its valid interval. New
   `oriented_witness_mono` remains an explicit own adapter;
   `closed_bad_point_selection` now has a verified proof for the actual tuple.
   An old witness producer is not silently counted for the new tuple.
9. A normalized source is retained on `[-2*depth,0]`; higher-curvature goodness
   is required on `[-depth,0]`, with `modelDepth eps <= depth`. This preserves
   the past needed by witnesses at the earlier edge of the controlled window.
   Requiring such witnesses at the earliest time of the source itself is wrong.
10. Far separating necks use the actual spatial slice (`SpatialNeck`), avoiding
    an extra backward-flow requirement at an extension edge. Buffered canonical
    data stores a smaller positive tolerance and strict scalar/tensor/volume
    reserves as well as the radial margin and actual cap collar.
11. The cone-terminal exclusion is stated for any local nonnegative Ricci flow
    with a nonflat radial cone metric at its terminal time. Source-sequence
    provenance belongs to the horn construction, not to this local obstruction.

Earlier inputs still needed by the proof chain: general-dimensional entropy
monotonicity/compact-scale lower bound and local CGT; fixed-kappa compactness and
UNIVERSAL (not model-dependent) mixed derivative estimates; local terminal
rank-one splitting; outward-neck subsequence/comparison; Chapter24 finite
canonical tuples, cap truncation and ordered two-arm/no-return geometry. The
existing KappaSolutions upstream additive-distance, Harnack, local compactness,
terminal Shi and volume-naturality declarations remain read-only references.
No integration of those branches is asserted at the skeleton milestone.

The reproducible coverage manifest is
`E:/lean-tools/chapter25-skeleton-20260908/manifest.json`;
`check_coverage.py` checks the exact37 labels and7 node IDs against the local
book, declarations, classification and current source hashes. The final
verification receipt is `completion.json` in the same directory.

### 9.1 Historical verified skeleton checkpoint (commit6f07c2d242)

Skeleton coverage: **44/44 = 100%, 0 skeleton nodes remaining**: the37 formal
Chapter25 statements and7 finite-horn cards all have checked native declarations
or explicitly identified existing producers. This percentage is NOT proof
completion. No Chapter23/24 integration is claimed.

At this checkpoint the six new leaves contained50 public theorems:45 explicit `sorry` obligations
(39 own Chapter25,6 earlier inputs), four proved but conditional assemblies,
and one standard-axiom-only spatial-to-parabolic conversion. Fresh `#print axioms`
therefore reports49 public theorems with `sorryAx` and1 without it. All14 audited
data definitions use only the standard axioms. There is no new `axiom`, `unsafe`
or `opaque` declaration. This checkpoint established the skeleton, not45 proved
results. The current proof-debt counts are in section9.3.

Final serial checks and named builds, in the explicitly granted exclusive window:

| New leaf | Focused check (s) | Named build (s) | Own open | Earlier open |
|---|---:|---:|---:|---:|
| `Chapter25Geometry` | 40.6 | 39 | 0 | 0 |
| `Chapter25Entropy` | 29.5 | 24 | 5 | 3 |
| `Chapter25Convergence` | 30.5 | 26 | 2 | 0 |
| `Chapter25FiniteHorn` | 37.3 | 32 | 11 | 0 |
| `Chapter25Extension` | 39.3 | 31 | 10 | 1 |
| `Chapter25Theorems` | 39.0 | 35 | 11 | 2 |

Every check/build passed. Geometry's focused output is empty; all other final
warnings are exactly the recorded `sorry` declarations. Named builds also replay
the existing `UpstreamModelCurvature` warning. A fresh external audit checks all
50 public declarations plus14 data definitions. Source and artifact hashes,
complete logs, declaration lines, own/upstream classification and unique root
imports are saved in `E:/lean-tools/chapter25-skeleton-20260908/completion.json`.
Only the six individual imports were added to the owned aggregate hunk; no root
build or broad refresh was run.

The six explicit earlier slots are `Upstream.mu_monotone`,
`Upstream.mu_compact_scale_lower`, `Upstream.local_metric_injectivity`,
`Upstream.kappa_canonical_neighborhood`, `Upstream.fixed_kappa_compactness`, and
`Upstream.kappa_universal_derivatives`. The remaining Chapter25 obligations are
kept outside `Upstream`. Additional earlier lemmas needed when filling the proofs
are listed above; connecting them remains deferred.

### 9.2 Current book-to-source coverage

The status below supersedes the pre-skeleton missing/stated census in section8.
"Prior verified" refers to the existing producer, not an axiom audit rerun in
this skeleton batch. "Open adapter" explicitly records interval, orientation,
or witness changes that the older producer does not yet discharge.

| # | Book statement/card | Native declaration | Proof status |
|---:|---|---|---|
| 1 | `lem:scn-noncollapsing-scaling` | `Predicates: para_spatial_noncollapse` | Existing producer |
| 2 | `lem:scn-mu-Sobolev-relaxation` | `Chapter25Entropy: mu_sobolev_relaxation` | Open Chapter25 |
| 3 | `thm:scn-mu-monotonicity-interface` | `Chapter25Entropy: mu_monotone` | Open earlier input |
| 4 | `lem:scn-cutoff-entropy-doubling` | `Chapter25Entropy: cutoff_entropy_doubling` | Open Chapter25 |
| 5 | `lem:scn-local-entropy-volume` | `Chapter25Entropy: local_entropy_volume` | Open Chapter25 |
| 6 | `lem:scn-early-slab-volume` | `EarlySlabVolume: family_early_slab_volume` | Prior verified |
| 7 | `thm:scn-smooth-no-local-collapsing` | `Chapter25Entropy: spatial_no_local_collapsing` | Verified conditional assembly; strong-scalar producer open |
| 8 | `cor:scn-parabolic-noncollapse-injectivity` | `Chapter25Entropy: local_metric_injectivity` | Open earlier input |
| 9 | `thm:scn-strong-scalar-no-local-collapsing` | `Chapter25Entropy: strong_scalar_no_local_collapsing` | Open Chapter25 |
| 10 | `lem:scn-noncollapse-passes-to-limit` | `Chapter25Convergence: noncollapse_passes_to_limit` | Open Chapter25 |
| 11 | `lem:scn-admissible-Phi-majorant` | `PinchingDatum: exists_admissiblePinchingFunction_ge` | Prior verified |
| 12 | `lem:scn-Phi-scaling` | `PinchingDatum: phiAlmostNonnegative_paraSolution` | Prior verified |
| 13 | `prop:scn-HI-to-Phi` | `Chapter25Convergence: blowup_limit_nonnegative` | Open adapter |
| 14 | `lem:scn-model-witness-stability` | `Chapter25Theorems: strict_model_witness_open, oriented_witness_mono` | Open adapter |
| 15 | `lem:scn-good-point-derivatives` | `Chapter25Extension: good_point_derivatives` | Open adapter |
| 16 | `prop:scn-maximal-point-singularity-model` | `Chapter25Theorems: maximal_point_singularity_model` | Open Chapter25 |
| 17 | `lem:scn-bad-point-selection` | `Chapter25Theorems: closed_bad_point_selection, selected_countersequence_of_radius_failure` | Closed selection verified; countersequence adapter open |
| 18 | `lem:scn-local-propagation` | `Chapter25Extension: local_propagation` | Open adapter |
| 19 | `lem:scn-good-point-buffered-canonical` | `Chapter25Extension: good_point_buffered_canonical` | Open Chapter25 |
| 20 | `lem:scn-cone-terminal-exclusion` | `Chapter25FiniteHorn: cone_terminal_exclusion` | Verified, standard-only (`00bd34ae3`) |
| 21 | `lem:scn-compact-path-approximation` | `CompactPathAvoidance: exists_partition_eventually_rectifiable_path_avoiding_ball` | Prior verified |
| 22 | `lem:scn-finite-horn-produces-cone` | `Chapter25FiniteHorn: finite_horn_produces_cone` | Conditional assembly |
| 23 | `thm:scn-bounded-curvature-at-distance` | `Chapter25FiniteHorn: bounded_curvature_at_distance` | Open Chapter25 |
| 24 | `prop:scn-terminal-limit-global-bound` | `Chapter25Extension: terminal_limit_global_bound` | Open Chapter25 |
| 25 | `prop:scn-first-backward-slab` | `Chapter25Extension: first_backward_slab` | Open Chapter25 |
| 26 | `lem:scn-recentered-source-bound` | `Chapter25Extension: recentered_source_bound` | Open Chapter25 |
| 27 | `lem:scn-uniform-moving-slice-propagation` | `Chapter25Extension: uniform_moving_slice_propagation` | Open Chapter25 |
| 28 | `lem:scn-remote-point-triangle` | `RemotePointTriangle: remotePointTriangle` | Prior verified |
| 29 | `lem:scn-open-nonnegative-sphere-separation` | `Chapter25Extension: open_nonnegative_sphere_separation` | Open Chapter25 |
| 30 | `lem:scn-far-point-separating-neck` | `Chapter25Extension: far_point_separating_neck` | Open Chapter25 |
| 31 | `prop:scn-ancient-extension` | `Chapter25Extension: ancient_extension` | Open Chapter25 |
| 32 | `thm:scn-abstract-model-theorem` | `Chapter25Theorems: abstract_model_theorem` | Conditional assembly |
| 33 | `thm:scn-closed-flow-models` | `Chapter25Theorems: closed_flow_models` | Open Chapter25 |
| 34 | `cor:scn-arbitrary-high-curvature-blowup` | `Chapter25Theorems: arbitrary_high_curvature_blowup` | Open Chapter25 |
| 35 | `lem:scn-buffered-canonical-pullback` | `Chapter25Theorems: buffered_canonical_pullback` | Open Chapter25 |
| 36 | `thm:scn-smooth-canonical-neighborhood` | `Chapter25Theorems: smooth_canonical_neighborhood` | Conditional assembly |
| 37 | `cor:scn-high-curvature-derivatives` | `Chapter25Theorems: high_curvature_derivatives` | Open Chapter25 |
| 38 | `PC-F-RF-FINITE-HORN-END-RAYS` | `Chapter25FiniteHorn: finite_horn_end_rays` | Open Chapter25 |
| 39 | `PC-F-RF-FINITE-HORN-END-RAY-APPROXIMATION` | `Chapter25FiniteHorn: finite_horn_ray_approximation` | Open Chapter25 |
| 40 | `PC-F-RF-FINITE-HORN-END-ANGLE` | `Chapter25FiniteHorn: finite_horn_end_angle` | Open Chapter25 |
| 41 | `PC-F-RF-FINITE-HORN-DIRECTION-COMPACTNESS` | `Chapter25FiniteHorn: finite_horn_direction_compactness` | Open Chapter25 |
| 42 | `PC-F-RF-FINITE-HORN-CONE-CONVERGENCE` | `Chapter25FiniteHorn: finite_horn_cone_convergence` | Open Chapter25 |
| 43 | `PC-B-RF-FINITE-HORN-TWO-SCALE-COMPARISON` | `Chapter25FiniteHorn: finite_horn_two_scale_comparison` | Open Chapter25 |
| 44 | `PC-B-RF-FINITE-HORN-SMOOTH-CONE-PATCH` | `Chapter25FiniteHorn: finite_horn_smooth_cone_patch` | Open Chapter25 |


Proof continuation starts with the Chapter25 cone/radial geometry and terminal
exclusion, using the already proved `KernelSecondDerivative` identities. Then
fill the realized finite-horn cards, bounded-distance and terminal/ancient
extension producers. Keep the buffer and same-map invariants above. Do not
promote these interface checks or their conditional assemblies to proof status.

### 9.3 Verified proof continuation (2026-09-08, source commit31a49361c)

The skeleton remains **44/44 covered**. Its original39 own proof slots now have
**37 explicit obligations remaining (94.9%)**; two slots have proof bodies
(5.1%). This is a count of the original slots, not an effort estimate or a claim
that5.1% of the chapter's mathematics is complete. One removed slot is a
conditional assembly. The six earlier explicit obligations remain unchanged.

`ClosedBadPointSelection.exists_closed_window_bad_point` proves the actual
closed-time selection argument with `OrientedWitness`, preserving both time
endpoints, the whole selected backward window, and tangent orientation. Its
consumer `Chapter25Theorems.closed_bad_point_selection` is now standard-only.
The countersequence/normalization adapter is still open.

`Chapter25Entropy.spatial_no_local_collapsing` now uses the exact
`scalarFromRmRadius` conversion from `strong_scalar_no_local_collapsing` in
arbitrary dimension. The conversion is proved; its strong-scalar producer is
still an own Chapter25 obligation, and this consumer still audits with
`sorryAx`.

Three new leaves add16 standard-only public theorems:

- `ConeKoszul` (9): the actual local cone bilinear form, its derivative, and the
  native Levi-Civita identities for the radial and radial dilation fields.
  The metric equality holds on a neighborhood, not merely at the center.
- `ConeRadialCurvature` (6): a local concurrent field is killed by the actual
  curvature; corresponding native Rm04, Rm13 and Ricci identities; cone radial
  curvature follows from the proved connection computation.
- `ClosedBadPointSelection` (1): the closed-window selection producer above.

All five changed leaves passed the focused/named-build checks below, serially
with one Lean thread in the accepted23:11--00:10UTC exclusive window. The three
new leaves have empty focused output and no local lint warnings. The two
skeleton leaves have only their remaining explicit-obligation warnings.

| Leaf | Focused check (s) | Named build (s) | Own open | Earlier open |
|---|---:|---:|---:|---:|
| `ConeKoszul` | 18.2 | 23.5 | 0 | 0 |
| `ConeRadialCurvature` | 15.3 | 18.9 | 0 | 0 |
| `ClosedBadPointSelection` | 30.2 | 46.7 | 0 | 0 |
| `Chapter25Entropy` | 28.9 | 39.3 | 4 | 3 |
| `Chapter25Theorems` | 35.1 | 47.1 | 10 | 2 |

The other skeleton debt remains Geometry0/0, Convergence2/0, FiniteHorn11/0 and
Extension10/1 (own/earlier). A fresh26.2s external `#print axioms` audit checks
all66 public theorems from the six skeleton leaves plus these three new leaves:
18 standard-only,48 conditional. All17 audited data definitions are
standard-only. This census does not include the chapter's older helper leaves.
Standard-only means no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

Source and artifact hashes, exact final attempts, complete logs, all83 axiom
results, unique aggregate imports and the current debt census are in
`E:/lean-tools/chapter25-cone-20260908/completion.json`. The shared audit commit
`31a49361ceb8794fcbe63b495b31340158974690` already contains these exact Lean
changes; it also contains other-lane work and was not created by this task.
The earlier skeleton receipt is preserved as historical evidence.

`cone_terminal_exclusion` remains open. The next producer must realize the
actual `ConeChart` through angular charts/open pullback metrics, apply the
checked model identities there, and transfer them back to the original metric.
Then prove the traced covariant kernel variation and the terminal Ricci-flow
evolution contradiction. A possible direct Ricci route uses the radial Ricci
kernel and `nabla_X partial_r = r^-1 X` to obtain a positive radial Laplacian at
a nonflat point. This route still requires its geometric and evolution proofs;
none is supplied as an extra hypothesis to the public endpoint.

Compiler lesson: rewriting a separately proved radial-field equality avoids
unfolding the entire Levi-Civita connection during `change`. ConeKoszul then
checks at the default heartbeat limit; increasing it to600k did not fix the
unfolding route. Keep the local covector normed instances and product-domain
`ContinuousLinearMap.ext` pattern recorded in the adjacent note.

### 9.4 Earlier Ch23 delivery and common terminal interfaces (2026-09-09 review)

This source/reference review was made while proof work was paused; the user
resumed Chapter25 at 00:14UTC. The review itself changes the intended delivery
order, not theorem status or the counts in §9.3. `ConeLocalMetric` and
`ConeChartCoordinates` still await verification. Coordination is through this
plan and `WORKING_STATUS.md`.

**First cross-chapter delivery: the fixed model window.** The exact target is
`chapter23_modelCurvatureBoundNearBase`: choose `K(kappa)` before every scalar-one
three-dimensional ancient model, then bound its actual `rmNormSq` by `K^2` on
the radius-3 ball for the time-zero metric, at every time in `[-4,0]`.
The shorter route is already expressed by native declarations:

1. `StandardHarnackLimit.ancientKappaThree_toKLim` preserves the actual flow and
   produces `KLim`. Its saved focused/build/axiom receipts establish a conditional
   consumer; the earlier `hamilton_ancient_trace_harnack_at_terminal` remains an
   explicit dependency. It uses the existing bound of a standard ancient
   solution, without proving a boundedness upgrade for an arbitrary `KLim`.
2. `SeedVolume.exists_klim_seed_volume` and
   `exists_normalized_bounded_distance_scalar_constant` give the written route
   to one positive `C(kappa,3)` for every such model and every point in the closed
   terminal radius-3 ball. The seed chain remains source-written with pending
   verification and transitive upstream obligations; it is not an unconditional
   delivered result.
3. The verified `KLim.rmNormSq_le_of_terminal_scalar_le` already converts a
   terminal scalar bound `B` to `rmNormSq t y <= 3 * B^2` for every `t <= 0`.
   Thus take `K(kappa) = sqrt(3) * C(kappa,3)`. The scalar-one basepoint and
   closed-ball distance conversion must use the actual model data. No outward
   neck comparison, global boundedness upgrade or full fixed-kappa compactness
   is needed for this final assembly.

This follows the book's `lem:ksol-seed-volume`, normalized bounded-distance and
buffered-parabolic chain in `master05a.tex` around lines 29318--29433. The current
`UpstreamModelCurvature.lean` docstring still cites full fixed-kappa compactness;
revise it with the next authorized source edit. Deliver and audit this narrower
endpoint first to unlock model-dependent good-point derivatives and local
propagation; its consumer checks do not close the earlier analytic debts.

**Use one common convergence contract.** `UpstreamLocalAncientFlowCompactness`
currently retains one spatial map family and canonical spatial data but returns
metric convergence separately at each time. This does not imply the uniform
closed-window comparison required by `Chapter25Convergence.ConvergesOn`.
Reuse `Compactness/Foundations/PointedMaps.SourceSpacetimeConvergenceData` as the
existing core for uniform spatial jets over compact sets and closed time
windows. Adapt it using the same time-independent terminal maps, canonical
domains/reference metrics, eventual source-interval and domain containment,
and actual image capture. `MetricSourceCapture` is a separate requirement from
`ConvergesOn`; do not conflate the two. Actual mixed jets and terminal left
derivatives still require their Ricci-flow evolution and slot corrections.
Do not create a parallel Chapter25 convergence hierarchy to hide this gap.

For passing Harnack alone, prioritize the smaller fixed-time spatial `C^4`
route: use interior scalar evolution to express the time derivative by the
actual spatial jets, pass the inequality on the same maps, then extend to the
terminal time. This is not a substitute for full uniform spacetime convergence.
The general one-sided calculus theorem already exists in Mathlib:
`hasDerivWithinAt_Iic_of_tendsto_deriv` in
`Mathlib/Analysis/Calculus/FDeriv/Extend.lean`. Interior `f' = q`, continuity of
`f` to the endpoint, and a continuous extension of `q` supply its hypotheses;
reuse it rather than introducing another general analysis theorem.
The remaining obligations are the actual scalar-evolution realization,
continuity of its right-hand side to the endpoint, and carrier/derivative
adapters. For cone-terminal exclusion, also establish the required tensor
evolution and fixed-frame identifications: a scalar left-derivative adapter
alone does not prove the tensor contradiction. The resumed native-API search
found the closer producer
`Evolution/Scalar/IntrinsicDerivation.scalarEvolution_of_isSolution` (and
`scalar_curvature_evolution`), which already derives the interior equation from
`IsSolutionOn`; use it instead of the more heavily packaged `Scalar/Basic`
consumer. Its coordinate proof uses the existing `coordRicciEvol` API. This
does not supply terminal continuity of the second spatial curvature derivatives.

Resumed source checkpoint00:49UTC: the cone route now uses the Euler field
Z = r partial_r. ConeLocalMetric/ConeChartCoordinates construct it on an
actual open neighborhood with nabla Z = id; ConcurrentKernelHessian
differentiates the native Ricci kernel and traces metricNabla2Ric to 2R in an
actual basis/inverse metric. RicciTerminalDerivative reuses ricciPairCoord
and Mathlib's existing endpoint theorem to give the left derivative and
nonpositive sign at a past-nonnegative null pairing, conditional on the
actual ricciPairRHS being continuous from the left. All these new bodies are
UNVERIFIED. Still realize the coordinate reaction cancellation and terminal
RHS continuity before applying them to cone_terminal_exclusion. Native
solutionOnRestrictOpen/isSolutionOn_restrictOpen already provides the local
flow, so no replacement flow definition or ambient global field is needed.

Source checkpoint00:59UTC: ConcurrentRicciEvolution now reconstructs the
actual coordinate pairing in the native basis, cancels both reaction terms
using the curvature/Ricci kernels, and identifies ricciPairRHS with 2R.
This source is UNVERIFIED and does not establish terminal RHS continuity.

The finite-horn ambient contract has a concrete mathematical obstruction:
replace the ambient space by Completion W x Real and the inclusion by
x |-> (x,0), with ambient_end=(endpoint,0). Completeness, injectivity,
continuity, local distance equality and the axial distance identity all hold.
But the inclusion has empty interior, so its entire image lies in its
frontier. For an axial sequence w_j approaching the missing endpoint,
inclusion(w_j) itself belongs to outer_frontier, contradicting frontier_escape.
Thus finite_horn_end_rays does not follow from the current FiniteHorn fields.
This is an interface obstruction, not a Lean elaboration failure. Reconstruct
the actual ambient length-space/open-domain and global product-tube provenance
from the geometric producer; do not assume the card's desired conclusion.
An open-embedding field alone would remove this product-space example but
would not establish ambient path realization or the global radial barrier.

**Keep the mathematical separations.** Locally controlled preliminary `KLim`
limits and the later global boundedness upgrade remain distinct goals. Growth
of `C(kappa,D)` with `D` supplies no global bound. In particular, do not invoke
a splitting theorem requiring global bounded curvature to prove that very
bound in the rank-one branch; retain the local closed-slab/terminal-contact
route. Fixed-kappa and universal outputs also remain distinct. The book's
universal noncollapse theorem excludes shrinking spherical space forms, whereas
its universal derivative estimates include them through the separate round
cover argument. Do not transfer the first theorem's exception into the second.

### 9.5 Verified cone identities and consultation boundary (2026-09-09 01:50 UTC)

Source commit `8f59c3f28f983450aec70a7fba0b1597ccf906a9` contains five new
proof leaves, the two reviewed schema corrections and five own root imports.
All five new leaves have empty focused diagnostics, successful named lint
builds and a fresh external axiom audit. Their **21 public theorems and three
definitions use only propext, Classical.choice and Quot.sound**.

- `ConeLocalMetric` extends the actual open model metric near a chosen point,
  transports actual curvature through the partial chart, and pushes a smooth
  concurrent field to its actual open image. The ordinary product model norm
  is retained.
- `ConeChartCoordinates` uses the original surface chart and cone map to
  prove radial curvature vanishing and produce a local smooth field with
  covariant derivative equal to the identity. Neither identity is assumed in
  `ConeChart`.
- `ConcurrentKernelHessian` differentiates the actual Ricci kernel and traces
  its native second covariant derivative to `2 * metricScalarAt`.
- `ConcurrentRicciEvolution` reconstructs the actual coordinate pairing,
  cancels both reaction terms, and proves `ricciPairRHS_concurrent`.
- `RicciTerminalDerivative` proves the terminal left derivative and its
  nonpositive sign at a past-nonnegative null pairing, **conditional on the
  explicitly stated continuity of the actual Ricci evolution right-hand side**.
  It does not establish that analytic input or close `cone_terminal_exclusion`.

`Chapter25Convergence` and `Chapter25FiniteHorn` also passed their focused and
named checks, with exactly their two and eleven original placeholder warnings.
The unchanged `Chapter25Extension` and `Chapter25Theorems` passed fresh focused
checks and named refreshes through the corrected exports. The external audit
checked 107 names: 59 standard-only (including 20 data definitions) and 48 with
`sorryAx`. Those 48 conditional consumers remain conditional. The original
Chapter25 denominator is unchanged: **37 of 39 own slots remain (94.9% of
slots, not an estimate of remaining work)**. No new proof placeholder was added.

Exact final attempts, timings, source/artifact hashes and all axiom outputs:
`E:/lean-tools/chapter25-cone-chart-20260908/completion.json`.
Verification used the shared external wrapper from this dev checkout in
Chapter23's explicit 01:09--01:55 exclusive window, serial one-thread workers;
no REPL, child worker, root build or cross-checkout source copy was used.

The requested continuation has reached two concrete consultation questions:
(1) local terminal continuity of the actual Ricci evolution right-hand side
under the existing `IsSolutionOn` assumptions, or a local maximum-principle
route avoiding it; (2) a source-faithful ambient length-space/open-domain and
global tube package for the seven finite-horn cards. The product-space
counterexample in section9.4 rules out proving the latter from the current
raw ambient fields. Exact source snapshots and verification evidence accompany
`E:/lean-tools/chapter25-consult-20260909/REQUEST.md`; no consultation has been
sent externally. Do not resume by silently strengthening the flow or assuming
the horn card conclusions.


### 9.6 Consultation implementation in progress (2026-09-09)

The local consultation was read and its25 source hashes and1345 quoted lines
matched the then-current checkout. Neither supplied Lean proposal was already
verified. Resume implements the useful route in native leaves, without
importing the consultant's conditional wrapper as a completed producer.

The arbitrary-length ray approximation and EndAngles monotonicity were too
strong: an outer obstacle can obstruct minimizing connectors while leaving
the deep end unchanged. Their quantifiers now use a positive deep cutoff;
all full approximating arms/cross-connectors and the independent two-variable
angle limit are retained. EndRayLocality derives zero angle iff equality of
short representatives and the exact metric-quotient fiber relation. The
ordered neck tube and ambient/source-capture producers are still open.

TerminalCarrierBounds produces actual metric and curvature bounds on compact
carrier slabs using fixed reference unit tangents and tensor norm comparison.
TerminalLocalBounds applies first-exit twice, uses a fixed-duration translated
Shi window, and assembles a local moving-covariant derivative bound before the
terminal time. A native auxiliary complete metric supplies the reference
compact ball; this does not assume the original flow is complete.
TerminalJetLimits identifies finite uniformly Cauchy coordinate jets with
the actual terminal metric, with no extra derivative or subsequence.

Each new proof body is counted only after its separately logged verification.
TerminalCovariantBounds adapts the existing arbitrary-order `covOrder_Ico_tail`
and actual `solnTowerSwap_reg`, using `ricTower_normSq_le` to supply moving Ricci
bounds. This avoids building another connection-difference induction. The native
`timeLipschitz_of_hasDerivAt` and `chartJet_sub_le` offer the next direct route to
uniformly Cauchy coordinate jets; no duplicate subsequence compactness framework
is needed. Actual terminal Ricci RHS continuity remains open. No new placeholder
was added; cone_terminal_exclusion is not yet closed.

TerminalMetricTimeControl now has the actual common-buffer assembly, and
TerminalChartJets has the source-written full-family terminal Gram-jet endpoint.
One fixed chart neighborhood works for every derivative order. The Gram basis
is `chartModelBasis`, which must not be identified with `Module.finBasis` by
definitional equality. Native `ChartRicciJet` and `Coordinates/RicciJet` already
give smooth finite-jet Ricci/Christoffel operators and their actual-coordinate
identities; these are the next candidate route to the Ricci Hessian RHS.
TerminalJetLimits78c82ccd4, TerminalCarrierBoundsf80b2cf53,
TerminalLocalBounds690f56b19, TerminalCovariantBounds40290984b,
TerminalMetricTimeControldd3733053 and TerminalChartJets2a4dd851a have passed
their full verification triples: 16 public theorems, all standard-only.
TerminalRicciJetOperators23ba4921e adds four standard-only public theorems,
including the full-family actual terminal Ricci-jet endpoint; seven new terminal
leaves and20 public theorems are now verified. The revised ray signatures passed
their full triple in4de02c1f9; EndRayLocality remains in the verification queue.
Actual Ricci Hessian/RHS continuity and cone closure still
remain to be assembled. No full common-map spacetime compactness is claimed.

04:29 handback: EndRayLocality focused3 is EMPTY (30.18s); its named build,
fresh audit and root registration are deferred to honor the window handback.
Chapter25Extension/Chapter25Theorems refresh through the revised finite-horn
exports is also pending. TerminalRicciHessian claimde0e884f contains the native
spatial frame helpers and a general actual totalNabla0S chart formula, all
UNVERIFIED. Next assemble Ricci/Hessian component convergence from the checked
Ricci jets, then actual Ricci RHS continuity and the original cone exclusion.
Current root claim6634fc0c is released, host Lean/Lake0, and Chapter23 receives
the early return through05:20. Its ACK04:17 accepted the following Chapter25
05:20--06:20 window. Await its actual return before restarting compiler,
artifact refresh or root registration. Source work continues in the Hessian leaf.

04:55 source checkpoint: TerminalRicciHessian now reconstructs actual second
covariant Ricci components and gives draft left continuity in the fixed tangent
tensor fiber. TerminalRicciRHS then assembles the actual lower-order carrier
terms and extends the interior equation as a left derivative. The new
ConeTerminalExclusion source restricts the original flow to the actual open
neighborhood carrying the concurrent field, using the existing
solutionOnRestrictOpen/isSolutionOn_restrictOpen producers. Six public proof
bodies in these three leaves remain UNVERIFIED. No new terminal regularity,
completeness, model convergence or curvature bound is assumed. The original
cone slot is not closed until the source/check/build/axiom chain is complete.

Source audit for the later oriented-window adapter: `RealTimeInterval`
(Analysis/TimeInterval.lean) only stores an open regular subset of the carrier;
it does not identify it with the carrier interior. Therefore `window_mem`
alone cannot justify time smoothness at a newly created lower endpoint.
Copying `ModelComparison.mono` is also insufficient: the new comparison uses
`derivWithin` on its actual closed window, and set inclusion does not preserve
that total derivative without a differentiability or germ argument (already
the absolute-value function on [-1,1] versus [0,1] distinguishes them at0).
Before implementing that adapter, establish the actual regular-window/jet
restriction argument and audit its generic interval assumptions. No conclusion
about impossibility of the full existential witness theorem is asserted here.

### 9.7 Original cone terminal exclusion closed (2026-09-09)

The original `cone_terminal_exclusion` is now proved, not merely a conditional
wrapper with an added terminal-regularity or Hessian-continuity input.
Its fresh audit is exactly `[propext, Classical.choice, Quot.sound]`.
The actual original flow supplies the closed-carrier compact bounds, local
shifted Shi bounds, fixed-background time control, actual terminal spatial
jets, Ricci covariant Hessian continuity and the terminal left derivative.
The local cone's concurrent radial field then gives the contradiction.
Source commit `00bd34ae3`; the final focused/named/audit attempts are recorded
in section4 and `E:/lean-tools/chapter25-terminal-local-20260909/`.

The original skeleton retains **44/44 label coverage**. Of its39 own proof
slots, **36 remain explicit obligations (92.3% of slots)**. Three have proof
bodies: closed bad-point selection and cone exclusion are standard-only;
spatial no-local-collapsing remains a conditional assembly. The six earlier
explicit obligations remain. Current original-file census: Entropy7,
Convergence2, FiniteHorn10, Extension11, Theorems12 placeholders, total42;
36 are own obligations and6 earlier inputs. Slot percentages are not estimates
of remaining mathematical effort.

This closes consultation question1. Question2 remains substantive: the
finite-horn construction must return the actual ambient open domain/length
geometry, ordered global neck tube and source capture needed by its seven
cards. The height-zero inclusion into `Completion W × Real` still disproves
frontier escape from the present raw ambient fields. Local end-ray quotient
consequences do not supply that missing producer. The terminal continuity
proved here concerns one actual flow; it does not claim the Chapter23/25
common-map uniform spacetime compactness interface.

Final downstream refresh: Extension focused1/named1 and Theorems focused1/named1
passed with only their11/12 existing placeholder warnings. The fresh
six-endpoint downstream audit remains conditional as expected. The four new
leaves contribute15 standard-only public declarations (14 theorems and one
definition); the original cone wrapper is also standard-only. All source,
artifact and final-attempt identities are recorded in `cone-completion.json`
in the external receipt directory above. Source/root changes and section4
logs are committed separately; no other-lane source or new proof placeholder
was introduced. The next substantive horn task remains the producer described
above, not a terminal-regularity assumption or another quotient wrapper.

### 9.8 Fixed-collar shortening and actual horn data (2026-09-09)

The local shortening chain is verified through the actual current horn API:
`CollarShortening` (4 theorems), `CollarMetricControl` (8), `CollarNoReturn`
(3), and `FiniteHornCollar` (1). All16 public theorems have empty final
focused diagnostics, named builds, and fresh standard-only axiom audits.
The exact source/artifact hashes and final attempts are reconciled in
`E:/lean-tools/chapter25-terminal-local-20260909/collar-completion.json`.
Commits and verification times are in section4. The native endpoint is
`exists_finiteHorn_collar_shortening_depth` (`358545bae`).

This proves an actual transverse replacement, not just an arithmetic margin.
The reference sphere is the compact connected unit round sphere; time zero
in CylinderReference has twice its metric. Only the reference family at time
zero is identified, so the horn's constant family is consumed directly.
A fixed depth is chosen first; every sufficiently long collar contains the
same useful subcollar, with saving greater than one half in scalar-normalized
length. The curve-containment hypotheses remain explicit.

The user-requested neck-side repair is integrated as `2d19f3b8d`. FiniteHorn
now records a global smooth product presentation, cofinal product subends,
essential whole chosen central spheres, and common closure-buffered whole
arms/connectors. Six new geometric helper theorems are standard-only after
the parent's refresh and fresh18-public audit. These prove consequences of
given global maps. The horn constructor still has to produce those maps;
the extra data are not a completed gluing theorem.

The next local step is ambient first-exit control. The existing native
`closedBall_subset_image_of_metric_lower` in WitnessBallCapture already uses
compact model balls and actual lifted curves; adapt its same-model statement
to the IC-to-I3 chart. The new height-distance bound confines reference balls
to compact sphere slabs, so reference completeness should not be added just
to obtain compactness. This would control curves leaving the collar and
connect the contained-curve result to actual ambient distance bounds. The
present four leaves do not yet assert that extension.

The remaining global obstruction is unchanged: replacing the raw ambient
space by Completion W times Real leaves the recorded tube geometry intact
but makes every included point a frontier point. Thus arbitrary raw ambient
frontier escape is still false, even with the new topological data. The actual
source-domain provenance and distance/source-capture control must be supplied
by the geometric construction; topology or compact slabs alone do not imply
intrinsic equals ambient distance or existence of every required minimizing arm.

Original accounting remains44/44 skeleton labels and36/39 own proof slots
unfilled (92.3% by slots, not effort), plus6 earlier explicit obligations.
The original source census still has42 placeholders. New support theorems and
new geometric records do not reduce that denominator until an original own
argument is actually closed.

Current-interface downstream verification is complete: EndRayLocality's nine
public declarations remain standard-only after its fresh check/build/audit.
Extension and Theorems pass focused checks and named builds with only their
11/12 original placeholder warnings; the fresh six-endpoint audit retains
their expected sorryAx dependencies. Section4 records the exact final attempts.

### 9.9 Ambient collar confinement and compact minimizers (source-written, 2026-09-09)

Six new leaves now have proof bodies, all UNVERIFIED until the next explicit
compiler/artifact window. They are not new original-slot closures:

- CrossModelBallCapture: the existing WitnessBallCapture first-exit proof with
  different source/target models, then closed-ball capture and confinement of
  every prefix endpoint of a short ambient curve.
- CylinderBallCapture: reference balls lie in compact full-sphere slabs by
  the checked height-distance inequality. A C0 error at most one half yields
  ambient ball capture at half the collar radius, compact smaller closed balls,
  and a lower length bound for any curve which ever leaves the collar.
- AmbientCollarShortening: if D is the transverse shortcut bound, fix depth
  4(D+1) before precision. A single ambient exit then costs more than D+1/2.
  This removes prior chart containment from the shortening and near-minimizer
  trapping conclusions.
- FiniteHornAmbientCollar: consume the current cylindrical_tail with its exact
  constant reference family and scalar normalization, retaining whole ambient
  curves in a compact fixed subcollar.
- CompactCurveMinimizer: reuse the native complete-metric construction which
  agrees near a compact set and dominates the original metric. Near-minimizer
  trapping proves equality of the two distances; the auxiliary minimizing
  geodesic is therefore trapped and realizes the original distance smoothly.
  No completeness or geodesic-convexity input is added for the original metric.
- CollarMinimizer: instantiate that compact-minimizer theorem for every pair
  of points on a chosen central sphere; cancel the positive scalar normalization
  in the actual horn consumer, so its conclusion uses the original metric.

The six files contain18 public theorem bodies. External audit fixtures and
draft source hashes are prepared in
`E:/lean-tools/chapter25-terminal-local-20260909/ambient-source-draft.json`.
This receipt explicitly records UNVERIFIED status. No new artifact or root
import has been produced. Claims and the requested next09:00--10:00UTC window
are recorded in WORKING_STATUS.md; Chapter23's through09:00 window is respected.

The new local minimizers concern points on one chosen central sphere. Global
inner/outer slab trapping for arbitrary deep-end pairs, all radial-arm
connectors, actual horn construction, and the raw ambient/source-provenance
defect remain separate obligations. The original36/39 count is unchanged.

Two further SOURCE-WRITTEN leaves extend the intrinsic endpoint argument:
FiniteHornTransverseControl derives the uniform D/sqrt(R) distance bound to
an actual axial point from the full central sphere and its recorded axis
crossing, then uniform deep-tail proximity to the finite axis. FiniteHornEndpoint
uses positive global height on compact sets and compact thickening to separate
deep tails from every closed positive-parameter axial segment. Therefore the
entire deep tail approaches the actual completion endpoint. Axial cofinality
gives membership in each closure, yielding exactly the `unique_endpoint`
intersection. Covering a very deep piece by one endpoint ball and the
remaining compact product slab by finitely many balls also proves compactness
of each tail closure in the intrinsic completion. These seven additional
theorem bodies are UNVERIFIED and do not yet close an original EndGeometry
slot or its still-invalid ambient fields. The updated draft receipt covers
all25 public theorem bodies in the eight new files.

FiniteHornRadialNeighborhood adds four further UNVERIFIED proof bodies. The
actual global product gives connectedness and finite Riemannian edistance,
so the intrinsic distance equality has no toReal(infinity) ambiguity. A compact
cross-section has a positive gap from the missing endpoint. A short curve
from a short axial point cannot cross this section; therefore every fixed
subend contains an intrinsic endpoint ball. Any sequence approaching the
endpoint eventually enters every fixed tail. The nine-file draft now contains
29 public bodies; ambient provenance and the original slot count are unchanged.
