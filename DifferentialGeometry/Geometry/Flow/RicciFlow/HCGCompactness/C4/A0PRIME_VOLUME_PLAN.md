# A0′ `VolumeComparisonInput` producer — lane plan + dispatch prompts

Created 2026-07-24 (planning session).  Lane protocol: a Fable orchestrator
session owns this plan and the acceptance loop; individual bricks are
dispatched to Opus executor sessions/subagents with the preamble in §6.
Update §8 (Status) after every brick; this file is the running source of
truth for the lane.

## 0. Mission

Build the honest producer for the unconditional-Thm-3.9 input **A0′**:

- Target structure: `VolumeComparisonInput` in
  `DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/C4/StepAInputs.lean`
  (lines ~108–127).  Its one deep field is `ballMult`: for every ratio
  `m : Real`, every member `k`, every finite `r`-separated center family with
  the joint cap `m * r ≤ r0`, at most `Imult m` centers lie within `m·r` of
  any fixed point `z`.
- Consumer context: `MetricCompactBase` (`C4/MetricCompactnessInputs.lean`
  ~line 546) stores `volume : VolumeComparisonInput X` together with
  `dist_eq : volume.dist = decay.dist`.  So the producer must return the
  input **for a supplied distance**, not invent its own.
- Deliverable endpoint (names ≤ 20 letters, adjust freely):

  ```
  theorem volInput_of_bg
      (X : PointedRiemannianSeq I) (bg : SeqBoundedGeometry X)
      (hd : InjRadiusDecayInput X) (hreal : hd.RealizesEdist)
      (hcpl : <per-member completeness, weakest form the checked
              Hopf–Rinow entrypoint needs>)
      (r0 : Real) (hr0 : 0 < r0) :
      { vc : VolumeComparisonInput X // vc.dist = hd.dist }
  ```

  `hd` is consumed ONLY for `hd.dist`/`hreal` (distance realization); the
  proof must not use `hd.decay` — A0′ is mathematically independent of CGT.
  If a cleaner signature avoids `hd` entirely (taking
  `dist : PointedSeqDistance X` plus a realization predicate) and still lets
  `MetricCompactBase.dist_eq` be discharged, prefer it.

Hard rules: do NOT modify `VolumeComparisonInput`, `StepAInputs.lean`,
`GoodCovering*.lean`, or any Step-A consumer.  No new axioms.  Statement
strength is settled by the 2026-07-05 honest-input audit
(`PROJECT_MAP.md` §4): the capped form is TRUE as stated; produce exactly it.

## 1. Read-first

Working tree: `E:\testdifferential-geometry-ste-align` (branch
`codex/short-time-existence-align`).  `CLAUDE.md`/`AGENTS.md` rules apply
(lake-locked workflow, file claims, naming budget, honest-`sorry` policy).
Then: `HCGCompactness/PROJECT_MAP.md` §2 and §4 (A0′ row), this file, and the
same-name `.md` of any file you touch.  Keep tool output small (`rg -n`,
narrow windows).

## 2. Why the easy route is insufficient (do not rediscover this)

`Imult : Real → Nat` depends only on `m` — the bound must hold at every
`z`, arbitrarily far from the basepoint, with the SAME constant.  Any route
through normal-chart/small-ball absolute volume bounds needs charts of size
comparable to `r`, but injectivity radius decays (CGT: `~ e^{-C·d}`) along
the sequence members, so chart-based constants degrade with distance and
cannot give a distance-uniform `Imult`.  (Model picture: hyperbolic thin
parts — tiny injectivity radius, yet the multiplicity bound still holds.)

Therefore the producer MUST go through **relative Bishop–Gromov volume
comparison past the cut locus** (Ricci lower bound only, no injectivity
input).  This is the single genuine frontier of the lane; there is currently
NO cut-locus / segment-domain layer in the tree (grep for
`cutLocus|segDomain|cutTime` returns nothing).  Everything else below is
assembly on existing sorry-free machinery.

## 3. Mathematical route

Fix one member `(M, g, p)` with `Rm04` bound `Λ := bg.C 0`, hence
`Ric ≥ -(n-1)·C₀·g` with `C₀ = C₀(n, Λ)` (brick B1).  Let `v(s)` denote the
model volume `hypRadVol C₀ (n-1) s`-style (already defined in
`Comparison/Volume/BishopBall.lean`).

**(a) Capped relative Bishop–Gromov (brick B5, fed by B2–B4).**  For
`0 < s ≤ R ≤ Rcap := 8 * r0`, in multiplicative form (avoid division):

```
V(x, R) * v(s) ≤ v(R) * V(x, s)
```

where `V(x, t)` is `riemannianVolumeMeasure` of the open `edist`-ball.  As a
byproduct the same representation gives the absolute upper bound
`V(x, R) ≤ v(R) < ∞` (finiteness is needed in the counting step).

**(b) Counting (brick B6).**  Degenerate case `m < 1/2`: two distinct
centers would satisfy `r ≤ d(cᵢ,cⱼ) ≤ 2mr < r` — contradiction, so
`card ≤ 1`; set `Imult m := 1` there.  Main case `m ≥ 1/2`, `mr ≤ r0`:
pick `j₀ ∈ J`; the balls `B(cⱼ, r/2)` are pairwise disjoint and contained in
`B(c_{j₀}, (2m+1)r)`; conversely `B(c_{j₀}, (2m+1)r) ⊆ B(cⱼ, (4m+2)r)`.
Apply (a) at each `cⱼ` with `s = r/2`, `R = (4m+2)r`
(`(4m+2)r = (4 + 2/m)(mr) ≤ 8·r0 = Rcap` since `m ≥ 1/2`):

```
V(cⱼ, r/2) ≥ V(c_{j₀}, (2m+1)r) * v(r/2) / v((4m+2)r)
```

Summing disjoint balls inside `B(c_{j₀}, (2m+1)r)` and cancelling the
positive finite `V(c_{j₀}, (2m+1)r)` (positivity from
`SmallBall.edist_vol_pos`, finiteness from (a)) gives
`card ≤ v((4m+2)r) / v(r/2)`, which under the cap is bounded by an explicit
`Imult m = ⌈(8m+4)^n · exp((n-1)·√C₀·Rcap)⌉`-shaped constant (derive the
clean monotone bound from the model-volume structure; exact constant is
free).  The abstract counting chain in `Comparison/Volume/Packing.lean`
(`balls_disjoint`, `balls_subset_ball`, `ball_card_le_of_vol`,
`card_le_of_mul_lt`) should carry this step — reuse, do not reprove.

**(c) Decomposition of (a) — where the real work is.**

- (α) **Segment-domain polar representation with cut-time truncation** — the
  frontier (brick B2).  For complete members, every point of `B(x, R)` is
  `exp_x(v)` along a minimizing geodesic (point-pair Hopf–Rinow, already
  checked in-tree by the Route B′ lane); minimizing segments have no
  interior conjugate points (`not_conj_of_min_len` / `tail_not_conj_of_min`
  family, checked).  Needed outputs:
  1. upper form: `V(x,R) ≤ ∫_{SegDom ∩ B_R(0)} J ≤ v(R)` — the image-measure
     inequality direction needs NO injectivity
     (`measure_image_le`-style change of variables + Jacobian upper bound on
     the conjugate-free star-shaped set);
  2. relative form: per-direction cut profile `τ(θ)`, star-shapedness
     (`t·θ ∈ SegDom` for `t < τ(θ)`), measurability, and the polar Fubini
     `V(x,t) = ∫_{sphere} ∫_0^{min(t, τ(θ))} J` (or an inequality pair
     sufficient for (a)).
- (β) **Radial density ratio monotonicity** under `Ric ≥ -(n-1)C₀` (brick
  B3): `J(t,θ)/j_{C₀}(t)` nonincreasing in `t` up to `τ(θ)` — Riccati/index
  comparison; the tree already has `JacobiRiccati`, `RadialGronwall`,
  `BishopJacobi`, `BishopRadial`, `BishopIntrinsic` (the Calabi lane's
  "intrinsic Bishop comparison including dimension one" is this layer's
  derivative form).  Expect reuse or thin adapters, not new theory.
- (γ) **Ratio-of-integrals lemma** (brick B4): if `f/g` is monotone then
  `∫₀^R f · ∫₀^s g ≥ ∫₀^s f · ∫₀^R g` in the truncated-domain form needed by
  (α)(2) — pure measure theory, check Mathlib
  (`inner_le_nnorm`-unrelated; look for Chebyshev/`MeasureTheory` ratio
  monotonicity) before writing one.
- (δ) counting = (b); (ε) sequence uniformization: `SeqBoundedGeometry.bound`
  gives the SAME `C₀` for every member, so all constants are `k`-free by
  construction.

**Fallback discipline:** if (α)(2) resists after three genuinely different
routes, STOP; leave the capped-ratio statement (a) as one precisely stated
`sorry` frontier, report per §7, and do NOT ship a weakened or
extra-hypothesis producer instead.  The upper form (α)(1) alone is NOT
sufficient for `ballMult` — do not deliver only it and call the lane done.

## 4. In-tree machinery (planner's grep, 2026-07-24; re-verify shapes before use)

Sorry-free at source level (whole `Geometry/Comparison/Volume/` tree):

- `Comparison/Volume/Packing.lean` — abstract counting chain (see §3(b)).
- `Comparison/Volume/BishopBall.lean` — `hypRadVol` model volume,
  `exists_framed_ratio`, `normalBall_ratio` (chart-scale ratio results:
  useful shapes, insufficient strength — see §2).
- `Comparison/Volume/BallVolume.lean` — `metricBall_meas`,
  `metricBall_subset_smallNormalBall`, two-sided chart-scale bounds,
  `Rm04GlobalBound`.
- `Comparison/Volume/BishopPolar.lean` (`normalBall_polar`),
  `NormalChartMeasure.lean`, `RadialGram.lean`, `IntrRadialFrame.lean`,
  `RadialRadius.lean` — polar/measure ingredients within the framed chart;
  B0 must determine how far they go toward (α).
- `Comparison/Volume/JacobiRiccati.lean`, `RadialGronwall.lean`,
  `JacobianBounds.lean` (pointwise upper density suite),
  `BishopJacobi/BishopRadial/BishopLocal/BishopIntrinsic.lean` — (β) layer.
- `Comparison/Volume/SmallBall.lean` — `edist_vol_pos` (positivity),
  `exists_ball_vol_low`; `FamilySmallBall.lean` is the settled noncollapse
  producer — do NOT refactor either.
- Checked geometry from the Route B′/Calabi lane: point-pair Hopf–Rinow,
  basepoint-free completeness, `not_conj_of_min_len`, `tail_not_conj_of_min`,
  `tail_no_conj` (grep for exact locations; some live near
  `Comparison/DistanceCalabi.lean`).

Warnings:

- `Comparison/HopfRinow.lean` contains 8 `sorry`s in OTHER variants; consume
  only the checked entrypoints and confirm the capstone's closure with
  `#print axioms` under a real build (remember the `lake env lean`
  false-green lesson: exit 0 and `#print axioms` are only trustworthy after
  `lake-locked build` of the module).
- Elaboration gotchas already paid for in this subtree: keep the local
  `MeasurableSpace M := borel M` / `BorelSpace` instance pattern and the
  `attribute [-instance] Tensor0SBundle.tangentSpace_*` header used by
  `FamilySmallBall.lean`; `open scoped ENNReal` clashes with ContDiff `∞`;
  if a structure appears to reject well-typed fields, `#check @TheStruct`
  for an InnerProductSpace-vs-NormedSpace section mismatch before rewriting
  the proof.

## 5. Bricks and dispatch order

New reusable mathematics goes under `Geometry/Comparison/Volume/` (canonical
home); only the sequence-level producer goes in a NEW file
`HCGCompactness/C4/VolumeOverlap.lean` (+ same-name `.md`).  Keep every new
file ≤ 3000 lines; split by abstraction boundary (suggested:
`SegmentDomain.lean` for (α) set/measurability, `BishopGlobal.lean` for
(a)).  Each brick = one Opus dispatch with the §6 preamble; acceptance =
focused check green + no new axioms + note updated.

- **B0 (read-only inventory, cheap).**  Verify §4 claims; record in §8 the
  exact names/shapes covering (β), (γ), what `BishopPolar`/`RadialRadius`
  already give toward (α), the checked Hopf–Rinow/no-conjugate entrypoint
  names, and whether a `HasCurvDerivBound 0 → Ric ≥ -(n-1)C₀` bridge exists.
  Output: go/no-go plus the precise starting statement for B2.
- **B1.**  Ricci-lower-bound bridge from `bg.C 0` (skip if B0 finds it).
- **B2 (THE frontier; independent full session, not a subagent).**
  (α): segment-domain set, star-shapedness, measurability, Hopf–Rinow
  surjectivity, image-measure upper bound, cut-time profile + truncated
  polar representation/inequalities.  Deliver in the (1)→(2) order so the
  upper bound lands even if (2) stalls.
- **B3.**  Ratio monotonicity (β) as reuse/adapters on the Riccati layer.
- **B4.**  Truncated ratio-of-integrals lemma (γ).
- **B5.**  Capped relative BG (a), multiplicative form, on one member.
- **B6.**  `ballMult` counting core (b) on one member, `Imult` explicit,
  degenerate `m` cases included, via the `Packing.lean` chain.
- **B7.**  Sequence assembly `volInput_of_bg` + the `vc.dist = hd.dist`
  subtype; distance hypotheses transported through `RealizesEdist`
  (`edist`-balls vs supplied `dist`: separation/containment translate via
  `edist_eq` + `dist_nonneg`).
- **B8.**  Cleanup per CLAUDE.md: discharge obsolete helpers, axiom replay
  of the capstone, update this §8, `PROJECT_MAP.md` A0′ row, and the
  same-name `.md`s.

B3/B4 are independent of B2 and can run in parallel with it.  B5 blocks on
B2(2)+B3+B4; B6 on B5; B7 on B6.

## 6. Executor preamble (paste verbatim at the top of every Opus dispatch)

```
Work in E:\testdifferential-geometry-ste-align (branch
codex/short-time-existence-align).  Read CLAUDE.md and
DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md
first; your brick is §5 <BRICK-ID> and its acceptance criteria are binding.
Claim files before editing:
  ./scripts/lake-locked.ps1 claim -Files <paths>
Verify with focused checks only:
  ./scripts/lake-locked.ps1 check -Token <t> -Files <path> -NoLakeLock
plus one targeted `build -NoLakeLock +Module.Name` before relying on new
exports downstream; release the claim when done.  Do not touch
StepAInputs.lean, GoodCovering*.lean, MetricCompactnessInputs.lean, or any
settled Volume/ file except to ADD new files/lemmas; no new axioms, no new
foundational classes/instances/notation; theorem names ≤ 20 letters,
Mathlib casing; weakest hypotheses that the route actually uses
(FiniteDimensional/CompactSpace acceptable when Mathlib's route needs them);
docstrings state the result, not the proof.  Prefer an honest, precisely
stated `sorry` over a wrapper that moves the gap into new hypotheses.  Stop
after three genuinely different failed routes OR on a wrong statement /
missing-API / design / performance wall, and report failure-first: exact
theorem, goal, error, routes tried, suspected obstruction class, smallest
unblocking lemma.  Record findings in the same-name `.md` (verification
pass/fail only, no logs) and update A0PRIME_VOLUME_PLAN.md §8.  Do not
expand scope beyond the brick.
```

## 7. Acceptance and reporting (orchestrator)

Accept a brick only on: focused check green on the edited files, one
targeted build green for newly exported modules, `#print axioms` clean for
capstones (under real build), consumers untouched, notes updated.  Report
progress against the ENDPOINT only: the A0′ producer is 0% until
`volInput_of_bg` is sorry-free; brick completions are machinery percentages
and must be reported as such.  On lane completion: wire nothing into
`MetricCompactBase` yet (that is the unconditional-3.9 assembly's job),
update `PROJECT_MAP.md` §4 A0′ row + §2, and close this plan with a
lessons paragraph.  Escalation: use the CLAUDE.md GPT-Pro consult template
(Case 2 — push branch, link files) after B2 exhausts three routes.

## 8. Status

- 2026-07-24: plan created; no bricks started.  Endpoint `volInput_of_bg`:
  0%.  Declared frontier: B2(α)(2) truncated polar representation (no
  cut-locus layer exists in-tree).  Machinery reuse expectation: (β)(γ)(δ)
  largely present per §4 grep; B0 to confirm.

- **B0 findings (2026-07-24).**  Read-only inventory complete (no Lean edits, no
  builds).  Verdict **GO** for B2/B3/B4 dispatch.
  1. *§4 sorry-check:* all 20 `Comparison/Volume/*.lean` files are source-level
     sorry-free.  `Comparison/HopfRinow.lean` carries **4** code `sorry`s (not 8 —
     the other 4 are prose in its header) in 3 decls:
     `exists_continuous_path_realizing_riemannianEDist` (:779),
     `minimizing_path_is_smooth_geodesic` (:818),
     `unit_speed_rescale` (:854).  Its point-pair capstone
     `exists_unit_speed_minimizing_geodesic_between_points` (:940) has a clean
     body but transitively calls all three → **tainted; do NOT use it.**
  2. *(β) usable, incl. a past-cut-locus form.*  Ratio engine is uniformly
     **Ricci**-driven (`Ric ≥ -(n-1)q²`).  J(t,θ)=`normalChartDensity`
     (`NormalChartMeasure.lean:53`) ≡ `curveDensity g (radialCurve g p x)
     (radialJacobiField …)` (`Variation/JacobiGram.lean:69`); model
     j_C₀=`hypDensity q (n-1) r` (`HyperbolicModel.lean:102`), integrated
     `hypRadVol` (`BishopBall.lean:268`).  Chart-scale master antitone ratio:
     `exists_radial_cmp` (`BishopRadial.lean:642`).  **Past cut locus:
     `exists_intrMean` (`BishopIntrinsic.lean:494`) gives the mean-curvature
     comparison along the intrinsic geodesic on `Ioo 0 b`, b>1, under a
     nonconjugacy hyp `hno` — (β) already extends past inj-radius.**  Riccati core
     `mean_riccati_le` (`JacobiRiccati.lean:450`); antitone-from-mean
     `curveRatio_anti` (`BishopJacobi.lean:134`).  Pointwise |J| bounds are
     Rm04-driven (`exists_dens_le_rm04` `JacobianBounds.lean:711`).
  3. *(α) every volume/polar representation is chart-bound.*  `normalBall_polar`
     (`BishopPolar.lean:102`), `framedBall_polar` (`BishopPolarFramed.lean:255`),
     `normalChart_volume_eq/_radial` (`NormalChartMeasure.lean:382/398`),
     `normalDensity_curve` (`RadialGram.lean:470`) all need the R-ball ⊆
     `(exp/framedExpDiffeo).source` (or tighter `expMapC2Radius`/`jacobiVarRadius`).
     **Only two α pieces survive past inj-radius, neither a volume formula:**
     `exists_intrFrame` (`IntrRadialFrame.lean:57`, un-capped parallel ON frame
     along the C^∞ `intrinsicGeodesic`) and `radialJacobi_scale`
     (`NormalChartMeasure.lean:201`).  No `cutLocus/segDomain/cutTime` exists (grep
     empty) → B2 is a genuinely new file.
  4. *Hopf–Rinow / no-conjugate — clean entrypoints (all in 0-sorry files):*
     point-pair surjectivity `hopf_rinow_expMapIntrinsic_surjective_minimizing`
     (`Exponential/MinimizingGeodesic.lean:2430`, unconditional under
     Connected+Complete) + `minExp_of_ne_top` (:2229); basepoint-free finiteness
     `riemannianEDist_ne_top` (:339); properness `properSpace_riemMetric`
     (`HopfRinowProper.lean:240`); geodesic completeness
     `isGeodesicOn_Ici_of_complete` (`HopfRinow.lean:432`); no-conjugate
     `not_conj_of_min_len` (`Variation/MinimalGeodesicNoConjugate.lean:47`),
     `tail_not_conj_of_min` (`Variation/MinimizingNoConj.lean:290`), `tail_no_conj`
     (:436).  Source-level dependency chains clean (`#print axioms` deferred to
     build).
  5. *B1 bridge EXISTS — skip B1 as research.*  `ricciLower_of_rm`
     (`BonnetMyers/RicciBound.lean:46`): `Rm04GlobalBound g Rm → RicciBoundedBelow
     g (-(finrank²·Rm))` (hyp is definitionally `Rm04GlobalBound`; **no
     CompactSpace**).  Compose with `rm04Bound_of_seq` (`BoundedGeometry.lean:183`):
     `SeqBoundedGeometry → Rm04GlobalBound (X.obj i) (hX.C 0)`.  `RicciBoundedBelow`
     antitone in κ (needs `0 ≤ g.inner`) picks model q≥n·√(Rm/(n-1)) for the
     `-(n-1)q²` Bishop form.  Coarser constant `-(n²·C₀)` but valid/uniform.  B1 =
     ~3-line composition folded into B5.
  6. *Endpoints (fields verbatim):* `VolumeComparisonInput` (`StepAInputs.lean:108`)
     = {dist:`PointedSeqDistance`, r0, r0_pos, Imult:ℝ→ℕ, ballMult(deep)}; member =
     `X.obj k : PointedRiemannianManifold` (`.M`, `.metric`, `.basepoint`).
     `PointedSeqDistance` (:49) = `∀ k, (X.obj k).M → (X.obj k).M → ℝ`.
     `SeqBoundedGeometry` (`BoundedGeometry.lean:160`) = {C:ℕ→ℝ, nonneg, bound}.
     `InjRadiusDecayInput` (:59); `RealizesEdist` (`GoodCovering.lean:252`) =
     {dist_nonneg, edist_eq}.  `MetricCompactBase`
     (`MetricCompactnessInputs.lean:539`): `volume`, `dist_eq :
     volume.dist = decay.dist`, `realizes`.
  7. *Verdict = GO.*  B2 frontier = segment-domain **polar-MEASURE** representation
     past the cut locus (α)(2); density monotonicity (β) is already intrinsic via
     `exists_intrMean`, so B2's real gap is the image-measure / truncated-polar
     change of variables for the surjective `expMapIntrinsic` — NOT the ratio.  B4
     (γ) has no in-tree truncated ratio-of-integrals (only untruncated chart-bound
     `localBall_cross` `BishopLocal.lean:141`) → new lemma / Mathlib Chebyshev.
     B2 start point + first lemma sketches delivered to the orchestrator.

- **B2 status (2026-07-25).**  Delivered two files under `Comparison/Volume/`.
  1. *`SegmentDomain.lean` — deliverable (1), **GREEN + sorry-free + no warnings**
     (focused check + targeted build; olean built).*  Set/measurability layer,
     all past the cut locus (no injectivity): `SegDom g hEnorm x :=
     {v | √(g.inner x v v) = (riemannianEDist I x (expMapIntrinsic … x v)).toReal}`;
     `segDom_smul` (star-shaped, via `intrinsicGeodesic_riemannianEDist_le` +
     triangle + `intrinsicGeodesic_smul` — NOT `subArc`/`pathELength_eq_arcLength`);
     `ball_sub_image_segDom` (Hopf–Rinow surjectivity onto the edist-ball,
     landing in `SegDom ∩ gBall`, from
     `hopf_rinow_expMapIntrinsic_surjective_minimizing`);
     `isClosed_segDom`/`measurableSet_segDom`; `gBall`/`isOpen_gBall`/`measurableSet_gBall`.
  2. *`SegmentPolar.lean` — deliverables (2)+(3) as the ONE precise `sorry`
     frontier (compiles green, 2 intended sorrys).*  `segBall_vol_le`
     (absolute `V(x,R) ≤ ofReal(hypRadVol q (n-1) R)`) and `segBall_vol_rel`
     (capped relative `V(x,R)·v(s) ≤ v(R)·V(x,s)`, the B5 input), stated in
     `riemannianVolumeMeasure`/`hypRadVol` terms — directly consumable by B5.
  3. **FRONTIER (blocks (2) AND (3)) — failure-first:** the brick premise that
     (α)(1) is a cheap `measure_image_le` change of variables is WRONG.  Mathlib's
     non-injective `addHaar_image_le_lintegral_abs_det_fderiv` (`Jacobian.lean:903`)
     is `E → E` with an **additive-Haar target**; it does NOT apply to
     `expMapIntrinsic x : T_xM → M` (target = `riemannianVolumeMeasure`, a manifold
     measure).  The in-tree change-of-variables
     (`riemannianVolumeMeasure_image_param_eq`, `normalChart_volume_eq`) is
     **diffeomorphism-only** (fails past the cut locus).  Smallest unblocking
     lemma = **non-injective area inequality for a `C¹` map `E → M`** into a
     Riemannian manifold (`riemannianVolume_image_le_lintegral_density`, home =
     `Analysis/Integration/Measure/`), built by countable chart-partition + the
     Euclidean `addHaar_image_le` per piece + Jacobi-density identification; it
     also needs off-zero differentiability of `v ↦ expMapIntrinsic x v` (only
     at-zero + variational forms in-tree; `expMap_contMDiffAt_of_ne_zero` is for
     the chart-fixed `expMap`).  Given that lemma, (β) (`curveMean_le_hyp`/
     `exists_intrMean`, intrinsic past the cut locus) + Euclidean polar of
     `hypDensity` close `segBall_vol_le`; `segBall_vol_rel` further needs the
     truncated polar Fubini (`τ(θ)`) + B4.  Obstruction class = **missing reusable
     API** (manifold area formula + off-zero exp regularity), not proof-search.
     Endpoint `volInput_of_bg`: still 0%.  Details in
     `Comparison/Volume/SegmentDomain.md` + `SegmentPolar.md`.

- **Orchestrator B2 review (2026-07-25) — PARTIAL ACCEPT + one statement
  rejection.**  ACCEPTED: `SegmentDomain.lean` (independently grep-verified
  0 `sorry`); `segBall_vol_rel` as the frontier statement (multiplicative
  form is normalization-independent — the sphere-mass constant cancels —
  and it passes flat-ℝⁿ and dim-1 sanity checks).  REJECTED as stated:
  `segBall_vol_le` — **FALSE by the dimensional sphere-mass factor**.
  Counterexample: flat ℝ² (q = 0, `RicciBoundedBelow g 0` holds):
  `V(x,R) = πR²` but `hypRadVol 0 1 R = R²/2`.  The polar route's `toSphere`
  total mass (= finrank · vol(unit ball)) is silently dropped.  Fix
  dispatched back to the B2 session (scope-locked): restate with the
  explicit dimension-only constant, add B6-facing corollary
  `segBall_vol_fin` (`V(x,R) < ⊤`), keep `segBall_vol_rel` unchanged,
  record the counterexample in `SegmentPolar.md`.  LESSON for this lane:
  sorry'd frontier statements get NO compiler truth-check — the acceptance
  loop must sanity-check them against model cases before consumers build
  on them (this catch is exactly why).  Frontier re-map after B2: the
  lane's one genuine frontier is now the **manifold-valued non-injective
  area inequality** (`E → M`, `riemannianVolumeMeasure` target) + off-zero
  differentiability of `expMapIntrinsic`, feeding both sorrys; Pro consult
  on that decomposition queued per §7 (three routes exhausted on the
  original (α)(1) premise).

- **B2 ACCEPTED IN FULL (2026-07-25, after correction).**  Fix verified:
  `segBall_vol_le` restated with the explicit finite sphere-mass constant
  `σ = (modelHaar E).toSphere Set.univ`; flat-ℝ² is now equality-shaped;
  counterexample + "do not re-drop σ" recorded in the docstring; NEW proved
  corollary `segBall_vol_fin` (`V(x,R) < ⊤`, no own `sorry`) gives B6 a
  constant-independent interface; `segBall_vol_rel` byte-identical;
  `SegmentDomain.lean` untouched (0 `sorry` re-verified); exactly two code
  `sorry`s in `SegmentPolar.lean` (:120, :174).  DISPATCH DECISION: B6
  (counting) goes out NOW against the stated interface (`segBall_vol_rel`
  + `segBall_vol_fin` + open-pos positivity) — it never needed the frontier
  closed; B5 is re-scoped to "discharge the two SegmentPolar sorrys" and
  waits on the area-inequality API brick (B5-pre) informed by the Pro
  consult (prompt: `C4/A0PRIME_AREA_CONSULT.md`).  Endpoint `volInput_of_bg`:
  **0%** (machinery only).

- **B2 correction landed (2026-07-25).**  `segBall_vol_le` restated with the
  explicit dimension-only constant `σ := (modelHaar E).toSphere Set.univ`
  (`= finrank · vol(unit ball)`, finite via `Measure.toSphere`'s
  `IsFiniteMeasure` instance; `toSphere_apply_univ` gives the closed form):
  `V(x,R) ≤ σ · ofReal(hypRadVol q (n-1) R)`.  Flat-ℝ² check now equality
  (`πR² ≤ 2π·(R²/2)`), dim-1 `2R ≤ 2·R`.  Added `segBall_vol_fin`
  (`V(x,R) < ⊤`) — **PROVED** as a corollary of `segBall_vol_le` (only frontier
  dependency is the latter's `sorry`), stable B6 interface.  `segBall_vol_rel`
  UNCHANGED.  Counterexample recorded in `SegmentPolar.lean` header +
  `SegmentPolar.md`.  Focused check + targeted build green; exactly two
  `sorry`s (`segBall_vol_le`, `segBall_vol_rel`).  Frontier unchanged (the
  manifold-valued non-injective area inequality).

- **Orchestrator dispatch record (2026-07-24).**  B0 ACCEPTED (read-only
  verified: git clean of Lean edits).  B1 SKIPPED per §5 (bridge exists, B0
  item 5; the ~3-line `rm04Bound_of_seq` ∘ `ricciLower_of_rm` composition is
  assigned to B5).  Dispatched in parallel with the §6 preamble: **B2**
  (independent Opus session; target `Comparison/Volume/SegmentDomain.lean`,
  deliverables in (1)→(2)→(3) order, hard warning against the tainted
  HopfRinow.lean capstone), **B3** (Opus subagent; target
  `Comparison/Volume/IntrinsicRatio.lean`, deliverable 1 = pointwise upper
  density flagged as B2 import; independent of B2's SegDom names by design),
  **B4** (Opus subagent; target `Comparison/Volume/RatioIntegral.lean`,
  Mathlib-first).  B5 blocks on B2(2/3)+B3+B4; B6 on B5; B7 on B6; B8 last.
  Support files ported into this slim checkout root today (CLAUDE.md,
  AGENTS.md, convention/dictionary/lessons/important_lesson.md, scripts/) —
  they are git-ignored here, deliberate.  Endpoint `volInput_of_bg`: **0%**
  (unchanged; nothing above machinery until B7).

- **B4 status (2026-07-25) — DONE, sorry-free, verified.**  New file
  `Geometry/Comparison/Volume/RatioIntegral.lean` (+ `.md`), geometry-free, only
  Mathlib measure-theory/order/ENNReal imports.  Namespace
  `...Riemannian.VolumeComparison`.  Focused check + targeted module build both
  PASSED; no new axioms, no new imports beyond Mathlib.
  1. *Mathlib-first (per brick):* NO integral-form Chebyshev / monovary ratio
     inequality exists in Mathlib's MeasureTheory tree.  Chebyshev is finset-only
     (`Algebra/Order/Chebyshev.lean`); `MonovaryOn` has no integral form;
     `ChebyshevMarkov`/`Lebesgue/Markov` are the unrelated tail-bound Markov.
     ⟹ proved from scratch.  In-tree `localBall_cross` (`BishopLocal.lean:141`) is
     the untruncated chart-bound analog (shape pattern only, not reusable).
  2. *Delivered (names ≤ 20 letters, Mathlib casing):*
     - `CrossAnti R f g : Prop` := `∀ a b, 0<a → a≤b → b≤R → f b*g a ≤ f a*g b`
       (division-free `ℝ≥0∞` form of "f/g antitone on (0,R]"; a `def` so the three
       lemmas compose).
     - `lintegral_cross_le` (main, γ): general `μ : Measure ℝ`, hypotheses
       `AEMeasurable f/g (μ.restrict (Ioc 0 R))` + `CrossAnti R f g` + `0 ≤ s ≤ R`
       ⟹ `(∫_{Ioc 0 R} f)*(∫_{Ioc 0 s} g) ≤ (∫_{Ioc 0 s} f)*(∫_{Ioc 0 R} g)`.
     - `crossAnti_ofReal` (bridge = part 2): `AntitoneOn (F/G) (Ioc 0 R)` + `F≥0`,
       `G>0` on window ⟹ `CrossAnti R (ofReal∘F) (ofReal∘G)`.
     - `crossAnti_indicator` (truncation = part 3): `CrossAnti R f g →
       CrossAnti R (indicator (Iio τ) f) g`, any `τ` (lower-set argument).
  3. *Route:* disjoint split `Ioc 0 R = Ioc 0 s ∪ Ioc s R`; common `If*Ig` is
     ADDED not subtracted (`∞-∞`-safe, `add_le_add le_rfl`), reducing to
     `Jf*Ig ≤ If*Jg`; reshape both products into the SAME iterated `∫_B ∫_A`
     (`lintegral_const_mul''`/`mul_const''` under `lintegral_congr`) and compare
     pointwise by `hcross` via nested `lintegral_mono_ae` + `ae_restrict_mem`.
     Multiplicative `ℝ≥0∞` form avoids division and integrability side conditions.
  4. *B5 handoff:* apply `crossAnti_ofReal` to the per-direction Jacobian /
     model-density ratio (β, `exists_intrMean`-driven), then `crossAnti_indicator`
     at the cut time `τ(θ)`, then `lintegral_cross_le` with `s`,`R` the two radii.
     Endpoint `volInput_of_bg` still **0%** (B4 is machinery).

- **B4 ACCEPTED by orchestrator (2026-07-25).**  Independent re-verification:
  `RatioIntegral.lean` grep-clean of `sorry`/`axiom`; consumers untouched (git
  surface = B4's two new files only, besides B2/B3 in-flight edits); independent
  targeted build of `+…Comparison.Volume.RatioIntegral` PASSED.  γ is banked;
  B5's (γ) input is `lintegral_cross_le` ∘ `crossAnti_indicator` ∘
  `crossAnti_ofReal` exactly as in the handoff above.

- **B3 status (2026-07-25) — ALL deliverables DONE, sorry-free, verified.**
  New file `Geometry/Comparison/Volume/IntrinsicRatio.lean` (+ `.md`); one producer
  ADDED to the END of settled `BishopIntrinsic.lean`.  Both edited modules pass a
  targeted `lake build` sorry-free (only pre-existing `HopfRinow.lean` sorrys remain
  in the graph, B0-known).  No new axioms; no new imports beyond `BishopIntrinsic` +
  `Variation/MinimizingNoConj`; namespace `...Riemannian.VolumeComparison`.
  Consumers (StepAInputs/GoodCovering/MetricCompactnessInputs, settled Volume files)
  untouched; `BishopIntrinsic.lean` edit is additions-only.
  1. *Producer `exists_intrRatio` (BishopIntrinsic.lean, END).*  Companion to
     `exists_intrMean`: same transverse-Jacobi setup (reuses the file's `private`
     `intr*` helpers), concludes `AntitoneOn (fun t => curveDensity g γ V t /
     hypDensity (q*ell) (n-1) t) (Ioo 0 b)` via `curveRatio_anti ∘
     curveMean_le_hyp`.  Speed-scaled model `q*ell`, `ell = √⟨u,u⟩` (true form).
     Hyp `hd : 0 < finrank-1` (drops `exists_intrMean`'s d=0 branch — dim ≥ 2 in
     every BG use); window `Ioo 0 b` with nonconjugacy `hno` on the same window,
     no `1<b`.  **This `AntitoneOn` output is B4's `crossAnti_ofReal` (β) input
     directly** (B4 does the cross-multiplication) — B5 restricts `Ioc 0 R ⊆
     Ioo 0 b`.
  2. *Deliverable 2 `intrCross_anti` — DONE.*  Division-free
     `curveDensity t · hypDensity s ≤ curveDensity s · hypDensity t` for
     `s ≤ t` in-window, from the antitone ratio + `hypDensity_pos` (`div_le_div_iff₀`).
  3. *Deliverable 3 `intrNoConj_min` — DONE.*  `∀ t ∈ Ioo 0 1, ¬IsConjVec …` on
     the shifted minimizing tail, from `tail_no_conj` (`Ioo 0 1 ⊆ Ioc 0 1`);
     supplies `hno` with base `z.proj`, dir `uTail`, `b=1`.  Independent of B2's
     SegDom names by design.
  4. *Deliverable 1 `intrDens_le_hyp` (PRIORITY; B2 import) — DONE, UNCONDITIONAL.*
     `∃ v (frame), LI ∧ perp ∧ ∃ N>0, ∀ t ∈ Ioo 0 b, curveDensity g γ V t ≤
     N·hypDensity (q*ell) (n-1) t`.  Two proved pieces: `densUB_of_pole` (generic
     antitone-ratio + near-pole cap ⟹ uniform pointwise bound; the ratio sup is at
     the pole) and `intrPoleCap` (the near-pole cap, **discharged**).  The pole cap
     was the declared missing-API frontier (no light near-pole upper density in the
     tree) but assembles from PUBLIC pieces: `exists_perp_basis`
     (`LinearIndependent.option` + `basisOfLinearIndependentOfCardEqFinrank`, Option
     basis from `u`+perp frame) → `normalDensity_curve` (chart↔curve identity on a
     small window) → `normalChartDensity` `ContinuousAt 0` (re-derived from PUBLIC
     `paramDensity_contOn`) → `hypDens_ge_pow` (`hypSn q t ≥ t`) → `intrJacobi_raw`
     transfer, giving `N = (normalChartDensity 0 + 1)/c`.  **Type-synonym norm trap
     paid** (`‖r•(u:E)‖` takes the metric norm, not `E`'s — bind `let ue : E`; see
     `.md`).  B2 can import `intrDens_le_hyp` NOW as a sound theorem.  Endpoint
     `volInput_of_bg` still **0%** (B3 is machinery).

- **B3 ACCEPTED by orchestrator (2026-07-25).**  Independent re-verification:
  `IntrinsicRatio.lean` grep-clean of `sorry`/`axiom`; `BishopIntrinsic.lean`
  diff is 156 insertions / 0 deletions (additions-only confirmed); consumers
  untouched; independent targeted builds of `+…Volume.BishopIntrinsic` and
  `+…Volume.IntrinsicRatio` both PASSED.  One open nit for B8: style lint at
  `IntrinsicRatio.lean:242` (`show`-tactic warning) — mechanical, deferred to
  avoid churning a green file B2 may be importing right now.  (β) is banked;
  B5's (β) feed = `exists_intrRatio`'s `AntitoneOn` output → B4's
  `crossAnti_ofReal`, with `intrNoConj_min` supplying `hno` and
  `intrDens_le_hyp` covering the absolute-bound/finiteness side.

- **B5-pre scout findings (2026-07-25).**  READ-ONLY orchestrator scout (no
  Lean edits, no claims, no builds; four parallel sub-scouts + first-hand
  reads).  Caveat: align checkout has NO built Mathlib (`.lake/packages/mathlib`
  absent); Mathlib statements below are source-read from the sibling
  `E:\testdifferential-geometry\.lake` (same foundation).  Nothing here is
  compile-verified — statements are read, not built.
  1. *VERDICT: chart-partition route (i) = **MODERATE**, and it is the SHORTEST.*
     Alt-routes (ii null-cut-locus+diffeo-CoV, iii direct polar) BOTH collapse
     onto the SAME non-injective `E→M` area inequality; (ii) is strictly worse
     (needs an open strictly-minimizing-star `PartialDiffeomorph` with NO in-tree
     def — `SegDom` is CLOSED (`isClosed_segDom`), includes cut endpoints — plus a
     "cut locus is `riemannianVolumeMeasure`-null" fact that is CIRCULAR: it is
     itself a C¹-image-of-null `E→M` statement needing the same machinery). (iii)
     still needs the `E→M` `≤` to absorb the `ball ⊆ exp''(SegDom∩gBall)`
     multiplicity, plus a per-direction truncated-polar slice that does not exist
     (only whole-ball diffeo-only `normalBall_polar`/`framedBall_polar`).  So do (i).
  2. *KEY QUESTION answered: the measure IS chart-local by construction and the
     per-chart UPPER bound is NEAR-DEFINITIONAL.*  `riemannianVolumeMeasure g =
     riemannianMeasure g (chartAtlasPOU)` (`Invariance.lean:423`) `= Measure.sum
     (α ↦ (chartLocalMeasure g α).withDensity (ofReal∘ρ α))` (`RiemannianMeasure.lean:71`).
     `riemannianVolumeMeasure g S ≤ ∑' α, chartLocalMeasure g α S` assembles from
     EXISTING lemmas: `Measure.sum_apply` (equality `= ∑' α (…withDensity ρα) S`,
     used inline `Properties.lean:242`) + `pou_term_le_chartLocalMeasure`
     (`Properties.lean:195`, **PRIVATE** — de-privatize; proof is `ρα≤1` + two
     `setLIntegral_mono`) + `ENNReal.tsum_le_tsum` + `chartLocalMeasure_lintegral`
     (`Invariance.lean:472`, per-chart pullback to `modelHaar`); collapse `∑'`
     over M to countable via `countable_nonempty_support_of_pou` (`Invariance.lean:922`).
     The diffeo-only EQUALITY CoV `riemannianVolumeMeasure_image_param_eq`
     (`ParamEvaluation.lean:1428`, takes `PartialDiffeomorph 𝓘(ℝ,E) I E M 1`) is
     NOT needed for the `≤`.  Instances (all `theorem`s, not registered): sigmaFinite
     `Properties.lean:346`, isOpenPos `:646`, regular `:667`, locallyFinite `:326`.
  3. *Mathlib Euclidean area lemma EXISTS with the exact needed shape.*
     `addHaar_image_le_lintegral_abs_det_fderiv` (`Jacobian.lean:903`):
     `(hs:MeasurableSet s)(hf':∀x∈s,HasFDerivWithinAt f (f' x) s x) : μ(f''s) ≤
     ∫⁻ x in s, ofReal|det(f' x)| ∂μ` — `E→E` (SAME space, `.det`), additive-Haar
     target, **NO injectivity**, pointwise `HasFDerivWithinAt` (not ApproxLinOn,
     not a.e.), `f'` arbitrary.  Injective `=`/reverse-`≤` siblings (`:1101`,`:1056`)
     add `InjOn`.  Partition kit: `ChartedSpace.secondCountable_of_sigmaCompact`,
     `isOpen_iUnion_countable`, `disjointed`+`MeasurableSet.disjointed`, and the
     upper-bound-only aggregators `measure_iUnion_le` / `lintegral_iUnion_le`
     (no disjointness).
  4. *FRONTIER-A (regularity) is TWO-TIERED — plan/consult text is WRONG here.*
     `expMap_contMDiffAt_of_ne_zero` **DOES NOT EXIST** (doc-comment only, incl.
     `SegmentPolar.lean:55` and `A0PRIME_AREA_CONSULT.md:34`).  Real chart-fixed
     lemmas are the small-ball `_of_norm_lt` family (`OffZero.lean:353`/`:1171`,
     `GaussLemmaPullback.lean:276`) — gated `‖w‖<δ`, NOT arbitrary `v≠0`.  Off-zero
     C¹ of `v↦expMapIntrinsic x v`: **none exists**; only at-0 `mfderiv_…at_zero`
     (`IntrinsicMfderivZero.lean:57`, `=id`) + the `(s,t)`-VARIATIONAL
     `expMapIntrinsic_variation_contMDiff` (`ExpVariationSmooth.lean:829`, map
     `(s,t)↦expMapIntrinsic (γ t)(s·(V₀ t).snd)` — does NOT specialize to joint-in-`v`).
     New lemma `expMapIntrinsic_contMDiffAt_of_ne_zero` SPLITS: ROUTINE for SMALL
     `v₀` (via `exists_expMapIntrinsic_eq_expMap_radius` `MinimizingGeodesic.lean:756`
     + `congr_of_eventuallyEq`), **genuine FRONTIER for LARGE `v₀`** (geodesic
     leaves home chart ⟹ cross-chart ODE smoothness-in-velocity; `expMap=expMapIntrinsic`
     is local-only, global is false/frontier).  Large `v` is exactly the BG regime.
  5. *FRONTIER-B (density identity) = THE RISKIEST SINGLE STEP.*  Need
     `mfderiv_v(expMapIntrinsic x)` = radial Jacobi map ⟹ `|det D(extChartα∘
     expMapIntrinsic x)_v|·chartDensityα(exp v) = curveDensity` past the cut locus.
     Template exists ONLY in the diffeo regime: `normalDensity_curve`
     (`RadialGram.lean:470`, for `normalChartDensity = paramDensity(expMapDiffeo)`).
     Couples to FRONTIER-A (needs the large-`v` differential).
  6. *One extra measure helper the naive premise missed:* Mathlib's `:903` is
     UNWEIGHTED (`g≡1`); `chartLocalMeasure` carries the `chartDensity` weight, and
     the weighted image `∫⁻_{f''s} w` non-injective `≤ ∫⁻_s (w∘f)·|det f'|` is NOT
     in Mathlib (weighted `=` needs `InjOn`, `:1189`).  Derivable from `:903` by
     simple-function approximation of `w` (`w=∑cᵢ1_{Tᵢ}`, `f''(s∩f⁻¹Tᵢ)=f''s∩Tᵢ`,
     monotone conv) — a ~40–80-line helper, NOT a frontier.
  7. *Smallest lemmas, dependency order (suggested homes):*
     (L1) `expMapIntrinsic_contMDiffAt_of_ne_zero` [Exponential/Smoothness/] —
       small-`v` routine, large-`v` FRONTIER-A;  (L2) velocity-differential =
       radial-Jacobi + `|det(chartα∘exp)|·chartDensity = curveDensity`
       [Comparison/Volume/, near RadialGram] — FRONTIER-B, riskiest;  (L3) weighted
       non-injective Euclidean area `≤` [Analysis/Integration/Measure/] — helper
       from `:903`;  (L4) de-private + name `riemannianVol g S ≤ ∑' chartLocalMeasure`
       [Properties/Invariance] — near-definitional;  (L5) `riemannianVolume_image_le_
       lintegral_density` (`E→M` non-inj area, `SegmentPolar.md:67`) [Measure/] =
       L2+L3+L4+countable-chart-partition — the bridge feeding BOTH sorrys;  (L6)
       `segBall_vol_le` = L5 + (β `intrDens_le_hyp`/`exists_intrMean`) + Euclidean
       polar (`toSphere`/`volumeIoiPow`/`hypRadVol`, σ factor);  (L7) `segBall_vol_rel`
       = L5 + truncated polar (`τ(θ)`) + B4 (`lintegral_cross_le`/`crossAnti_indicator`).
     RISKIEST = L1(large-`v`)+L2 coupled (off-cut-locus velocity-Jacobian of the
     intrinsic exp); L3/L4 routine, L5–L7 assembly on in-tree/Mathlib parts.
  8. *Consult impact:* validates the `A0PRIME_AREA_CONSULT.md` decomposition
     (Route i is right, smallest frontier = `E→M` non-inj area) but CORRECTS two
     premises for the Pro prompt: (a) `expMap_contMDiffAt_of_ne_zero` is fictional —
     off-zero exp regularity is itself a large-`v` frontier, not an existing lemma;
     (b) the area lemma must be the WEIGHTED non-injective form (chartDensity weight),
     assembled per-chart, not a bare `measure_image_le`.  Endpoint `volInput_of_bg`:
     still **0%** (this is a read-only scout; no machinery moved).

- **Orchestrator post-scout dispatch (2026-07-25).**  Scout ACCEPTED (git
  surface = plan file only).  Route decision ADOPTED: chart-partition (i).
  Brick split per scout L-numbering: **B5a = L3+L4** (weighted non-injective
  Euclidean area `≤` + public per-chart `≤`-decomposition lemmas) — ROUTINE,
  dispatched NOW in parallel with the in-flight B6; **B5b = L1(large-v)+L2
  (+L5 assembly)** — the lane's single genuine frontier (cross-chart
  velocity-differentiability of `expMapIntrinsic` + chart-Jacobian ↔
  `curveDensity` identity), HELD until the Pro consult lands or, if browser
  access stays unavailable after B5a+B6 acceptance, dispatched
  scout-informed by explicit orchestrator decision (recorded then).
  `A0PRIME_AREA_CONSULT.md` REVISED per scout corrections (a)+(b) and
  re-focused on L1(large-v)+L2 only; submission still blocked on browser.
  B8 punch-list grows: fix `SegmentPolar.lean:55`-area doc-comment citing
  the fictional `expMap_contMDiffAt_of_ne_zero` (scout item 4), plus the
  `IntrinsicRatio.lean:242` `show` lint.  Endpoint: **0%**.

- **B5a status (2026-07-25) — DONE, sorry-free, verified (L3 + L4).**  Both pieces
  landed; focused check + targeted module build GREEN for each; grep-clean of
  `sorry`/`axiom`; no new axioms; consumers untouched.
  1. *L3 — `MeasureTheory.image_lintegral_le`* in NEW file
     `Analysis/Integration/Measure/JacobianImageLe.lean` (+ `.md`), `namespace
     MeasureTheory` (sits with its parent).  Weighted non-injective Euclidean area `≤`:
     `hs`, `hf : Measurable f`, `hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x`,
     `hw : Measurable w` ⟹ `∫⁻ y in f''s, w y ∂μ ≤ ∫⁻ x in s, w (f x)·ofReal|(f' x).det| ∂μ`
     for `μ` additive-Haar on a finite-dim real normed `E`.  Route = per-set Mathlib
     `addHaar_image_le_lintegral_abs_det_fderiv` (Jacobian.lean:903) → `SimpleFunc.induction`
     → LHS-only monotone convergence.  **KEY:** the Jacobian weight `|det f'|` is NOT assumed
     measurable; this forces the additive step through the unconditional superadditivity
     `le_lintegral_add` (Lebesgue/Add.lean:248) and confines all limits to the image side —
     the measure-pushforward and layer-cake routes both DIE on weight-measurability
     (`withDensity`/Tonelli).  `Measurable f` (only) is the honest added hyp (base case needs
     `f⁻¹'T` measurable; the intended `expMapIntrinsic x` is smooth ⟹ measurable).  Mathlib
     search: no weighted non-injective form exists (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`
     is `InjOn` + equality).
  2. *L4 — public per-chart upper decomposition* ADDED to `Properties.lean` (additions-only,
     34 ins / 0 del; private `pou_term_le_chartLocalMeasure` and all existing statements
     untouched).  `vol_le_tsum_supp` (PRIMARY):
     `riemannianVolumeMeasure g S ≤ ∑' α, chartLocalMeasure g α (S ∩ tsupport (chartAtlasPOU I M α))`.
     `vol_le_tsum_chart` (the brick's literal shape, kept as a documented coarsening):
     `riemannianVolumeMeasure g S ≤ ∑' α, chartLocalMeasure g α S`.  Route = `…_def` →
     `Measure.sum_apply` → `pou_term_le_chartLocalMeasure` → `ENNReal.tsum_le_tsum`.
  3. **STATEMENT CORRECTION (flag for L5).**  The brick's literal L4 target
     `∑' α : M, chartLocalMeasure g α S` is **generically `⊤`** — `chartLocalMeasure g α` is
     supported on `(chartAt α).source`, so a fixed positive-measure `S` is seen by uncountably
     many chart sources ⇒ the unrestricted sum diverges and the bound is vacuous.  The usable
     bound is `vol_le_tsum_supp`: the `tsupport (ρ α)` restriction makes every summand vanish
     off the **countable** `{α | support (ρ α) ≠ ∅}` (`countable_nonempty_support_of_pou`,
     Invariance:922).  L5 should consume `vol_le_tsum_supp`, not `vol_le_tsum_chart`.  (Same
     class as the B2 σ-mass catch — sanity-check bounds on the model case.)
  4. *modelHaar pullback for L5 — not re-added* (brick: only if missing).  Already public/usable:
     `chartLocalMeasure_setLintegral_indicator` (Invariance:573, `F := fun _ => 1`) and
     `chartLocalMeasure_lintegral` (:472).
  5. *B8 punch-list note:* the `[Module.Finite ℝ E]` unusedSectionVars warning on
     `vol_le_tsum_supp`/`vol_le_tsum_chart` is pre-existing and file-wide in `Properties.lean`
     (un-`omit`able: the var is referenced by the section instance graph); not introduced here.
  Endpoint `volInput_of_bg`: still **0%** (L3/L4 are machinery; B5b L1+L2 remain the frontier).

- **B5a ACCEPTED by orchestrator (2026-07-25).**  Independent re-verification:
  `Properties.lean` diff 34 ins / 0 del (additions-only confirmed);
  `JacobianImageLe.lean` grep-clean of `sorry`/`axiom`; independent targeted
  builds of both modules PASSED.  The item-3 ⊤-flag is ADOPTED as the L5
  contract: **B5b must consume `vol_le_tsum_supp`** (tsupport-restricted),
  never the coarse `vol_le_tsum_chart`; the countable collapse is
  `tsum_subtype_eq_of_support_subset` + `countable_nonempty_support_of_pou`.
  Two acceptance-loop catches in one lane (B2 σ-mass, B5a ⊤-sum) confirm the
  standing rule: every bound stated for the frontier gets a model-case
  sanity check before consumers bind to it.  Remaining pre-B5b state: B6 in
  flight; consult still browser-blocked.

- **B6 status (2026-07-25) — DONE, sorry-free, verified.**  New file
  `Geometry/Comparison/Volume/SegmentCount.lean` (+ `.md`).  Consumes
  `segBall_vol_rel` + `segBall_vol_fin` (SegmentPolar) AS STATED; adds **no
  `sorry`**.  Focused check GREEN + warning-clean; targeted build
  `+…Volume.SegmentCount` PASSED (only `sorry`s in the whole import chain are the
  two intended SegmentPolar frontiers, now at `SegmentPolar.lean` decls :107/:159,
  bodies :120/:174).  No new axioms/classes/instances/notation; consumers
  (StepAInputs/GoodCovering/MetricCompactnessInputs, settled Volume files)
  untouched.
  1. *Public names for B7.*  `segImult (n : ℕ) (q r0 m : ℝ) : ℕ` =
     `⌈e^{8q(n-1)r0}(16m+8)ⁿ⌉ + 1` (member-independent; `n = finrank ℝ E`).
     `le_segImult`, `one_le_segImult` (the two facts B6 needs about it).  Main
     theorem **`segBall_card`**: signature mirrors the `ballMult` field but in
     `riemannianEDist`/`ENNReal.ofReal` terms —
     `(g)(hEnorm)(hq : 0≤q)(_hr0 : 0<r0)(hRic : RicciBoundedBelow g (-((finrank-1)·q²)))`
     `(hr : 0<r)(hcap : m*r≤r0){α}(centers : α→M)`
     `(hsep : ∀ i j, i≠j → ofReal r ≤ riemannianEDist I (cᵢ)(cⱼ))(z)(J : Finset α)`
     `(hJz : ∀ j∈J, riemannianEDist I (cⱼ) z ≤ ofReal (m*r))` ⟹
     `J.card ≤ segImult (finrank ℝ E) q r0 m`.  Member instance set =
     `[ConnectedSpace M][PseudoEMetricSpace M][IsRiemannianManifold I M]`
     `[CompleteSpace M][IsContinuousRiemannianBundle E (TangentSpace I)]`.
  2. *B7 wiring (mechanical).*  `Imult := segImult (finrank ℝ E) q r0`;
     `ballMult := fun m k _α _ _ centers r hr hcap hsep z J hJz => segBall_card …`.
     B7 converts the supplied `dist`↔`riemannianEDist` on the separation and
     containment hyps via `RealizesEdist.edist_eq` + `dist_nonneg` (NOT B6's job);
     `_hr0`/`Fintype`/`DecidableEq` are in B7's scope, passed positionally or
     simply not needed by `segBall_card` (the latter two were dropped — Packing
     needs neither; unusedFintype/DecidableInType linters).
  3. *Route (see `SegmentCount.md`).*  Members have NO real-`dist`
     `PseudoMetricSpace`, so the `Metric.ball` Packing lemmas don't apply —
     routed through the type-agnostic `mul_lower_le_upper` + `card_le_of_mul_lt`
     over raw `riemannianEDist`-balls, with local open/mono/shift/disj helpers
     (triangle + `riemannianEDist_comm`).  Big-ball positivity via
     `riemannianVolumeMeasure_isOpenPosMeasure` (T2+σ-compact only, **no
     CompactSpace** — members lack it) + `segBall_vol_fin` finiteness.
     `r`-independent model ratio proved WITHOUT closed-form integrals
     (`integral_pow`/FTC oleans are unbuilt in this checkout): `hypSn q τ ∈ [τ, τe^{qτ}]`
     + constant bounds on `[0,R']` / `[s/2,s]` via `integral_const` → factor-2
     cruder constant `(16m+8)ⁿ` (irrelevant to counting).  Degenerate `m<1/2`
     ⇒ `card ≤ 1 ≤ segImult` up front.
  Endpoint `volInput_of_bg`: still **0%** (B6 is machinery; frontier stays B5b
  L1+L2).  B8 punch-list unchanged (B6 added nothing to it).

- **B6 ACCEPTED + GATE DECISION (2026-07-25).**  Independent re-verification:
  `SegmentCount.lean` grep-clean (`sorry` only in prose); git surface = its
  two new files; independent targeted build PASSED (background-completed,
  3893 jobs, exit 0) on the final binder-cleaned version.  δ (counting) is
  banked; B7's wiring contract is §8 B6-status item 2.  GATE DECISION per
  the post-scout policy: browser STILL disconnected after B5a+B6
  acceptance, so **B5b (L1+L2 frontier session) is dispatched NOW,
  scout-informed**, owning the design questions the consult would have
  answered (`A0PRIME_AREA_CONSULT.md` Tasks; the prompt stays ready and an
  answer, if access appears, will be relayed to the running session).
  Brick split confirmed: B5b = L1+L2 only; **B5c** = L5+L6+L7 assembly +
  discharge of the two SegmentPolar sorrys, queued behind B5b.  **B7 is
  dispatched EARLY in parallel** (its inputs are landed; its product will
  EXIST but stay transitively sorry'd via exactly the two SegmentPolar
  frontiers — endpoint remains 0% per §7 until they close).  Endpoint:
  **0%**.

- **B5b status (2026-07-25) — DONE, sorry-free, verified (L1 + L2).**  The
  lane's declared "single genuine frontier" (L1 large-`v` regularity coupled
  with L2) **DISSOLVED** on scout re-inventory; both deliverables landed
  sorry-free.  Focused check + targeted module builds
  (`+…Exponential.Smoothness.IntrinsicOffZero`, `+…Volume.SegmentDensity`)
  GREEN; grep-clean of `sorry`/`admit`; no new axioms/classes/instances/
  notation; consumers untouched (SegmentPolar/SegmentDomain/StepAInputs/
  GoodCovering/MetricCompactnessInputs unedited).
  1. *L1 = a FALSE WALL — correction to §8 "B5-pre scout findings" item 4 and
     `A0PRIME_AREA_CONSULT.md` premise (a).*  Large-`v` velocity regularity of
     `expMapIntrinsic x` is **already in-tree, sorry-free, GLOBAL C∞**:
     `intrinsicFiber_smooth` (`Exponential/IntrinsicVelocity.lean:191`,
     `ContMDiff 𝓘(ℝ,E) I ∞ (fun v ↦ expMapIntrinsic g hEnorm p v)`), built from
     the geodesic spray `geodesicVectorField` + `flow_slice_smooth` on `TM`.
     The scout listed only `mfderiv_expMapIntrinsic_at_zero` and never grepped
     `intrinsicFiber_smooth`, the actual producer (used tree-wide).  Chain
     re-verified sorry-free (HopfRinow's 4 sorrys are unreachable from the
     velocity branch).  No new large-`v` proof exists or is needed.  NEW file
     `Exponential/Smoothness/IntrinsicOffZero.lean` adds only the
     downstream-consumable Euclidean form `expChart_contDiffAt`
     (`ContDiffAt ℝ ∞ (extChartAt y₀ ∘ exp_x) v`, from `intrinsicFiber_smooth`
     + target chart), NOT a redundant alias.  (B8 punch-list: fix the
     `SegmentPolar.lean:55`/`A0PRIME_AREA_CONSULT.md:34` doc-comments still
     citing the fictional `expMap_contMDiffAt_of_ne_zero`.)
  2. *L2 = `exp_density_curve` PROVED sorry-free* in NEW file
     `Comparison/Volume/SegmentDensity.lean` (namespace `…VolumeComparison`):
     `chartDensity g y₀ (exp_x v)·|det D(extChartAt y₀ ∘ exp_x)_v| =
     curveDensity g (intrinsicGeodesic x v) (intrinsic Jacobi frame) 1`.  LHS =
     exactly the `image_lintegral_le` integrand.  **Route C — the density
     identity is INVERTIBILITY-FREE.**  The route-decider scout established
     that the `paramDensity_eq_abs_det_mul_chartDensity` chain
     (`ParamEvaluation.lean:162→…→354`) uses `Ψ` only via `MDifferentiableAt`
     + chart membership, never invertibility.  So L2 needs **no local
     diffeomorphism, no manifold IFT, no nonconjugacy** — only
     `MDifferentiableAt`, supplied everywhere by `intrinsicFiber_smooth`; the
     differential columns are the endpoint Jacobi fields via
     `intrinsic_jacobi_one` (`JacobiVariation.lean:257`, un-capped).  The
     identity therefore **drops the nonconjugacy hypothesis** and holds for ALL
     `v` (both sides `0` at a conjugate `v`) — strictly stronger than the
     plan's "conjugate-free directions" scope.  Two reusable general-map
     helpers landed alongside: `mfderiv_chartBasis` (diffeo-free port of
     `paramDeriv_chartBasis_eq_sum`) and `gramDiff_det` (diffeo-free port of
     `paramGramMatrix_det_pullback` — the "Riemannian area Jacobian" for any
     `C¹` `f : E → M`; candidate to promote to `Analysis/…/Measure/` later).
     Routes A (IFT + `¬IsConjVec ⟹ invertible`, un-built, weaker) and B
     (duplicate the whole param layer) rejected — see `SegmentDensity.md`.
  3. *B5c handoff.*  Consume `exp_density_curve` to rewrite the
     `image_lintegral_le` integrand as `curveDensity` of the intrinsic Jacobi
     frame; then polar-decompose (Gauss lemma: radial × transverse) and apply
     the `(β)` bound `intrDens_le_hyp`/`exists_intrRatio` (transverse
     `(n-1)`-frame `curveDensity ≤ N·hypDensity`) to reach `hypRadVol`,
     discharging `segBall_vol_le`/`segBall_vol_rel`.  L2's frame is the FULL
     `chartModelBasis`-generated `n`-frame; the radial/transverse split is
     B5c's step.  L1 for the area formula's pointwise `HasFDerivWithinAt` is
     `expChart_contDiffAt.differentiableAt.hasFDerivAt` (or
     `intrinsicFiber_smooth` directly).
  Endpoint `volInput_of_bg`: still **0%** (L1/L2 are machinery; the SegmentPolar
  sorrys remain until B5c assembles L5+L6+L7).  **The lane no longer has an open
  frontier** — B5b's dissolution of the L1/L2 wall means B5c is now pure
  assembly on landed, sorry-free parts + the two SegmentPolar sorrys.

- **B7 status (2026-07-25) — DONE, own content `sorry`-free, verified.**  New file
  `HCGCompactness/C4/VolumeOverlap.lean` (+ `.md`).  Focused check + targeted build
  `+…C4.VolumeOverlap` both GREEN and warning-clean; grep-clean of `sorry`/`axiom`
  in the file; consumers untouched (git surface = the two new files only; no edit to
  StepAInputs/GoodCovering*/MetricCompactnessInputs or any settled Volume file).
  `#print axioms volInput_of_bg = [propext, sorryAx, Classical.choice, Quot.sound]` —
  **no new axioms**; the single `sorryAx` traces to `SegmentPolar.lean:107`/`:159`
  (the two intended frontiers), NOT to the HopfRinow variants (segBall_card uses the
  clean `hopf_rinow_expMapIntrinsic_surjective_minimizing`).
  1. *Endpoint `volInput_of_bg` (a `def` — result is the data subtype).*  Signature:
     `(X)(bg : SeqBoundedGeometry X)(hd : InjRadiusDecayInput X)(hreal : hd.RealizesEdist)`
     `(hcpl : SeqMetricComplete X)(hconn : ∀ k, ConnectedSpace (X.obj k).M)(r0)(hr0 : 0<r0)`
     `→ { vc : VolumeComparisonInput X // vc.dist = hd.dist }`.  `hd` used ONLY via
     `hd.dist`/`hreal` (never `hd.decay`); subtype proof is `rfl`, so
     `MetricCompactBase.dist_eq` is dischargeable.
  2. *Input-bundle decision = REUSED, no new bundle.*  Per-member instances mirror the
     proven `GoodCoveringOrdered.exists_proper_realization_aux` stack:
     `SeqMetricComplete`→`MetricComplete.complete` (CompleteSpace),
     `PointedRiemannianManifold.{riemBundle,riemBundle_cont,emetricSpace}` (bundle/emetric),
     `hconn` (connectedness, honest input — `segBall_card` + Hopf–Rinow need it, matching
     `exists_pairR_of_seqBoundedGeometry`).  Two inputs beyond §0's sketch (`hcpl`,
     `hconn`) are both genuinely required; NOT the explicit-`hRic` fallback (Ricci is
     derived internally).
  3. *Distance bridge = `rfl`-level.*  Mathlib `IsRiemannianManifold` is
     `class … where out (x y) : edist x y = riemannianEDist I x y`, proved `fun _ _ => rfl`
     by `ofRiemannianMetric`.  Installing `⟨fun _ _ => rfl⟩` + `IsRiemannianManifold.out`
     turns `hreal.edist_eq` into `riemannianEDist = ofReal (hd.dist …)`; hyps transfer via
     `ENNReal.ofReal_le_ofReal`.  `hEnorm` reuses
     `tensor0SBundle_enorm_eq_riemannianBundle_enorm` (`simpa`).
  4. *Ricci fold (the B1 fold) + dim-1 resolution.*  `q := n·√(bg.C 0)`
     (`q² = n²·bg.C 0`).  `n ≥ 2`: `rm04Bound_of_seq`→`ricciLower_of_rm` gives
     `Ric ≥ -(n²·C₀)`, transferred to `-(n-1)q²` by antitonicity in κ (inlined; needs
     `0 ≤ g.inner`).  **dim-1 (the known wrinkle) RESOLVED, not deferred:** target κ is `0`,
     antitone fails; proved `ricciTensor ≡ 0` in dim 1 (`ricci_dim1_bddBelow`) from PUBLIC
     API — `riemannOp_dim1_zero` (`riemannOp_swap` antisymmetry + `finrank_eq_one_iff_of_nonzero'`
     + triple-CLM `map_smul`) fed through `ricciTensor_apply_basisSum`.  No reusable in-tree
     dim-1 vanishing existed (only a `private` DeTurck `dim1_riemannOp_first_two_eq_zero`);
     the two helpers live locally in `VolumeOverlap.lean`.  **B8 punch-list:** relocate
     `riemannOp_dim1_zero`/`ricci_dim1_bddBelow` to the canonical curvature layer
     (`RicciConnection.lean` / `BonnetMyers/RicciBound.lean`).
  5. *B7 wiring (mechanical, as B6 handoff item 2):* `Imult := fun m => segImult (finrank ℝ E)
     q r0 m`; `ballMult` intros everything, installs member instances, builds `hRic`/`hEnorm`/
     the distance bridge, and applies `segBall_card` (its `Fintype`/`DecidableEq` binders
     discarded).
  Endpoint `volInput_of_bg`: **0%** per §7 (assembly landed; own content `sorry`-free).
  Remaining to sorry-free = ONLY the two SegmentPolar frontiers (B5b L1+L2, B5c assembly);
  `VolumeOverlap.lean` needs no edit when they close.  B8 punch-list gains item 4 above.

- **B7 ACCEPTED by orchestrator (2026-07-25).**  Independent re-verification:
  git surface = the two new files only; `VolumeOverlap.lean` grep hits are
  the honest transitive-`sorry` prose only; independent targeted build
  PASSED (3916 jobs).  The two signature additions vs §0's sketch (`hcpl :
  SeqMetricComplete X`, `hconn`) are ACCEPTED as honest inputs — §0's
  `hcpl` clause anticipated exactly "the weakest form the checked
  Hopf–Rinow entrypoint needs", and connectedness is part of that
  entrypoint's instance set; both mirror already-proven C4 stacks, and no
  Ricci/`hRic` leakage into the public signature occurred (Ricci derived
  internally incl. the from-scratch dim-1 vanishing).  The executor's
  in-build `#print axioms` (sorryAx from `SegmentPolar` only) stands as
  B7-level evidence; the FINAL capstone axiom replay stays a B8 gate.
  Lane state after B7: B0–B7 all accepted; live = B5b (frontier session);
  queued = B5c (L5–L7 + discharge), B8 (cleanup incl. the two curvature
  helpers' relocation, the fictional-lemma doc fix, the `show` lint).
  Endpoint: **0%** until the two SegmentPolar sorrys close.

- **B5b ACCEPTED — THE LANE FRONTIER IS DISSOLVED (2026-07-25).**
  Independent re-verification: false-wall claim CONFIRMED first-hand
  (`intrinsicFiber_smooth` lives in `Exponential/IntrinsicVelocity.lean`,
  file 0-sorry, consumed tree-wide — the L1 "off-zero regularity frontier"
  never existed; scout+B2 both missed the producer; memory note
  `ricciflow-agents-overcount-walls` updated with the two-stage-miss
  sub-lesson); `IntrinsicOffZero.lean`/`SegmentDensity.lean` grep-clean;
  independent targeted builds of both modules PASSED.  L2
  `exp_density_curve` is STRONGER than planned: invertibility-free, holds
  for ALL `v` (both sides vanish at conjugate points), no nonconjugacy
  hypothesis.  ORCHESTRATOR DESIGN NOTE for B5c's L5 (exact-constant
  assembly): the unweighted per-chart `≤` (`vol_le_tsum_supp`) carries
  chart-overlap multiplicity — fine for lossy steps, NOT for the exact
  `∫_A curveDensity` target.  Use the POU-WEIGHTED decomposition instead:
  `Measure.sum_apply` EQUALITY, per-summand `image_lintegral_le` with
  `w := ofReal ∘ (ρα · chartDensity α)`, then collapse with
  `Σ_α ρα (exp v) = 1` (`SmoothPartitionOfUnity.sum_eq_one`) +
  `lintegral_tsum`/countable support.  The B5a ⊤-lesson still stands
  (never the unweighted unrestricted sum).  B5c dispatched NOW.

- **B5c status (2026-07-25) — PARTIAL: L5 DONE (sorry-free, axiom-clean); L6+L7
  NOT closed; both SegmentPolar `sorry`s remain UNTOUCHED.  Endpoint
  `volInput_of_bg`: still 0%.**  Failure-first: `segBall_vol_le` /
  `segBall_vol_rel` are NOT discharged.  The brick premise that L5+L6+L7 is
  "pure assembly" is CORRECT for L5 but WRONG for L6 (see the frontier below).

  1. *L5 LANDED — the plan's identified missing bridge.*  New file
     `Comparison/Volume/SegmentArea.lean` (+ `.md`), **sorry-free, verified**
     (focused check + targeted build `+…Volume.SegmentArea`, 3818 jobs;
     `#print axioms riemVol_exp_image_le = [propext, Classical.choice,
     Quot.sound]` — no `sorryAx`, no HopfRinow taint).  Public
     `riemVol_exp_image_le`: for `IsCompact K ⊆ E`,
     `riemannianVolumeMeasure g (expMapIntrinsic x '' K) ≤ ∫⁻ v in K,
     ofReal(curveDensity g (intrinsicGeodesic x v) (intrinsic n-frame) 1)
     ∂modelHaar`, past the cut locus, no injectivity.  Route = the §8 orchestrator
     design note EXACTLY: `riemannianVolumeMeasure_def`/`riemannianMeasure_def`
     + `Measure.sum_apply` (needs `exp''K` measurable ⟸ `IsCompact K`), per-chart
     `image_lintegral_le` with `w = ofReal∘(ρα·chartDensity α)` (both `fα =
     chart∘exp` and `w` made global-`Measurable` via `Set.piecewise … 0` +
     `ContinuousOn.measurable_piecewise`), integrand rewritten by
     `exp_density_curve`, α-sum collapsed via `tsum_subtype_eq_of_support_subset`
     + `lintegral_tsum` + `tsum_ofReal_pou_eq_one`.  Private helpers
     `expJacDensity`, `expJacDensity_continuous`, `pou_term_exp_le`.

  2. *L6 is FROM-SCRATCH, not assembly (read-only scout confirmed).*  **NO
     absolute `V ≤ σ·hypRadVol` bound exists in ANY regime** — the diffeo regime
     has only the polar EQUALITY (`normalBall_polar`) and RELATIVE ratio bounds
     (`normalBall_cross`/`localBall_cross`); the ONLY `V ≤ σ·hypRadVol`-shaped
     statements in the whole `Volume/` tree are the two SegmentPolar `sorry`s.
     Given L5, `segBall_vol_le` still needs `∫⁻ v in SegDom ∩ closedGBall R,
     ofReal(curveDensity(full n-frame) v) ∂modelHaar ≤ σ·hypRadVol`, which
     requires: (a) a GLOBAL Gauss block-det factorization full n-frame →
     radial × transverse (`intrinsic_gauss` = global orthogonality exists;
     `endpoint_det_split`/`density_det_eq` in `RadialGram.lean` are chart-scale +
     `private` → must be redone past the cut locus); (b) the `√det(gₓ)`
     E-vs-`gₓ`-Haar constant reconciling `modelHaar.toSphere` (E-orthonormal
     sphere) with the `gₓ`-arclength model; (c) a **SHARP `N=1`** transverse
     bound `curveDensity(gₓ-orthonormal transverse frame) ≤ hypDensity` — the
     in-tree `intrDens_le_hyp` is NON-sharp (`N=M₀/c` from `intrPoleCap`, a
     non-orthonormal frame), so integrating it gives only `σ·N·hypRadVol`, NOT
     the exact `σ·hypRadVol` the statement requires (equality in flat ℝ²); the
     sharp constant needs `exists_intrFrame`'s parallel `gₓ`-ON frame with pole
     ratio → 1 (a NEW lemma, this session's newly-surfaced sub-frontier); (d)
     `lintegral_polar` integration to `σ·hypRadVol`.  Obstruction class =
     **missing reusable API** (from-scratch Bishop–Gromov absolute bound).  L7
     (`segBall_vol_rel`) further needs truncated polar (`τ(θ)`) +
     `lintegral_cross_le` (B4, banked) + injectivity of `expMapIntrinsic` on the
     open minimizing interior.

  3. *Also done (brick B8 punch-list item):* the `SegmentPolar.lean` header +
     both theorem docstrings were corrected — the fictional
     `expMap_contMDiffAt_of_ne_zero` citation removed, the frontier
     re-characterized around the now-existing `riemVol_exp_image_le`.
     `SegmentPolar.lean` statements/`sorry`s byte-identical; still compiles GREEN
     with exactly the two intended `sorry`s.  `SegmentPolar.md` + `SegmentArea.md`
     updated.  `SegmentCount.lean`/`VolumeOverlap.lean` untouched (still
     transitively `sorry` via the two SegmentPolar frontiers).

  4. *compact-`K` sub-lemma attempted, hit the TangentSpace-vs-E norm trap*
     (`InnerProductSpace` fibre synth vs E-norm coercivity).  Removed from
     `SegmentArea.lean` (kept clean).  Correct route for next session: under the
     `attribute [-instance] Tensor0SBundle.tangentSpace_*` header the fibre norm
     IS the g-norm (`hEnorm` ⟹ `‖v‖ = √(g.inner x v v)`), so
     `{v | √(g.inner x v v) ≤ R} = Metric.closedBall 0 R`, compact by properness
     — NOT via `gpCoerciveConst` E-norm coercivity.

- **B5c PARTIAL ACCEPTED + B5d DISPATCHED (2026-07-25/26).**  Independent
  re-verification of the partial: `SegmentArea.lean` grep-clean, targeted
  build PASSED (3818 jobs), the two SegmentPolar code `sorry`s byte-intact
  (count re-verified = 2).  The failure-first diagnosis is accepted:
  orchestrator re-checked the fixed statement on flat ℝ² AND a skewed
  constant metric (`g = diag(4,1)`: `√det g` and the ellipse shrinkage
  cancel — `V = πR² = σ·hypRadVol` again), so `segBall_vol_le` is
  anisotropy-robust as stated; the remaining difficulty is making the
  constant chain telescope, not the statement.  **B5d scope:** L6 discharge
  first — (a) global Gauss block-det split, (b) E-vs-gₓ polar
  normalization (must telescope to 1), (c) the SHARP `N=1` transverse
  bound (pole-normalized `exists_intrFrame` parallel ON frame +
  `curveRatio_anti` + pole ratio → 1), (d) polar Fubini to `σ·hypRadVol`;
  then L7 if the session has room (truncation `τ(θ)` + interior
  injectivity + B4 cross-Chebyshev), else hand L7 to B5e.  Endpoint:
  **0%** (unchanged).

- **B5d status (2026-07-26) — step (a) CORE landed sorry-free; full L6 route
  DERIVED with exact constants; both SegmentPolar `sorry`s UNTOUCHED; endpoint
  `volInput_of_bg` STILL 0%.  `volInput_of_bg` is NOT sorry-free.**

  Failure-first: L6 (`segBall_vol_le`) is confirmed a genuine multi-session
  from-scratch Bishop–Gromov absolute bound — four interlocking substantial
  sub-lemmas (a)/(b)/(c)/(d).  One session lands a fraction; L6 was NOT closed and
  L7 was not started.

  1. *Landed (reusable machinery, NOT the endpoint).*  New file
     `Comparison/Volume/SegmentGauss.lean` (+ `.md`), **sorry-free, axiom-clean**
     (focused check + targeted build `+…Volume.SegmentGauss`, 3814 jobs; `#print
     axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
     HopfRinow taint).  `velJac_gram_split` / `velJac_density_split`: the GLOBAL
     Gauss block-determinant / density factorization at the geodesic endpoint
     (step (a) core), `det[{γ̇(1)}∪{Jᵢ(1)}] = g_x(u,u)·det[transverse]`,
     `curveDensity = √(g_x(u,u))·curveDensity(transverse)`, from the PUBLIC
     `intrinsicJacobi_perp` + `intrinsicGeodesic_speedSq_eq` (no chart-scale
     `expMapC2Radius` cap; this is `RadialGram.endpoint_det_split` redone past the
     cut locus).  Instance-ordering lesson recorded (attribute `[-instance]`
     BEFORE the emetric variables, else `PseudoEMetricSpace` fails to synth and
     terms show phantom `sorry`).

  2. *DE-RISKED: the complete L6 route with EXACT constants, verified on flat ℝ²
     AND diag(4,1) (both telescope to equality).*  Recorded in full in
     `SegmentPolar.md` (2026-07-26 block).  Summary: `expJacDensity v =
     √det(g_x,x)·curveDensity(transverse gₓ-ON)(1)` [(a)] ≤
     `√det(g_x,x)·hypSn(q·|v|_{g_x},1)^{n-1}` [(c), sharp N=1: pole limit
     `√det Gram(ON) = 1`, using `hypSn(q·ℓ,t) ~ t`]; the `g_x^{1/2}` change of
     variables cancels `√det g_x` [(b)]; E-polar's `r^{n-1}·hypSn(qr,1)^{n-1} =
     hypSn(q,r)^{n-1}` reproduces `hypRadVol`, times `σ = toSphere univ` [(d)].

  3. *Remaining L6 sub-lemmas (ordered for next session).*
     (i) `radialJac_eq_vel` (radial Jacobi = velocity) — attempted this session,
     blocked ONLY on an `mfderiv (1+·) 0 1 = 1` notation fiddle
     (`mfderiv_eq_fderiv`/`HasFDerivAt.fderiv`); math routine (reparametrize by
     `intrinsicGeodesic_smul`, `mfderiv_comp_apply`).  Route in `SegmentGauss.lean`
     comment.  (ii) step (a) change-of-basis + `|det C| = √det g_x`.  (iii) step
     (c) sharp: `exists_intrRatio` taking a gₓ-ON perp frame as INPUT + the sharp
     pole-limit lemma (reuse `intrPoleCap`/`densUB_of_pole`, sharpen `N=M₀/c` to
     the exact `√det Gram(∇Jᵢ(0))`).  (iv) steps (b)+(d) measure assembly.  L7
     (`segBall_vol_rel`) not started — hand to B5e or a later B5d continuation.

  Obstruction class = **missing reusable API** (from-scratch Bishop–Gromov
  absolute bound).  Statements correct + anisotropy-robust; do NOT weaken.

- **B5d PARTIAL ACCEPTED + B5d2 DISPATCHED (2026-07-26).**  Independent
  re-verification: `SegmentGauss.lean` grep-clean, targeted build PASSED
  (3814 jobs); the two SegmentPolar code `sorry`s intact (count 2).  The
  failure-first assessment is accepted: L6 is multi-session; but the route
  is now FULLY derived with exact constants and split into four ordered
  sub-lemmas (i)–(iv), of which (i) is one atom stuck on a trivial
  `mfderiv (1+·)` computation — not a mathematical wall.  B5d2 = close L6
  by executing (i)→(iv) in order against the recorded route (SegmentPolar.md
  + §8 B5d block + SegmentGauss.lean comments), discharging
  `segBall_vol_le`; L7 only if room.  Orchestrator hint for the (i) atom:
  on ℝ with `𝓘(ℝ,ℝ)`, `mfderiv_eq_fderiv` + `((hasFDerivAt_id _).const_add 1).fderiv`
  (the fderiv of `fun r => c + r` is `id`), then `ContinuousLinearMap.id_apply`
  — or bypass `mfderiv` entirely by stating the reparametrization with
  `HasMFDerivAt` and composing `HasMFDerivAt.comp` witnesses.  Endpoint:
  **0%** (unchanged).

- **B5d2 status (2026-07-26) — step (i) + step (a) GLUE landed sorry-free;
  `segBall_vol_le` NOT discharged; both SegmentPolar `sorry`s UNTOUCHED; endpoint
  `volInput_of_bg` STILL 0% (NOT sorry-free).**

  Failure-first: `segBall_vol_le` is NOT closed.  The dispatch premise that (i)→(iv)
  is executable to closure this session is WRONG at step (c): the **sharp `N=1`
  transverse bound is a genuine MISSING-API frontier**, not assembly.

  1. *Landed (SegmentGauss.lean, all sorry-free; focused check + targeted build
     `+…Volume.SegmentGauss` 3814 jobs, warning-clean).*
     - `radialJac_eq_vel` (step (i)): `intrinsicJacobi x u u 1 = curveVelocity
       (intrinsicGeodesic x u) 1`.  Executed as planned — reparametrize `u+r•u =
       (1+r)•u`, spray homogeneity `intrinsicGeodesic_smul` to `φ∘(1+·)`, then
       `HasMFDerivAt.comp 0 hshift` with `hshift : HasMFDerivAt (1+·) 0 id` (from
       `hasMFDerivAt_iff_hasFDerivAt` + `(hasFDerivAt_id 0).const_add 1`).  The
       `mfderiv (1+·) 0 1 = 1` fiddle DISSOLVED (the `.comp` carries the `id`
       differential; the final `((mfderiv φ 1).comp id) 1 = mfderiv φ 1 1` closes
       by `rfl` — `simp` reports "no progress" on the CLM-coe form).
     - `curveGram_recomb` / `curveDensity_recomb` (step (a) glue): change-of-basis
       congruence `curveGram V' t = Cᵀ·curveGram V t·C`, `curveDensity V' t =
       |det C|·curveDensity V t` for `V' i t = ∑ k C k i • V k t`.  Pure `g.inner`
       bilinearity + `det(Cᵀ G C) = (det C)² det G`.  Reusable.
     - `curveDensity_reindex`: `curveDensity (V∘e) t = curveDensity V t`, `e:ι≃κ`.

  2. *THE BLOCKER — step (c) sharp `N=1` (missing API, gauge-confirmed).*  The
     transverse bound `curveDensity(gₓ-ON transverse)(1) ≤ hypSn(qℓ,1)^{n-1}`
     requires the pole ratio `curveDensity(transverse)(t)/hypDensity(qℓ,n-1)(t) →
     1`.  The only in-tree pole cap, `intrPoleCap` (IntrinsicRatio.lean:205,
     private), is **NON-sharp**: it yields `N = (normalChartDensity(0)+1)/c`,
     `c = ℓ/|det(B→model)|`, and its OWN docstring flags sharp `N=1` as "not yet
     available".  `segBall_vol_le` is an EQUALITY on flat ℝ² (σ exact), so a lossy
     `N>1` CANNOT discharge it.  The sharp pole normalization
     (`normalChartDensity(0)·|det(B→model)|/ℓ = 1`, i.e. `mfderiv exp_x at 0 = id`
     pushed through the density defs) is a genuine ~200-line sub-project absent
     from the tree.  Also: `exists_intrFrame` (IntrRadialFrame.lean:57) is a FULL
     `n`-frame (parallel, g-ON at all points), NOT the transverse `(n-1)` frame;
     the transverse perp frame is `exists_perp_pos`.

  3. *Also missing (assembly, tractable, blocked behind (c)).*  Step (a) full
     assembly (launch-basis `|det C_b|=ℓ/√det gₓ` from its gₓ-Gram block
     `[[ℓ²,0],[0,I]]` + `Fin n ≃ Option (Fin (n-1))` reindex to `velJacFrame` via
     `curveDensity_reindex`); step (b)+(d) measure (`gₓ^{1/2}` CoV via Mathlib
     `addHaar_image_linearMap`; truncated E-polar from in-tree `lintegral_polar`
     `PolarEvaluation.lean:50` + `toSphere_apply_univ` + `volumeIoiPow`).  L7
     (`segBall_vol_rel`) NOT started — sorry UNTOUCHED per dispatch.

  4. *Sorry-status (verbatim).*  `SegmentPolar.lean`: `segBall_vol_le` `sorry`
     (:120), `segBall_vol_rel` `sorry` (:174) — both UNCHANGED, statements
     byte-identical.  `segBall_vol_fin` still PROVED (transitively sorry-dep on
     `segBall_vol_le`).  `VolumeOverlap.lean` `volInput_of_bg`: own content
     sorry-free, transitively `sorry` via the two SegmentPolar frontiers —
     UNCHANGED (not rebuilt; no edit).  SegmentCount/VolumeOverlap untouched.

  Obstruction class = **missing reusable API** (sharp Bishop pole normalization).
  Smallest unblocking lemma = the sharp pole cap: for a gₓ-ON transverse frame,
  `Tendsto (fun t => curveDensity(intrinsicGeodesic x v)({J(êᵢ)})(t) /
  hypDensity(qℓ,n-1)(t)) (𝓝[>]0) (𝓝 1)` (or `∀ᶠ ≤ 1`), sharpening `intrPoleCap`
  from `M₀/c` to the exact `√det Gram(∇Jᵢ(0)) = 1`.  Endpoint stays **0%** until
  BOTH SegmentPolar sorrys close.

- **B5d2 PARTIAL ACCEPTED + B5d3 DISPATCHED (2026-07-26).**  Independent
  re-verification: `SegmentGauss.lean` (with `radialJac_eq_vel`,
  `curveGram_recomb`/`curveDensity_recomb`, `curveDensity_reindex`)
  grep-clean; independent targeted rebuild PASSED (3814 jobs); both
  SegmentPolar `sorry`s intact.  The (i)-atom stall dissolved via the
  `HasMFDerivAt.comp` hint route.  The three-route collapse onto ONE
  lemma is ACCEPTED as the lane's true remaining frontier: the sharp
  `N=1` transverse pole limit.  **B5d3 = exactly that lemma + the
  step-(c) corollary**, dispatched with the orchestrator's CONTINUITY
  route (J(t)/t → D(exp)₀ = id via `mfderiv_expMapIntrinsic_at_zero` +
  `intrinsicFiber_smooth` derivative-continuity; Gram/det continuity;
  `hypSn(q·ℓ,t)/t → 1`) — not Taylor expansion.  If B5d3's three-route
  fallback fires, the lane is genuinely blocked pending the
  (browser-blocked) Pro consult and dispatching STOPS.  Housekeeping:
  B5d2's two orphaned claims force-released (pids dead; script hiccup);
  the registry's many OTHER stale claims (dead Codex-lane pids,
  2026-07-15..18) left untouched — not this lane's to clean.  Endpoint:
  **0%**.
