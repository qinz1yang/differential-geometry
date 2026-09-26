# Design: B13, fine cut necks on every final slab (the S leaf's last input), 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ 9126abc30 plus uncommitted lanes. Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`. The B13 here is the S brick. It is not the B13 of
`DESIGN_B6D_GLUE.md`, which is the composed ancient-limit headline.

Every statement in §2 was elaborated with `sorry` bodies in one probe outside the repo. The probe
imported only committed modules with shared oleans: `Contract/UniformDebitSurgeryStepOfFactory`,
`Topology/CanonicalNeighborhoodContinuationLeaves`, `Topology/TerminalSpatialCanonicalAlternatives` and
`Topology/HornSeparationFrontierScalar`. It ran with `LEAN_NUM_THREADS=2` and produced only
`declaration uses sorry`. The probe has been deleted.

## 0. Failures first

**F1. `hlong` is the wrong reduction: it is not implied by the Crossing core, and it is probably false.**

What `hlong` says (`Contract/UniformDebitSurgeryStepOfFactory.lean:307`):
- The clause `∀ Qc ≥ Qθ, 2θ ≤ Qc·(s − a)` collapses to `Qc = Qθ`, because `s − a > 0`.
- So `hlong` is exactly `∀ B θ, ∃ τ(B, θ) > 0`: for every history with `InitialIdentification`, horizon
  `< B`, and every singular final slab, `s − a ≥ τ`.
- That is a uniform time gap between consecutive singular times. It would also bound the number of
  events by `B/τ`.

Why the Crossing core cannot supply it:
- It quantifies over ALL such histories. It has no class, no records, no CN, no κ, no pinching and no
  derivative clause.
- The only producers of the missing information (B3e, B5, the X-core, T1/T2 below) consume exactly
  those clauses.
- Their output is necks, not slab length. Nothing in the tree, and nothing in Perelman, gives a time
  gap. Finiteness of surgeries is by volume.

Why it is probably false (no explicit history is written down):
- A cut at a fine scale `h` leaves a standard cap attached to half a `δ`-neck of scale `h`.
- Its standard-solution model dies at normalized time 1, so a pinch within real time `≈ c·h²` is not
  excluded.
- In the class, cut scales are only bounded above: `hasCanonicalCutoffRecords` bounds `δ` and
  `neckRadius` from above.
- S's own events cut at the uniform scale `Q`. With `θ = 2(Λb + θB) ≥ 2`, a remnant-neck pinch at
  normalized age `< 1` already violates `2θ ≤ Q(s − a)`.

Verdict:
- Retire `uniformDebitSurgeryStepStrong_of_long_slabs` as the S route.
- S consumes fine cut necks directly: T5 consumes the supply statement T4 (`FineCutNeckSupply`).
- B12 (`Contract/HornFineCutNecksLongSlab.lean:291`) stays a true special case but is no longer needed.

**F2. The strong-neck route is dead on short slabs; spatial necks at `τ → s` are exactly what F\* consumes.**
- `StrongNeck` needs `[τ − 1/R, τ] ⊆ [a, s)` (SB13 item 5). So no strong-neck form exists when `R(s − a) < 1`.
- F\*'s premise `FineCutNecks εc Q` (`Contract/HornFineCutNecks.lean:30`) asks for `NormalizedNeck`s of
  the terminal metric `L`.
- `TerminalLimitMetric.eventually_normalizedNeck_of_spatialNecks`
  (`Topology/TerminalSpatialCanonicalAlternatives.lean:473`) turns `SpatialNeck (G.metric τₙ) eps x`
  with `τₙ → s⁻` into `NormalizedNeck L δ k`. Its inputs are `eps < δ`, `δ⁻¹ + 1 ≤ eps⁻¹` and
  `k ≤ ⌈eps⁻¹⌉`. Take `δ := εc`, `k := ⌊εc⁻¹⌋ + 1`, and `eps` small.
- So "fine SPATIAL necks at `τ → s`" (review G item 4) is the right output shape. T3 is stated so.

**F3. T1 is almost free, and "`U < ∞`" is redundant.**

The obstruction reduces to topology already in the tree:
- `exists_neck_coordinates_in_horn_of_frontier_scalar_lt` (`Topology/HornSeparationFrontierScalar.lean:116`,
  uniform, frontier `< (1 − 4323δ)·scale`) puts any fine neck centred in horn `e` into horn coordinates.
- `exists_horn_neck_end_separation_tolerance` (`Contract/HornNeckEssentiality.lean`) then gives a
  `ComplementPair` of that central sphere in `positiveHornDomain`, with connected sides. The left side
  contains `u → 0` and the right side contains `u → ∞`.

The argument:
- If `W` is open and connected with `frontier W = Σ`, then `W` is clopen in `Σᶜ`, hence equals one side.
- The left side's closure reaches the base sphere, where `R ≤ Λ/r² = ℓ < cQ`.
- The right side has `R → ∞` (`horn_scalar_diverges`), which is excluded by `R ≤ U`, or by
  compactness of `closure W`.

Consequences:
- "Same tip side" and "`x ∈ K`" are not needed.
- The only real input is that the centre of `N` lies in horn `e`. It follows from connectedness of
  `closure W` plus `R > ℓ` on it (brick T1b).

**F4. The lower bound of K comes from `x`'s own curvature, not from the birth scale or the class.**
- Take `x` as a cap-window point. The comparison `exists_standard_comparison_of_cap_window_trace`
  (`Topology/CapWindowStandardComparison.lean:20`) and `exists_scalar_lower_bound_of_cap_window_trace`
  (`Topology/TracedRegionOrCapWindow.lean:31`) give `c·scale ≤ R ≤ Creset·scale` on the whole window.
  The window contains `x`.
- Hence `scale ≥ R_L(x)/Cup ≥ Kfine·ℓ/Cup`, and `c·scale > 2ℓ` once `Kfine > 2·Cup/c`.
- The class and birth-scale facts are only HYPOTHESES of the comparison: `qcan ≤ Cbirth·scale` and
  `1 ≤ a₀·scale`. S supplies them by choosing `ρbound ≤ ρ₀(qcan, a₀)` through
  `IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale`
  (`Topology/CanonicalNeighborhoodContinuationLeaves.lean:88`). This is S's choice, after `qcan` and `a₀`.

**F5. K is producible on the terminal metric, but through four genuinely new steps (T2a–T2d):**
- **T2a.** "CW frequently as `τ → s`" gives fixed `(j, b, window point, trace)` with
  `s − t_j ≤ θcap/scale`, by pigeonhole over `Fin eventCount × RetainedBoundaryIndex`. Finiteness of
  `tubes.Boundary` still has to be checked.
- **T2b.** The comparison applies at every `t < s`, and `normSq0S ≤ P²` after rescaling. This puts
  `Ξ(closed ball)` inside `terminalRegularRegion`: the `riemannNorm` bound is exactly that definition,
  `EventData.lean:214`. `R_L` inherits `[c·scale, Creset·scale]` in the limit. `Ξ` is `t`-independent,
  by injectivity of the survivor map.
- **T2c.** Standard far radial necks at radius `D₁`, `t ∈ [0, Θ]`
  (`Perelman/StandardSolution/StandardFarRegion.lean:400`; the map is radial, so the central sphere is
  `{‖v‖ = D₁}`), transported through the window comparison to `L`.
- **T2d.** `W := Ξ(open ball D₁)`. No Jordan–Brouwer is needed.

**F6 (blocker, binder order). The X-core as designed cannot be consumed by S.**

What the X-core needs:
- B3e needs `Rrad(A) ≤ p₀.modelRadius` and `p₀.modelAccuracy ≤ ζ₀(A)`
  (`Topology/BoundedCurvatureAtDistanceSliceTerminal.lean:249`; its proof instantiates
  `Dcap = Rrad = transitionEnd + 1 + n`).
- The maximal-window steps need `CW(D(A, T, Q), θcap(T, Q))` with `θcap ↑ 1` (DESIGN_MAXWINDOW §1, §3.3, §4.3).
- The ancient limit needs every `A`.

Why S cannot provide it:
- The Crossing leaf gets all of this by negating its own `∃ Dcap εcap δmax`.
- In S, `p₀` is S's single `∃`, chosen before `H`.
- F\* forces `Dbig` before `εcut`: `∀ Dtrace Dbig …, ∃ εold δold, ∀ m accuracy ηrecord, ∃ δ εcut`,
  `Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:556`.
- So a contradiction sequence for a fixed `εcut` has fixed cap parameters.

What S can consume, and the gap:
- S can consume only T4 with `(Rrad ζ₀ δ₀ ρ₀ m₀)` chosen BEFORE `εc`, as stated below. T5 then
  elaborates with `Dbig := max (max Dcap (Dtrace+1)) Rrad`.
- The current X-core design proves only the εc-first variant `∀ εc, ∃ Rrad(εc) …`. That variant is
  circular with F\*.
- The resolution must be one of:
  - (i) a fixed-parameter X-core: CW exclusion at the full window radius, and `Θ` fixed by
    `(ε, κ, C1s, C2s, Ctime, Cgrad, a₀)`;
  - (ii) a reordered F\* in which `εcut` no longer depends on `Dbig`. This fights the gluing
    requirement `εcut ≲ 1/Dbig`.
- Decide this before any T3 work.

**F7 (tied to F6). Cap-age band `(Θ(p₀), 1]`.**
- With fixed `p₀`, T2 excludes young caps only up to the `Θ` whose `ζ₀(Θ, D)` is at least
  `p₀.modelAccuracy`.
- Caps whose normalized age at `s` lies in `(Θ, 1]` near a deep horn point are covered neither by T2
  nor by the traced alternative, which crosses the event inside that cap.
- Perelman handles them with `θ(ε)` and canonical-ness of the standard solution at late times. That
  argument is absent here.
- This is the concrete counterexample shape to send to review: a horn at `s` grown from the remnant
  neck of a cap of age `≈ 1`.

**F8 (small).**
- The comparison needs `∀ x, -3/a₀ ≤ R(H.initialMetric 0) x`, but S provides only
  `InFixedHamiltonIveyRegion … a₀`. No supplier exists. `HI(a₀)` gives `R ≥ −e²/a₀`, not `−3/a₀`.
- Fix by an `a₀`-adjusted lemma, or by adding the scalar lower bound to S/C's clause (C knows `g₀`).
- B3e also needs `Λ ≤ R·t` with absolute `t`. This needs `t ≥ c/max|Rm(g₀)|` from
  `InitialIdentification` (M7c): a first-singular-time lower bound. Is it in the tree? Check.

**Simplification.** Unlike the Crossing leaf, S has `SpatiallyCanonicalBefore … s`, the derivative and
gradient bounds on `(a, s)`, and `TerminalNoncollapsedBefore … t₀` for all `t₀ ∈ (a, s)`. So B3e
applies directly at every slice `τ < s`. The BS1–BS7 sliver machinery is not needed for S.

## 1. Route

1. At a deep horn point `x` of `L`, use `R_L(x) ≥ Kfine·max(Λ/r², qcan, 1)` and split on the slices
   `τ → s⁻`.
2. **Frequently cap-window:** T2 builds `W`, then T1 gives `False`.
3. **Eventually not cap-window:** T3 gives eventually `eps`-spatial necks at `(x, τ)`. It works through
   B3e, the X-core, the terminal arms (`exists_minimizingArms_of_horn_point`,
   `Topology/HornCentralSphereSeparation.lean:488`) transferred to the slices, then a line in the
   ancient κ-limit, then the round cylinder.
4. Then `eventually_normalizedNeck_of_spatialNecks` gives `FineCutNecks εc Qc` (T4).
5. T5 feeds F\*.

## 2. Exact statements (all elaborated; namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`)

Opens as in `UniformDebitSurgeryStepOfFactory.lean`, plus
`Perelman.CanonicalNeighborhood.FiniteHorn` and `Filter`. It also uses the file's private
`SigmaCompactSpace G.terminalRegularOpen` instance.

**T1, the terminal cap-side obstruction (frozen form of review G item 4):**
```lean
theorem TerminalCorePresentation.false_of_terminal_capSide :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
    ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
      δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ P.hornHalfRange c e →
    ∀ (W : Set D.slab.terminalRegularOpen) {cQ U : ℝ}, IsOpen W → IsConnected W →
      frontier W = N.chart '' {z | z.val.2 = 0} →
      2 * (Λ * (P.coreRadius ^ 2)⁻¹) < cQ →
      (∀ z ∈ closure W, cQ ≤ metricScalarAt D.terminal.metric z ∧
        metricScalarAt D.terminal.metric z ≤ U) →
      False
```
- `ℓ = Λ/r²` is the core-frontier bound (`frontier_scalar_le`, `Contract/Terminal.lean:173`).
- The factor 2 feeds the `(1 − 4323δ)` margin, since the centre of `N` lies in `closure W`.
- `ε` is the presentation's accuracy. T4 applies T1 to `P.withEps eta` (brick T1a), so the neck's
  accuracy is independent of `εP`.

**T2, producing `K = closure W` on the terminal metric with both bounds:**
```lean
theorem RetainedCoreHistory.exists_terminal_capSide_of_frequently_capWindowPoint
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) (Ctime : ℝ≥0) (Dcap : ℝ) (hDcap : 0 < Dcap)
    {eps : ℝ} (heps : 0 < eps) (heps11 : eps < 1 / 11) :
    ∃ (c Cup Cbirth Rrad ζ₀ δ₀ : ℝ) (m₀ : ℕ), 0 < c ∧ c ≤ Cup ∧ 0 < Cbirth ∧
      Dcap + 1 < Rrad ∧ 0 < ζ₀ ∧ 0 < δ₀ ∧
    ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → Rrad ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j b, qcan ≤ Cbirth * ((records j).static b).neck.scale) →
      (∀ j b, 1 ≤ a₀ * ((records j).static b).neck.scale) →
    ∀ {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount) →
      H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime qcan s →
    ∀ x : G.terminalRegularOpen,
      (∃ᶠ τ in 𝓝[<] s, H.CapWindowPoint records (Fin.last H.eventCount) x.1 τ Dcap θcap) →
    ∃ (W : Set G.terminalRegularOpen) (Qs : ℝ), 0 < Qs ∧ x ∈ W ∧ IsOpen W ∧ IsConnected W ∧
      IsCompact (closure W) ∧
      (∀ z ∈ closure W, c * Qs ≤ metricScalarAt L.metric z ∧
        metricScalarAt L.metric z ≤ Cup * Qs) ∧
      ∃ (w : G.terminalRegularOpen) (nk : SpatialNeck L.metric eps w),
        frontier W = range (fun y : Sphere 2 => nk.map (y, 0))
```
- `Qs` is the record scale.
- `SpatialNeck.exists_normalizedNeck_of_two_mul_le` (`Geometry/Neck/SpatialNormalization.lean:146`)
  keeps `chart = nk.map`. So the frontier is `N.chart '' {z.2 = 0}`, as T1 needs.

**T3, the Crossing core at deep horn points (fine SPATIAL necks at `τ → s`):**
```lean
theorem TerminalCorePresentation.eventually_spatialNeck_of_not_capWindowPoint
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
    ∀ (κ C1s C2s qcan a₀ : ℝ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ} (ε : ℝ),
      0 < κ → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < a₀ →
      Perelman.AdmissiblePinchingFunction phi → 0 < ε → ε ≤ εcone →
    ∃ (Dcap θcap Rrad ζ₀ δ₀ ρ₀ : ℝ) (m₀ : ℕ), 0 < Dcap ∧ 0 < θcap ∧ θcap < 1 ∧
      Dcap + 1 < Rrad ∧ 0 < ζ₀ ∧ 0 < δ₀ ∧ 0 < ρ₀ ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
    ∃ Kfine : ℝ, 1 ≤ Kfine ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (H : RetainedCoreHistory P₀) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      InitialIdentification P₀ g₀ H.toHistory →
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      δbound ≤ δ₀ → ρbound ≤ ρ₀ →
    ∀ hend : H.time (Fin.last H.eventCount) = H.horizon,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) →
      H.EventSlabsPinched phi →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
    ∀ {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
      G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
      (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
        H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
    ∀ {εP Λ : ℝ} (P : TerminalCorePresentation
        { stage := H.stage (Fin.last H.eventCount)
          startTime := H.time (Fin.last H.eventCount)
          endTime := s
          startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
          startTime_lt_endTime := G.lt
          slab := G
          terminal := L
          singular := hsing
          parameters := parameters } εP Λ), εP ≤ eta →
    ∀ (c : ConnectedComponents G.terminalRegularOpen) (e : P.hornIndex c)
      (x : G.terminalRegularOpen),
      x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) →
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ metricScalarAt L.metric x →
      ∀ᶠ τ in 𝓝[<] s,
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) x.1 τ Dcap θcap →
          Nonempty (SpatialNeck (G.flow.base.metric τ) eps x.1)
```
- F6 applies to exactly this statement: the tuple `(Dcap θcap Rrad ζ₀ δ₀ ρ₀ m₀)` is placed before
  `eps`.
- The variant with the tuple after `eps` is what the current X-core design can prove.

**T4, the supply S consumes (replaces `hlong`); `phi` is internal, from
`exists_admissiblePinchingFunction_for_identified_incomingSlabs`, `Topology/HamiltonIveyPinching.lean:689`:**
```lean
def FineCutNeckSupply (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
  ∀ (κ C1s C2s qcan a₀ : ℝ) (Ctime Cgrad : ℝ≥0) (ε : ℝ),
    0 < κ → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < a₀ → 0 < ε → ε ≤ εcone →
  ∃ (Rrad ζ₀ δ₀ ρ₀ : ℝ) (m₀ : ℕ), 0 < ζ₀ ∧ 0 < δ₀ ∧ 0 < ρ₀ ∧
  ∀ εc : ℝ, 0 < εc → εc < 1 / 2 →
  ∃ Kfine : ℝ, 1 ≤ Kfine ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
    Rrad ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    δbound ≤ δ₀ → ρbound ≤ ρ₀ →
  ∀ H : RetainedCoreHistory P₀, InitialIdentification P₀ g₀ H.toHistory →
  ∀ hend : H.time (Fin.last H.eventCount) = H.horizon,
    H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan (H.time j.succ)) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
  ∀ {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)),
    G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
    G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
    (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
      H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
  ∀ {εP Λ : ℝ} (P : TerminalCorePresentation
      { stage := H.stage (Fin.last H.eventCount)
        startTime := H.time (Fin.last H.eventCount)
        endTime := s
        startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
        startTime_lt_endTime := G.lt
        slab := G
        terminal := L
        singular := hsing
        parameters := parameters } εP Λ), εP ≤ eta →
  ∀ Qc : ℝ, Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Qc →
    P.FineCutNecks εc Qc

theorem fineCutNeckSupply (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupply P₀ g₀
```
Proof bookkeeping:
- `eta := min eta_T1 eta_T3`.
- T2 runs at `Θ := (θcap + 1)/2` and `Dcap` from T3, with `eps_T2 := eta_T1/2`.
- `Rrad := max Rrad_T2 Rrad_T3`; likewise `ζ₀, δ₀, m₀` by min/max.
- `ρ₀ := min ρ₀_T3 (min √(Cbirth/(4·qcan)) √(a₀/2))`.
- `Kfine := max Kfine_T3(eps) (2·Cup/c + 1)`, with `eps` from `εc` as in F2.

**T5, the S assembly (edit of `Contract/UniformDebitSurgeryStepOfFactory.lean`; B12 dropped):**
```lean
theorem uniformDebitSurgeryStepStrong_of_fineCutNeckSupply
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hfine : FineCutNeckSupply P₀ g₀) :
    UniformDebitSurgeryStepStrong P₀ g₀

theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_fineCutNeckSupply P₀ g₀ (fineCutNeckSupply P₀ g₀)
```
Instantiation changes relative to the current proof:
- `ε := min εbar (min εF εcone_T4)`, and F\*'s input `η := eta_T4`.
- `Dbig := max (max Dcap (Dtrace + 1)) Rrad`.
- `m := max (max mcap (⌈tol⁻¹⌉₊ + 2)) m₀`.
- `accuracy := min (min εold εcap) ζ₀`.
- `ηrecord = δbound := min (min δold δmax) δ₀`.
- `ρbound := min (min ρmax 1) ρ₀`.
- `Kfine` from T4 at `εc := min εcut (1/4)`, then `fineCutNecks_of_le`.

All of T4's inputs are S clauses. T5 is sound and does not depend on F6: it can land now.

## 3. Suppliers and bricks

Suppliers:
- F\*: `Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:556`.
- F\* with input `η`: `UniformDebitSurgeryStepOfFactory.lean:39`.
- `nonempty_terminalLimitMetric`: `Topology/TerminalMetricExistence.lean:84`.
- Horn coordinates and separation: `HornSeparationFrontierScalar.lean:116`,
  `Contract/HornNeckEssentiality.lean` (`exists_horn_neck_end_separation_tolerance`),
  `Topology/SphereSeparation/ComplementPair.lean:9`, `Contract/HornComponents.lean:17`,
  `Contract/HornNeckCoordinates.lean:125`.
- Cap windows: `CapWindowStandardComparison.lean:20`, `TracedRegionOrCapWindow.lean:31`, `:665`;
  `CapWindowPoint` at `CanonicalNeighborhoodContinuationLeaves.lean:136`.
- Standard necks: `StandardFarRegion.lean:400`.
- Neck normalization: `SpatialNormalization.lean:71`, `:146`.
- Terminal transfer: `TerminalSpatialCanonicalAlternatives.lean:473`;
  `HornSeparationSliceTransfer.lean:36`, `:62`.
- Arms and the cylinder limit: `HornCentralSphereSeparation.lean:488`;
  `Perelman/CanonicalNeighborhood/WindowedArmCylinderLimit.lean:27`.
- B3e: `BoundedCurvatureAtDistanceSliceTerminal.lean:249`, `:336` (uncommitted).
- X-core: DESIGN_MAXWINDOW §2–§5 and DESIGN_B6D_GLUE.

| Brick | Content | Lines |
|---|---|---|
| T1a | `TerminalCorePresentation.withEps` (monotone in `ε`) | 30–60 |
| T1b | `closure W` connected, `R > ℓ`, meets horn `e` ⇒ ⊆ positive horn `e` (centre in `hornHalfRange`) | 80–150 |
| T1c | clopen-in-`Σᶜ` + `ComplementPair` ⇒ `W` is a side; the left side reaches the base, the right side has `R → ∞` | 150–300 |
| T1 | assembly | 60–120 |
| T2a | pigeonhole to fixed `(j, b, trace)`, `s − t_j ≤ θcap/scale`; `Finite RetainedBoundaryIndex` | 60–120 |
| T2b | window in `terminalRegularRegion`, `R_L ∈ [c, Creset]·scale`, `Ξ` independent of `t` | 190–380 |
| T2c | far radial neck of the standard solution transported to `L` (limit of the window comparison at `τ = scale(s − t_j) ≤ Θ`) | 250–450 |
| T2d | `W := Ξ(open ball D₁)`; open, connected, compact closure, frontier = neck sphere | 80–150 |
| F8 | `-3/a₀` scalar floor from HI (or an S/C clause), and first-singular-time lower bound | 40–150 |
| T3 | τ-selection; ball bound on `L` from B3e plus the limit; arms to slices; line ⇒ cylinder in the ancient limit; neck back to approximants | 0.9–1.8k, plus the X-core (7–13k, Crossing lane) |
| T4 | dichotomy assembly + `eventually_normalizedNeck_of_spatialNecks` + constants | 200–400 |
| T5 | S reduction edit + leaf | 150–270 |

Order:
1. T5 now, as a conditional on `FineCutNeckSupply`. It retires `hlong`.
2. T1 (T1a–c) and T2 (T2a–d) in parallel; F8.
3. F6 decision (lead + review) BEFORE T3.
4. T3 after the X-core, in the fixed-parameter form if (i) is chosen.
5. T4.

## 4. Single-statement review prompt (T4, `FineCutNeckSupply`)

> 请审查下列单一命题（Lean 全文见 `Surgery/Skeleton/DESIGN_B13.md` §2 T4）。背景：S 叶子经工厂 F* 只剩一个输入——在终端度量上"深喇叭点处有细割颈"（`FineCutNecks εc Qc`）。原假设 `hlong`（奇异终片长度一致下界）等价于相邻奇异时刻的一致时间间隔，且对所有历史量化而不含类条件，我们判其不可由现有核心导出、且很可能为假，故以 T4 取代。
> T4 断言：固定 (P₀, g₀)。∃ eta εcone；∀ κ C1s C2s qcan a₀ Ctime Cgrad ε≤εcone；∃ Rrad ζ₀ δ₀ ρ₀ m₀（帽参数要求，**选在 εc 之前**）；∀ εc∈(0,1/2)；∃ Kfine；∀ p₀（modelRadius≥Rrad，accuracy≤ζ₀，order≥m₀）、δbound≤δ₀、ρbound≤ρ₀，∀ 满足类条件与 S 全部条款（导数、梯度、空间典范见证、历史/终端非塌缩、Hamilton–Ivey）的历史 H 与奇异终片 G、终端度量 L、以及任意 εP≤eta 的终端核心呈现 P：凡 R_L(x) ≥ Kfine·max(Λ/r², qcan, 1) 的喇叭内点 x 皆为 εc-细法化颈中心。
> 证明路线：沿 τ→s 分两支。若 x 频繁为帽窗点，则由帽窗记录与标准解比较构造终端紧帽侧 W（两侧界 c·Qs ≤ R ≤ Cup·Qs，边界为喇叭中的颈中心球），拓扑上 W 必为该球的核心侧（含 R≤ℓ 的边界）或尖端侧（R→∞），矛盾。否则由 B3e、X-core 得古代 κ 极限，喇叭双臂给出直线，从而为圆柱，得空间细颈，再传到 L。
> 请回答：(1) 真值：帽参数在 εc 之前、p₀ 在 H 之前固定时，T4 是否成立？特别是归一化帽龄处于 (Θ(p₀),1] 的旧帽（其颈残部在 s 形成喇叭）是否构成反例？(2) 常数簿记：F* 要求 Dbig 先于 εcut（εcut 依赖 Dbig）；若 T4 只能证成"∀εc ∃Rrad(εc)"，是否存在不循环的选法？(3) 可供给性：B3e 需 Rrad(A)≤modelRadius（A→∞），固定 p₀ 下 X-core 能否运行？是否有 Perelman II 4.3 式的固定 δ 论证可替代？(4) 如判假，请给出具体历史反例或最小修正（改 F* 次序，或加强类条件）。
