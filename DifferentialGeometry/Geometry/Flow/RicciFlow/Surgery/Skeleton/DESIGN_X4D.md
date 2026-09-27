# Design X4d: the Σ-sequence anchored bound, its persistence engine, and the X4/X4a/W1 deltas (2026-09-26)

Read-only design on `codex/pc-target-c-psf` @ 88a4eec5a, per review H14
(`Surgery/consult/H14-crossing-x4d-review-digest.md`, binding). It replaces §2.7 X4d, the X4 step 6/8 text and the W1
κ remark of `Surgery/Skeleton/DESIGN_CROSSING_ASSEMBLY.md` (cited as `DCA:line`). Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`, except those beginning `Geometry/`, which are relative to `DifferentialGeometry/`. No proofs.

## 0. Failures and gaps in the current X4d text

**G1. Six persistence inputs are missing (H14 (a) FIX).** X4d (`DCA:486–514`) asks only
`Rrad ≤ modelRadius`, `2 ≤ modelOrder`, `modelAccuracy ≤ ζ₀` (`DCA:499`). The lemma the route cites,
`exists_standard_comparison_of_cap_window_trace` (`Surgery/Topology/CapWindowStandardComparison.lean:20`),
has these binders, all of which must be supplied:

| Binder | Line | Status in old X4d |
|---|---|---|
| `(Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1)` | :21 | `Θ` implicit ("1/2"); `C` never tied to `Ctime` |
| `∃ R, D + 1 < R`, `∃ m₀, 4 ≤ m₀`, `∃ ζ₀ δ₀` | :24–25 | only `2 ≤ modelOrder`; no `m₀`, no `δ₀` |
| `δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀` | :30 | `δbound ≤ δ₀` and `m₀ ≤ modelOrder` absent |
| `(qcan a₀ θcap) (0 < qcan) (θcap ≤ Θ)` | :31 | `qcan` conflated with the witness threshold `q` |
| `∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x` | :32 | absent |
| `∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x` | :33 | absent |
| `Gk.flow.base.metric (H.time k) = H.initialMetric k` | :35 | present (`hG`) |
| `H.EventSlabsDerivative C qcan k`, `Gk.DerivativeBoundBefore C qcan t` | :36–37 | present at threshold `q`, not `qcan` |
| trace anchor `A.point j.succ … = ((records j).static b).window x` | :41 | absent (the CWP branch never names it) |
| age `t - H.time j.succ ≤ θcap * scale⁻¹`, `‖x.val‖ < D + 1` | :42–43 | from CWP, but with `D := D₁`, not the enlarged radius |
| `qcan ≤ Cbirth * scale`, `1 ≤ a₀ * scale` | :44–45 | absent |

A supply gap, not a counterexample: every binder is discharged eventually along `Σ` (§1, P1s).

**G2. "Anchor trace ⇒ nearby ball survives" was assumed.** `DCA:525` ("use the standard-cap window bound
`R ≤ C(D₁)·λ` on `B(w, D₂/√λ)`") and `DCA:80, 527` ("the window exit is handled by an enlarged window, as in H9")
assume that the current metric ball about the rebase point lies in a surviving window. One `BackwardPointTrace`
of `w` gives nothing about its neighbours. Correction: the whole-window survival IS delivered — :20 concludes
an embedding `Ξ : standardCapWindow D → backwardSurvivorIncomingDomain` (:62–70) for ANY `D` below the model
radius, from the single anchor trace, because `WindowPersistence.lean:1029` does the KL §74 dichotomy internally
(`records.delta ≤ δ₀`, :1060). What is missing is (i) calling it at the ENLARGED radius `D₂` and (ii) the
capture of the metric ball by `Ξ(window D₂)` (P2). Neither was stated.

**G3. `λ ≤ 2R_t(w)` cited the birth slice.** `DCA:525–526` ("`λ ≤ 2R(w)` by `hscale` (the cap scalar lower
bound)") and `DCA:79` (`StandardTerminalBlowup.lean:61`). The cap lower bound used in the tree,
`scale/2 ≤ R(witness.cap w)` (`BoundedCurvatureAtDistanceSliceTerminal.lean:291, 312`), is for
`witness.metric` at the BIRTH time `H.time j.succ`. At the slice `v > H.time j.succ` it must come through the
evolved comparison (P3: :20's 2-jet closeness to `Q(τ)` plus `StandardActionComparison.lean:40`).
`hscale` (`DCA:275`) is `λ ≥ (n+1)·qcan`, a lower bound on `λ`; it cannot give an upper bound on `λ`.

**G4. H9's ¬CWP centre was silently generalized.** `DCA:527` invokes "H9's first-touch argument" for a centre
that IS a CWP. In H9 (`BoundedCurvatureAtDistanceAfterEvent.lean:45`) the centre's `hnot` is consumed twice:
`hyU` (:136–139, the centre is in the survivor domain) and the first-touch contradiction (:224–226,
`exact hnot (H.capWindowPoint_at_event_of_edist_le …)`). For a CWP centre both steps fail; the first-touch
argument has no contradiction to reach. P2 replaces it by an open-embedding capture that uses no ¬CWP.

**G5. "No Harnack" is inaccurate.** `DCA:481` ("It does not use Harnack"). X4a's distance step,
`ricciFlow_additive_distance_bound_of_terminal_scalar` (`Estimates/Distance/TerminalScalar.lean:173`), imports
`HamiltonHarnack/TerminalScalar.lean` (:1) and applies `hamilton_scalar_le_terminal_bound` (:101), the
finite-left-endpoint Harnack `R(t) ≤ (b−a)R(b)/(t−a)` (`HamiltonHarnack/TerminalScalar.lean:64`). It also needs
`hbound : ∃ C, ∀ r ∈ Icc a b, |Rm| ≤ C` (:179) BEFORE the call: the bootstrap window `[a, 0]` must already carry
a bound. What X4a avoids is the ANCIENT Harnack (`R_t ≥ 0` on `(−∞, 0]`).

**G6. W1 kept an infinite-depth "any scale" κ reading.** `DCA:443–444` makes TimeControl:781 a corollary of W1,
and TimeControl's limit clause is `∀ ρ' > 0, ParabolicallyKappaNoncollapsedBelowScale … (infiniteClosed 0 0)
(κ/250) ρ'` (`Surgery/Topology/TracedRegionAncientLimitTimeControl.lean:950–951`). On a finite window
`(−T*, 0]` no such clause is available: a parabolic ball `[σ − r², σ]` must lie inside `[−τ_k, 0]` and its
spatial ball inside `V k`. `DCA:421` drops the limit κ clause silently instead of restating it windowed.

**G7. X4's conclusion at event-time trace points.** `DCA:519` avoids event slices by a countable exceptional
set; that handles hRP (with `A+1, D+1` margins) but not X4's own conclusion (`DCA:540–550`), whose slice
`w = tₙ − T'/Rₙ` may be an event time for infinitely many `n`. It needs W1's convergence uniformly on
`Icc (−inner) 0`, event times included (§1 X4-ev).

**G8. Anchors (H14 (b)).** `DCA:463–465` quantifies all anchors `∀ A Dd`. The base-centred choice
`A(s) = T*Q₀/(s+T*)` diverges, so X4a's proof must feed hRP only fixed `(A*, D*)`. X4d-Σ below is proved for
all `(A, D)` at no extra cost (the rebase level is `≤ max A 1 · Rₙ`), so X4a's hypothesis is unchanged; the
restriction is a constraint on X4a's PROOF, recorded in §2.

## 1. Statements (all elaborated)

Two scratch probes outside the tree, `lake env lean -DmaxSynthPendingDepth=3`, `LEAN_NUM_THREADS=2`, against the
pc3 build:
- probe A (6 declarations, 41 s): P3, P2, `extendAt`, P1s, P1 and X4d-Σ, inside the verbatim `Σ` block of
  `DCA:258–307` with `windowFarAccuracy` replaced by a variable `εfar`;
- probe B (2 declarations): the W1′ κ clause and the X4-ev identity.

Both produced only `declaration uses sorry` and are deleted. A third probe printed the axiom closures of the
delivered suppliers; each is `[propext, Classical.choice, Quot.sound]` (shared-olean caveat: only a fresh build
certifies):
- :20;
- B3e terminal (`BoundedCurvatureAtDistanceSliceTerminal.lean:249`) and B3e event (`…SliceEvent.lean:18`);
- the rebase point (`BoundedCurvatureAtDistanceSlice.lean:247`);
- `StandardActionComparison.lean:40, 115`, `StandardMetricControl.lean:55`;
- `OpenEmbeddingBallCapture.lean:52`.

Notation: `R n := (G n).flow.scalar (t n) (y n)`, `K n := (H n).extendAt …` as in `DCA:311`.

### 1.1 P3: evolved standard comparison (new, generic; `Perelman/StandardSolution/StandardCloseComparison.lean`, 80–150 lines)
```lean
theorem exists_scalar_metric_comparison_of_standard_close (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ η Cup Lc : ℝ, 0 < η ∧ 0 < Cup ∧ 0 < Lc ∧
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : SmoothRiemannianMetric (𝓡 3) U), ∀ τ ∈ Icc 0 T, ∀ x : U,
        (∀ j : ℕ, j ≤ 2 → metricDerivNorm j g ((Q.val.metric τ).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ η) →
        1 / 2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ Cup ∧
        ∀ v : TangentSpace (𝓡 3) x,
          (StandardCap.metric.restrictOpen U).inner x v v ≤ Lc ^ 2 * g.inner x v v
```
Suppliers:
- `(1/2)R_Q ≤ R_g` and `(1/2)g_Q ≤ g`: `StandardActionComparison.lean:40`;
- `R_g ≤ C`: `:115`;
- `1 ≤ R_Q`: `PartialStandardSolution.one_le_scalar` (`StandardScalarLower.lean:88`), with `S.one_le_lifetime`;
- `cap ≤ Λ·g_Q(τ)`: `MetricUniformEquivalentOn` (`StandardMetricControl.lean:55`), with `K` from
  `uniformStandardLifetime_slab`. So `Lc² := 2Λ`.

It is used at `T := 1/2`. In the history it reads `λ/2 ≤ R_v ≤ Cup·λ` on the young cap window: H14's
"`λ/2 ≤ R ≤ C'λ`", proved at the slice `v`, not at birth (G3).

### 1.2 P2: capture of the current ball by the window image (new, generic; next to `OpenEmbeddingBallCapture`, 60–120 lines)
```lean
theorem ball_subset_image_capWindow_of_scaled_lower {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) {D : ℝ} (Ξ : standardCapWindow D → M)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (hinj : Injective Ξ)
    (z₀ : standardCapWindow D) {r lam Lc : ℝ} (hr : 0 < r) (hlam : 0 < lam) (hLc : 0 < Lc)
    (hroom : ‖z₀.val‖ + r < D + 1)
    (hlower : ∀ (u : standardCapWindow D) (v : TangentSpace ThreeModel u),
      (StandardCap.metric.restrictOpen (standardCapWindow D)).inner u v v ≤
        Lc ^ 2 * (localPullMetric (scaleMetric lam hlam g) Ξ hΞ).inner u v v) :
    riemannianBallOf g (Ξ z₀) (r / (Lc * Real.sqrt lam)) ⊆
      Ξ '' {u : standardCapWindow D | ‖u.val‖ ≤ ‖z₀.val‖ + r}
```
Suppliers:
- `ball_subset_image_of_metric_lower_on_opens` (`Geometry/Comparison/OpenEmbeddingBallCapture.lean:52`), with
  `h := StandardCap.metric` on `E3`;
- `isCompact_metric_closedBall` (`Surgery/StandardCap/Distance.lean:198`);
- `radial_difference_le_edist` (`:134`), which gives `closedBall_cap(z₀, r) ⊆ {‖u‖ ≤ ‖z₀‖ + r} ⊆ window D`.

This is H14 (a)'s first-exit capture. A minimizing path that leaves `Ξ(window)` must cross `Ξ(sphere ‖z₀‖+r)`,
which is at current distance `≥ r/(Lc√λ)` from `Ξ z₀`. It uses no ¬CWP (G4), and needs survival of nothing
beyond `Ξ`'s domain.

### 1.3 P1s: the persistence inputs along `Σ` (new; `Surgery/Topology/CrossingPersistenceInputs.lean`, 100–200 lines)
```lean
theorem exists_capWindow_persistence_inputs_eventually :   -- in the Σ context
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x) ∧
      ∀ (Rw ζ₀ δ₀ Cbirth : ℝ) (m₀ : ℕ), 0 < ζ₀ → 0 < δ₀ → 0 < Cbirth → ∀ᶠ n in atTop,
        δb n ≤ δ₀ ∧ Rw ≤ (p₀ n).modelRadius ∧ m₀ ≤ (p₀ n).modelOrder ∧
        (p₀ n).modelAccuracy ≤ ζ₀ ∧
        ∀ i b, qcan n ≤ Cbirth * ((records n i).static b).neck.scale ∧
          1 ≤ a₀ * ((records n i).static b).neck.scale
```
Binder by binder against :20:

| :20 binder | Supply along `Σ` |
|---|---|
| `a₀` and the two initial clauses (:32–33) | `exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀` (`HamiltonIveyPinching.lean:666`), with `(hH n).1 : Nonempty (InitialIdentification …)` (`CanonicalNeighborhoodInduction.lean:166`); `a₀` is independent of `n` because `g₀` is fixed |
| `δbound ≤ δ₀` (:30) | `hpar.δb ≤ 1/(n+1)` |
| `R ≤ modelRadius` | `n+1 ≤ D n ≤ modelRadius` |
| `m₀ ≤ modelOrder` (`4 ≤ m₀` is :20's own output) | `n+2 ≤ modelOrder` |
| accuracy | `≤ 1/(n+1)` |
| `qcan ≤ Cbirth·λ` (:44), `1 ≤ a₀·λ` (:45) | `hscale : (n+1)·qcan ≤ λ` and `n+1 ≤ qcan`, so `λ ≥ (n+1)²` |
| `EventSlabsDerivative C qcan k`, `DerivativeBoundBefore C qcan t` (:36–37) | `hslabs`/`hbefore`, with `C := Ctime` and slices `v < t₀ n` |
| `θcap ≤ Θ` (:31) | `θcap = Θ = 1/2` |

### 1.4 P1: whole-window survival at the enlarged radius (new wrapper of :20; same file, 150–300 lines)
```lean
theorem eventually_capWindow_embedding_at_slice (Dw D₂ ε' : ℝ) (hDw : 0 < Dw) (hD : Dw < D₂)
    (hε' : 0 < ε') :                                            -- in the Σ context
    ∀ᶠ n in atTop, ∀ v : ℝ, (H n).time (Fin.last (H n).eventCount) < v → v < t₀ n →
    ∀ w : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) w v Dw (1 / 2) →
    ∃ (Ξ : standardCapWindow D₂ → ((H n).stage (Fin.last (H n).eventCount)).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
        ((n : ℝ) + 1) * qcan n ≤ lam ∧ τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (i : ℕ), i ≤ 2 →
          metricDerivNorm i
            (localPullMetric (scaleMetric lam hlam ((G n).flow.base.metric v)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < ε'
```
Route:
1. Apply :20 at `Θ = 1/2`, `C = Ctime`, `D := D₂`, `η := ε'`, `N := 2`, with inputs from P1s.
2. The CWP data `(j, A, b, x)` supply :41–43 (`‖x‖ < Dw + 1 < D₂ + 1`).
3. Compose `Ξ` with the incoming map: `CapWindowFlowPushforward.lean:72, 83` give the local diffeomorphism and
   injectivity of `(·).val.val`.
4. Set `λ := scale` and `τw := λ(v − H.time j.succ)`; `τw ≤ 1/2` is the CWP age.
5. The pulled-back metric identity is `window_metric_eq_localPullMetric_scaleMetric`
   (`CapWindowFlowPushforward.lean:229`), with :83–89 at `τ = τw`.

The event-slab form (slice `v` inside an event slab) is the same statement on `(H n).prefixAt k` through X1e,
exactly as for B3e-event.

This gives survival of the ENLARGED window from ONE anchor trace. The KL §74 dichotomy is not re-proved: either
`δ ≤ δ₀` excludes a later cut-in, or the whole block disappears, which the anchor's survival excludes. That
argument lives inside `WindowPersistence.lean:1029` (hypothesis `records.delta ≤ δ₀`, :1060).

### 1.5 X4d-Σ (replaces `DCA:486–514`; `Surgery/Topology/BoundedCurvatureAtDistanceAnchor.lean`, 400–800 lines)
```lean
theorem eventually_scalar_le_at_normalized_distance_of_anchor :   -- in the Σ context
    let K : ℕ → RetainedCoreHistory P₀ := fun n => (H n).extendAt (hH n).2.1 (G n) (hG n).2
      (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, σ < 0 → ∀ᶠ n in atTop,
      ∀ v : Icc (0 : ℝ) (K n).toHistory.horizon,
        (v : ℝ) = t n + σ / (G n).flow.scalar (t n) (y n) →
      ∀ z x : ((K n).toHistory.stageAt v).Carrier,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z ≤
          A * (G n).flow.scalar (t n) (y n) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z x <
          ENNReal.ofReal (Dd / Real.sqrt ((G n).flow.scalar (t n) (y n))) →
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
          C * (G n).flow.scalar (t n) (y n)
```
- **Quantifier order** `∀ A Dd, ∃ C, ∀ σ, ∀ᶠ n` (H14 (c)). `C` depends only on `(A, Dd)` and the `Σ` constants;
  `n₀ = n₀(σ, A, Dd)`.
- **No `T*`.** The statement is slice-wise, so every depth `σ < 0` is allowed. The slice lies in `(0, t₀ n)`
  eventually, because `R n · t₀ n → ∞` (F3) and `R n (t n − t₀ n) ≤ R n η n ≤ 1/(n+1)` (`hsliver` at `t' = t n`).
- **Event-time slices are included**, since `v` is any point of `Icc 0 horizon`. No exceptional set is needed
  downstream.

Constants, in order (`A' := max A 1`):
1. B3e terminal and event at `A_B := 2Dd√A' + 2`, `Cq := Cs`, `θ := 1/2`, giving `Q_B, Λ_B, D₁ := Dcap_B, Rrad_B, ζ_B`.
2. P3 at `T = 1/2`, giving `η₃, Cup, Lc`.
3. `r := 2(Dd+1)·Lc·√(2A'+2) + 1` and `D₂ := D₁ + 1 + r`.
4. P1 (:20) at `(1/2, Ctime, D₂, ε := η₃, η := η₃, N := 2)`, giving `R_P1, m₀, ζ₀, δ₀, Cbirth`; P1s holds eventually.
5. `C := max (Q_B·(A'+1)) (2·Cup·(A'+1)) + A' + 1`.

Per slice `v` strictly inside a slab (terminal form, or event form through `prefixAt`):
- If `R(x) ≤ A'·R n`, done.
- Otherwise take the rebase point from `ClosedSlab.exists_rebase_chain` (`BoundedCurvatureAtDistanceSlice.lean:247`),
  with threshold `q := R n ≥ qcan n` and the gradient bound from `hbefore`/`hslabs`. It gives `w` on a
  minimizing path from `z` to `x` with:
  - `R(w) = L := max (R n) (R z) ∈ [R n, A'·R n]`;
  - `d(z, w) < Dd/√R n`, so `d(w, x) < 2Dd/√R n ≤ 2Dd√A'/√L`.
- **(a) `¬ CWP(w, v, D₁, 1/2)`.** B3e at `w` gives `R(x) ≤ Q_B·L`. Its inputs: `q := qs n ≤ Cs·L`,
  `Λ_B ≤ L`, `Λ_B ≤ L·v`, `Λ_B ≤ ε√L`, κ at scale `ε`.
- **(b) `CWP(w, v, D₁, 1/2)`.**
  - P1 at `D₂` gives `Ξ, z₀, λ, Q, τw`.
  - P3 at `z₀` gives `λ/2 ≤ R(w) = L`, hence `λ ≤ 2A'·R n`.
  - P3's metric bound and P2 with `r` give `x ∈ Ξ(window D₂)`.
  - P3's upper bound gives `R(x) ≤ Cup·λ ≤ 2Cup·A'·R n`.

Slices at an event time `v = (K n).time i` are the start of a slab (`activeStage v = i`). Use right-continuity of
the slab flow at its left endpoint on the compact carrier, inside the per-`n` interval `[v, v + |σ|/(2R n)]`,
where every slice input still holds. The `A+1, Dd+1` margins are why `C` carries `A'+1`.

**Anchor restriction (H14 (b)).**
- The restricted statement is this theorem with `(A, Dd)` fixed to X4a's `(A*, D*)`. It is an instance, not a
  weaker lemma, because the proof above is uniform in `(A, Dd)`.
- So X4a's hypothesis (`DCA:463–465`, `∀ A Dd ∃ C`) is supplied as stated.
- What H14 (b) constrains is X4a's PROOF. It may call hRP only with `A*, D*` fixed before the window endpoint
  `a` (far-field escape anchors and the bootstrap), never with the base-centred `A(s) = T*Q₀/(s+T*)`.

### 1.6 X4-ev: the conclusion of X4 at event-time trace points (new lemma next to TimeControl, 60–120 lines)
```lean
theorem ObservedHistory.scalar_backwardPointTrace_eq_of_survivor_identity
    (K : ObservedHistory.{u}) (tn a w : Icc (0 : ℝ) K.horizon) (haw : a ≤ w) (hwt : w ≤ tn)
    {R : ℝ} (hR : 0 < R) {W : Opens (K.stageAt tn).Carrier}
    (h : ℝ → SmoothRiemannianMetric ThreeModel W)
    (f : (j : K.StageInterval (K.activeStage a) (K.activeStage tn)) → W →
      (K.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin K.eventCount) (hi : K.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ K.activeStage tn), ∀ x : W,
      (K.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlast : ∀ x : W, f ⟨K.activeStage tn, K.activeStage_mono (haw.trans hwt), le_rfl⟩ x = x.val)
    {σ : ℝ} (hσ : (w : ℝ) = tn + σ / R)
    (hid : ∀ j : K.StageInterval (K.activeStage a) (K.activeStage tn),
      (tn : ℝ) + σ / R ∈ K.stageDomain j.val →
        h σ = scaleMetric R hR (localPullMetric (K.stageMetric j.val ((tn : ℝ) + σ / R)) (f j)
          (hf j)))
    (x : W) (Bt : BackwardPointTrace K (K.activeStage w) (K.activeStage tn)
      (K.activeStage_mono hwt) x.val) :
    metricScalarAt (K.stageMetric (K.activeStage w) w)
        (Bt.point (K.activeStage w) le_rfl (K.activeStage_mono hwt)) =
      R * metricScalarAt (h σ) x
```
The hypotheses are literally TimeControl's survivor clauses (`TracedRegionAncientLimitTimeControl.lean:833–838`).
The identity holds for EVERY stage whose domain contains the slice, so at an event time both adjacent stages
agree on the survivors.

With it, X4 step 8 (`DCA:570`) becomes:
1. For `x ∈ B(ŷ, A/√R)` at `tₙ`, `x ∈ W k n` (`k + 3 ≥ A + 1`).
2. `Bt.point = f j x` by `BackwardPointTrace.point_unique` (`Surgery/Topology/Backward.lean:27`).
3. The identity gives `R(Bt.point) = Rₙ · R(h k n (−T'))(x)`.
4. W1's convergence gives `R(h k n (−T'))(x) ≤ C + 1` eventually. It is uniform over `s ∈ Icc (−inner_k) 0`,
   event times included, at `p = 2`, on the compact `φ`-preimage of the closed `(A+1)`-ball.

So `M := C + 1` (keep `2(C+1)`), uniformly in `T' < T*` once `T'` lies in the `k`-th inner window.

### 1.7 W1′: κ on inner windows only (delta to `DCA:397–444`)
The approximant κ-test clause stays as in `DCA:417–418`. It already carries `Icc (σ − r²) σ ⊆ Icc (−τ k) 0` and
the compact-ball capture in `W k n`.

The limit carries NO unconditional κ clause. If a consumer ever needs one, it is this per-`k` windowed clause
(elaborated):
```lean
    ∀ k : ℕ, ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ z : V k,
      ∀ r : ℝ, 0 < r →
      Icc (σ - r ^ 2) σ ⊆ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0 →
      IsCompact (riemannianClosedBallOf (Gloc k σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (Gloc k σ) z r,
        r ^ 4 * curvDerivNormSq 0 (Gloc k s) w ≤ 1) →
      ENNReal.ofReal (κ / 250 * r ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (V k) (Gloc k σ)
          (riemannianBallOf (Gloc k σ) z r)
```
No consumer in X4's chain reads a limit κ. Checked:
- B6 (`TracedRegionAncientLimitNeckAlternatives.lean:21`);
- B9 (`AncientPointedFlowLimitShiftedTransfer.lean:354`);
- B6d (`AncientPointedFlowLimitBoundedCurvature.lean`);
- X4a's hypotheses (`DCA:448–466`) have no κ.

So `DCA:443–444` is withdrawn: TimeControl:781 is NOT a corollary of W1. It keeps its own infinite-depth clause
(:950–951), used only by X5, where `τ_k = 2(k+2) → ∞`.

A glued clause on `openClosed (−T*) 0` is not needed now. If it were:
- time capture is automatic, since `ParabolicallyKappaNoncollapsedBelowScale` already requires
  `Icc (t − r²) t ⊆ D.carrier` (`Perelman/Noncollapsing/Parabolic.lean:30–31, 43`);
- spatial capture would come from `Rm ≥ 0`: `d_0 ≤ d_σ`, so `B_σ(z, r) ⊆ B_0(z, r) ⊆ V k` for large `k`.

## 2. Bricks, suppliers, order, and the clause deltas

| Brick | File (new) | Lines | Suppliers (`file:line`) | Depends on |
|---|---|---|---|---|
| P3 | `Perelman/StandardSolution/StandardCloseComparison.lean` | 80–150 | `StandardActionComparison.lean:40, 115`; `StandardScalarLower.lean:88`; `StandardMetricControl.lean:55` | none |
| P2 | `Geometry/Comparison/CapWindowBallCapture.lean` (or appended to `OpenEmbeddingBallCapture`) | 60–120 | `OpenEmbeddingBallCapture.lean:52`; `Surgery/StandardCap/Distance.lean:134, 198` | none |
| P1s | `Surgery/Topology/CrossingPersistenceInputs.lean` | 100–200 | `HamiltonIveyPinching.lean:666`; `CanonicalNeighborhoodInduction.lean:165–168`; `Σ.hpar/hscale/hslabs/hbefore` | `Σ` block |
| P1 | same file | 150–300 | `CapWindowStandardComparison.lean:20`; `CapWindowFlowPushforward.lean:72, 83, 229`; `HistorySurvivorIncoming.lean:65, 72` | P1s; X1e/X1k for the event and `K n` forms |
| X4d-Σ | `Surgery/Topology/BoundedCurvatureAtDistanceAnchor.lean` | 400–800 | B3e `…SliceTerminal.lean:249`, `…SliceEvent.lean:18`; rebase `…Slice.lean:247`; `capWindowPoint_of_prefixAt` (`RetainedCoreHistoryPrefixTransport.lean:177–216`) | P1, P2, P3, X1e, X1k, F3 |
| X4-ev | next to `TracedRegionAncientLimitTimeControl.lean` | 60–120 | `Backward.lean:27`; `metricScalarAt_scaleMetric` (`Geometry/Curvature/Metric/Scaling.lean:149`) | none |

The total is 0.85–1.7k lines, replacing X4d's 1.5–3k. The risk moves from X4d as a whole to one lemma, P1's
composition with the incoming map (a HEq-free restatement of :20's conclusion). All the mathematics of window
persistence is already delivered.

**Order:**
1. Now, in parallel: P3, P2, P1s and X4-ev.
2. Then P1, after P1s and X1e/X1k.
3. Then X4d-Σ.
4. Then X4, which also needs W1, X4a and the glue.

**Clause deltas:**

| Brick | Change | Exact delta |
|---|---|---|
| X4d | replaced | `DCA:486–514` goes; X4d-Σ (§1.5) and the P-bricks come in. `DCA:521–527` (route) is replaced by §1.5's case split; `DCA:515–519` (pull-back and exceptional set) by the transfer below. |
| X4 statement (`DCA:530–550`) | stays | — |
| X4 step 6 (`DCA:569`) | changes | hRP on the limit from X4d-Σ via the survivor maps. Fix `A, Dd`; take `C_lim(A, Dd) := C(A+1, Dd+1) + 1`. For `z, x` at slice `s` with `R_G(z,s) ≤ A` and `d_s(z,x) < Dd`, `C²`-convergence on a compact set containing a near-minimizing path gives, at the approximant, `R ≤ (A+1)Rₙ` and distance `< (Dd+1)/√Rₙ` (injective local isometries `f j` do not increase distance). X4d-Σ at `v = tₙ + s/Rₙ`, whose stage is `activeStage v`, matching the survivor identity. No exceptional set. |
| X4 step 8 (`DCA:570–571`) | changes | via X4-ev (§1.6); `M := 2(C+1)` stays. |
| X4 steps 1–5, 7 | stay | W1 at `τ_k = T*(k+1)/(k+2)`; inner depth `T*((k+1)/(k+2))² ↑ T*`. |
| X4a statement (`DCA:448–466`) | stays | — |
| X4a text | two corrections | (i) `DCA:481` "does not use Harnack" becomes: it uses finite-left-endpoint Harnack inside `TerminalScalar.lean:173` and needs `hbound` on `[a, 0]` before the call (G5). (ii) The proof must call hRP only at `(A*, D*)` fixed before `a` (G8). |
| X4ext (`DCA:551–558`, `573–577`) | stays | It consumes X4's `M` only. |
| X3 / X3p / X3a (`DCA:352–395`) | stay | W1′ removes only the limit κ clause, which X3 never reads (Transfer:440 and B9 carry no κ). |
| W1 (`DCA:397–444`) | changes | Approximant κ-test unchanged (already windowed); no limit κ clause (§1.7); `DCA:443–444` ("make TimeControl a corollary") withdrawn. |
| `DCA:766` table row | changes | X4d: 1.5–3k becomes P1–P3 + X4d-Σ + X4-ev at 0.85–1.7k; dependencies as above. |

## 3. Single-statement review prompt (H15: X4d-Σ with P1/P2/P3 as its engine)

> 背景：Lean 4/Mathlib 中带手术的三维 Ricci 流，反证序列 `Σ`。
> - `Hₙ` 为 cutoff 类历史，初始度量 `g₀` 固定。
> - 坏点 `(yₙ, tₙ)`，`Rₙ = R(yₙ, tₙ) → ∞`，`Rₙ t₀ₙ → ∞`，`Rₙ(tₙ − t₀ₙ) → 0`。
> - `t₀ₙ` 之前的所有切片上：阈值 `qsₙ ≤ Cs·qcanₙ` 以上有空间典范见证（精度 `ε ≤ coneAccuracy`）；导数界、梯度界
>   在 `qcanₙ` 以上成立；尺度 `ε` 处 `κ` 非塌缩。
> - `hpar`：`δₙ ≤ 1/(n+1)`，模型阶 `≥ n+2`，半径 `≥ n+1`，精度 `≤ 1/(n+1)`。
> - `hscale`：每个帽尺度 `λ ≥ (n+1)·qcanₙ`，其中 `qcanₙ ≥ n+1`。
>
> **断言（X4d-Σ）。** 对任意 `A, D > 0`，存在 `C`，使得对任意 `σ < 0`，对充分大的 `n`（`n₀` 可依赖于
> `σ, A, D`）：在切片 `v = tₙ + σ/Rₙ`（含事件时刻）上，若 `R(z) ≤ A·Rₙ` 且 `d_v(z, x) < D/√Rₙ`，则
> `R(x) ≤ C·Rₙ`。
>
> **证明引擎。**
> 1. 若 `R(x) ≤ A'Rₙ`（`A' = max A 1`）则结论已成立；否则沿 `z → x` 的极小测地线取重基点 `w`，使
>    `R(w) = max(Rₙ, R(z))`，且 `d(w, x) < 2D/√Rₙ`。
> 2. 若 `w` 不是 `CWP(D₁, 1/2)`：用已证的 B3e。
> 3. 若 `w` 是 `CWP(D₁, 1/2)`：
>    - (P1) 已证引理 `CapWindowStandardComparison:20`（`Θ = 1/2`，`C = Ctime`，半径取放大的 `D₂`）由 `w` 的
>      单个回溯给出整个 `D₂` 窗口的存活嵌入 `Ξ`，以及与某标准解 `Q(τ)`（`τ ≤ 1/2`）的 2 阶接近。
>      其全部输入沿 `Σ` 最终成立：`δ ≤ δ₀`，`m₀ ≤ 阶`（`m₀ ≥ 4`），`R ≤ 半径`，`ζ₀`，
>      `qcan ≤ Cbirth·λ`，`a₀λ ≥ 1`，Hamilton–Ivey 初始区域与 `R ≥ −3/a₀`（`a₀` 由 `g₀` 定）。
>    - (P3) 由 `R_Q ≥ 1`、`R_Q ≤ C_{1/2}`，以及接近性给出的 `½g_Q ≤ g`，在切片 `v` 上得到
>      `λ/2 ≤ R ≤ Cup·λ` 与 `cap ≤ Lc²·λ·g_v`；从而 `λ ≤ 2A'Rₙ`。
>    - (P2) 开嵌入球捕获：`B_v(w, r/(Lc√λ)) ⊆ Ξ({‖u‖ ≤ ‖z₀‖ + r})`，其中 `D₂ = D₁ + 1 + r`；于是 `x` 落在
>      窗口内，`R(x) ≤ 2Cup·A'·Rₙ`。
> 4. 事件时刻切片：在每个 `n` 内用右连续性，并留 `A+1, D+1` 余量。
>
> **请检查：**
> - (a) 断言是否为真；量词次序 `∀A D ∃C ∀σ ∀ᶠn` 是否正确（`C` 与 `σ`、`T*` 无关）。
> - (b) P1 的输入清单与 `:20` 的 binder 是否逐一对应、有无遗漏。尤其：导数阈值用 `qcan` 还是 `qs`；
>   `θcap = Θ = 1/2` 是否足够。
> - (c) 锚点：X4a 只以固定的 `A*, D*` 调用 hRP；本断言对一切 `A, D` 证明，这是否足以满足 X4a。
> - (d) 反例请求一：在放大窗口内、尺度 `~Rₙ^{-1/2}` 处，`v` 之前发生的后续手术切入。它是否确被 `:20`
>   内部的 KL §74 二分（小 `δ` 排除局部切入，或整块消失，而后者被锚点存活排除）所排除？
> - (e) 反例请求二：年龄在 `(1/2, 1)` 的锚点或重基点。此时它不是 `CWP(D₁, 1/2)`，交由 B3e 处理；B3e 以
>   `θ = 1/2` 调用时，其 `Dcap` 与假设是否仍覆盖年龄在 `(1/2, 1)` 的旧帽邻域？
> - (f) 重基点 `R(w) = max(Rₙ, R(z))`（阈值取 `Rₙ ≥ qcan`，梯度界在其上成立）是否满足 B3e 的
>   `q ≤ Cq·R(w)`、`Λ ≤ R(w)·v`。
