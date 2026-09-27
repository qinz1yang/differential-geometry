# Design: the exact assembly of the leaf `spatialCanonicalContinuation` (C4), 2026-09-26

This is a read-only design. It was made on `codex/pc-target-c-psf` @ 88a4eec5a (worktree
`D:\differential-geometry-pc3`), plus the uncommitted C4B deliveries M1a, M1b, M4, M4★ and M5. Paths
are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

**Probes.** Everything in §1 was elaborated in scratch probes outside the tree. They were compiled
with `lake env lean -DmaxSynthPendingDepth=3` and `LEAN_NUM_THREADS=2`. M5 was imported from
C4B3's scratch olean `C4B3.CapWindowSpatialCanonicalWitness`, whose source is byte-identical to the
tree file apart from the rewritten imports.
- Probe A contained P0, case (A) and the case-(C) brick as a `def`. It gave **0 errors**.
- Probe B was the complete leaf proof, with I29 applied, taking the case-(C) brick as a hypothesis.
  It gave **0 errors and no `sorry`**. Its only open input is the case-(C) brick.
- Both probes have been deleted.

## 0. Failures first

1. **Case (C) cannot be discharged from C3's output. It needs a Crossing-core brick.** C3's output
   is `CanonicalOn ε C1 C2 qcan τmin t₀ η` (`Surgery/Topology/CanonicalNeighborhoodInduction.lean:44`).
   It asserts a witness only under `τmin ≤ R(t − a)`, and that is exactly the complement of case (C).
   `DerivativeBoundOn` and `GradientBoundOn` give no witness. Two other sources fail as well:
   - The Crossing leaf (`CanonicalNeighborhoodContinuationLeaves.lean:232`) outputs
     `CanonicalBoundsOn … fun y t => R(t−a) < θ ∧ ¬CWP`. Its witness clause is again gated by
     `τmin ≤ R(t−a)`, so it is vacuous on (C). Review G item 6 says the same.
   - Forward persistence of the induction's own spatial witnesses was refuted in `DESIGN_C4.md`
     failure 2.

   **Fix:** a new sibling brick `SpatialCrossingContinuation` (§1.3). It is proved by Crossing's
   contradiction sequence, reusing X0–X5, together with a spatial per-point finish (X5s and X6s, §2).
   It is the only open mathematics left in C4.
2. **The leaf has no `εbar`, but case (C) needs one. INTERFACE FIX I29.**
   - `SpatialCanonicalContinuation` (`Surgery/Topology/SpatialCanonicalContinuation.lean:144`)
     quantifies over every `ε < 1/11`.
   - The Crossing machinery needs `ε ≤ εbar`, with
     `εbar = min coneAccuracy (min epsW (windowFarAccuracy/2))` (`DESIGN_CROSSING_ASSEMBLY.md` §1).
     B3d, B11 and X4a consume the hypotheses' spatial necks at that accuracy.
   - For `ε ∈ (εbar, 1/11)` the hypotheses hold only at accuracy `ε`, so the young clause cannot be
     produced. Lowering `ε` does not help, because every hypothesis is stated at the same `ε`.

   I29 (about 8 lines, two committed files, done by the acceptance lane):
   - Prefix the leaf def with `∃ εbar : ℝ, 0 < εbar ∧` and add `ε ≤ εbar →` after `ε < 1 / 11 →`.
     The body is otherwise unchanged.
   - In `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`
     (`CanonicalNeighborhoodsThroughSurgeryStrong.lean:272`), add
     `obtain ⟨εs, hεs, hspat⟩ := hspat`, then `refine ⟨min εbar εs, lt_min hεbar hεs, ?_⟩`, and feed
     `hεbar'.trans (min_le_left _ _)` to `hcont` and `hεbar'.trans (min_le_right _ _)` to `hspat`.

   `PoincareEndgame.lean` is unchanged. The assembly edit was not probed, but it only threads a
   `min`, and the downstream `CanonicalNeighborhoodsThroughSurgeryStrong` already carries its own
   `εbar`.
3. **No floors are needed, and none are available.** The leaf quantifies `C1 C2 τmin Ctime Cgrad`
   with only `1 ≤ C1`, `1 ≤ C2` and `0 < τmin`. It has none of C3's floors.
   - M5 takes every `Ctime Cgrad`.
   - SX must also be floor-free. Its conclusion constant `Cx` is its own (B8's `C` at `ε`), and the
     hypothesis constants only have to be finite.
   - Crossing's single floor-forcing supply is F9 (`Ctime₀ ≥ Cs_start`, the slab-start derivative
     extension for B5's `hcurrent`). Here that supply is replaced by the C3 output that C4 already
     receives (`DerivativeBoundOn Ctime qcan t₀ η`), through P0. **So SX must take the C3 output as a
     hypothesis, exactly as the leaf does.** It is not a circularity: SX is used only inside C4, and
     C4 receives that output from C3.
4. **Binder order and constants versus M5. No mismatch.** Probe B checked all of the following.
   - M5's `∃ Cs` (a witness constant; it is `Cw` below, not the leaf's `Cs`) depends on `ε` only,
     so it comes before `C1s C2s`.
   - `(Dw, θcap) := (Dx, θcap)` come from SX, after `κ phi` with `θ := τmin`. They are fed to M5,
     which returns `(Rcap, mcap)` before `qcan`.
   - M5 needs only `0 < qcan`, from `q₀ ≤ qcan`.
   - `(δmax, ρmax, εcap)` are the mins of SX's and M5's values.
   - The leaf outputs `Dcap := max Dx Rcap` and `mcap := max mx mw`.
   - The leaf's threshold ratio is `Cs := 1`, with `qs := qcan`.
   - M5's inputs, and where each one comes from:

     | M5 input | Supply |
     |---|---|
     | `Nonempty InitialIdentification` | `hH.1` |
     | `recenterConstant·δ ≤ 1/2` | `hH.2.2.2.2` |
     | records | `hasCanonicalCutoffRecords_iff_…` on `hH.2.2.2.1` |
     | `Gk.base.metric a = initialMetric k` | `H.event_initial j` / `hG.2` |
     | `EventSlabsDerivative Ctime qcan k` | the leaf hypothesis |
     | `Gk.DerivativeBoundBefore Ctime qcan t` | P0 from `Before t₀` and `On[t₀, t₀+η₃)` |
     | the gradient at `(y,t)` | C3's `GradientBoundOn` (`qcan = qs < R`) |

   - The event branch's `IncomingSlab (H.time j.castSucc) (H.time j.succ)` unifies with M5's
     `(k, s, Gk)` directly.
5. **ULift, reference conversion and transport margins are internal to M5 and closed.**
   - M3 `pushforwardOfInjectiveULift`
     (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniverseTransport.lean:1098`),
     M2 `_of_lt` with `D' = D − 1`, and the M1a margins (`m = 1/20`) are all consumed inside M5.
   - The leaf itself never meets a universe gap or a margin.
   - Case (C) needs no ULift. Its carry is along `U ↪ carrier` with `U : Opens carrier` in the same
     universe, so the committed same-universe `SpatialCanonicalWitness.pushforwardOfInjective`
     (`SpatialCanonicalWitnessTransport.lean:1048`) is enough. That lemma requires `2·radius < R`
     and a compact `closedBall R`. Both come from the traced region's compact half-ball
     (`TracedRegion.lean:598/722`, `ρ = A/√R` with `A > 4Cx`).
6. **Carried-over acceptance debt, not a C4 defect.** M5 and its five C4B2 prerequisites are
   uncommitted, and they were verified only as scratch modules. Their merges are deferred:
   - M3 into `SpatialCanonicalWitnessTransport`;
   - the M1a producer bodies into 27c;
   - M4★'s private copies.

   The probe's M5 olean dates from 11:26 and was built against the then-current shared build. Only
   the acceptance build proves it.
7. **Option A of `DESIGN_S_SUPPLY` (strong-neck interface), for the record only; not designed here.**
   If adopted, H13 item (3) adds to C4 an old-point embedding with `first := k` and a choice of `W`
   compatible with the strong property, carried through `Before`/`On` and the induction. That lands
   in case (A) and in SX. `DESIGN_STRONG_INTERFACE.md` is still a header only.

## 1. Exact statements (elaborated)

Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`. Opens: `Set`, `…FiniteHorn`,
`scoped Manifold NNReal`.

### 1.1 P0 and case (A), in `namespace OrientedThreeStage.IncomingSlab` (both proved in probe A, about 20 lines)
```lean
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem derivativeBoundBefore_of_derivativeBoundOn {Ctime : ℝ≥0} {qcan t₀ η t : ℝ}
    (hB : G.DerivativeBoundBefore Ctime qcan t₀) (hO : G.DerivativeBoundOn Ctime qcan t₀ η)
    (htη : t ≤ t₀ + η) (hts : t ≤ s) : G.DerivativeBoundBefore Ctime qcan t

theorem exists_spatialCanonicalWitness_of_canonicalOn {ε C1 C2 C1s C2s qcan qs τmin t₀ η : ℝ}
    (h1 : C1 ≤ C1s) (h2 : C2 ≤ C2s) (hq : qcan ≤ qs)
    (hcan : G.CanonicalOn ε C1 C2 qcan τmin t₀ η) {y : P.Carrier} {t : ℝ} (hat : a < t)
    (ht₀ : t₀ ≤ t) (htη : t < t₀ + η) (hts : t < s) (hR : qs < G.flow.scalar t y)
    (hold : τmin ≤ G.flow.scalar t y * (t - a)) :
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1s C2s y, W.capTubeHasNeckChart ε
```
The proofs:
- P0: split `t' < t₀` against `t₀ ≤ t'`.
- (A): `obtain ⟨W, hW⟩ := hcan …`, then
  `⟨W.toSpatial.enlargeConstants h1 h2, (W.capTubeHasNeckChart_toSpatial hW).enlarge_constants h1 h2⟩`.

### 1.2 Case (B): M5, consumed verbatim

`RetainedCoreHistory.exists_capWindowPoint_spatialCanonicalWitness`
(`Surgery/Topology/CapWindowSpatialCanonicalWitness.lean:31`, statement in `DESIGN_C4B.md` §2 M5).
Its output is `SpatialCanonicalWitness (Gk.flow.base.metric t) ε Cw (max Cw Cgrad) y`.

### 1.3 Case (C): the new brick `SpatialCrossingContinuation` (a `def`, elaborated)

It has Crossing's shape (`CanonicalNeighborhoodContinuationLeaves.lean:232`), with three
differences:
- there are no floors;
- the C3 output is an extra hypothesis;
- the conclusion is a spatial witness at young, non-CWP points, with its own constant `Cx` chosen
  before `C1s C2s`.
```lean
def SpatialCrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ Cx : ℝ, 1 ≤ Cx ∧
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi → 0 < θ →
  ∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory P₀) (hH : H.InCutoffClass g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          (∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η ∧
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η ∧
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η) →
          ∃ η : ℝ, 0 < η ∧ ∀ (y : (H.stage j.castSucc).Carrier) (t : ℝ),
            H.time j.castSucc < t → t₀ ≤ t → t < t₀ + η → t < H.time j.succ →
            qs < (H.toHistory.event j).incoming.flow.scalar t y →
            (H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc) < θ →
            ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness
                ((H.toHistory.event j).incoming.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          (∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧
            G.GradientBoundOn Cgrad qcan t₀ η ∧ G.CanonicalOn ε C1 C2 qcan τmin t₀ η) →
          ∃ η : ℝ, 0 < η ∧ ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
            H.time (Fin.last H.eventCount) < t → t₀ ≤ t → t < t₀ + η → t < s →
            qs < G.flow.scalar t y →
            G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ →
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε
```
Name check: `SpatialCrossingContinuation` is unused library-wide. The probe elaborated the same
body under a scratch name.

### 1.4 Combination and the leaf skeleton (probe B: complete, sorry-free given SX)

Constants:

| Output | Value | Notes |
|---|---|---|
| `C1s` | `max C1 (max Cw Cx)` | covers (A) `C1`, (B) `Cw`, (C) `Cx` |
| `C2s` | `max C2 (max (max Cw Cgrad) Cx)` | covers (A) `C2`, (B) `max Cw Cgrad`, (C) `Cx` |
| `Cs` | `1` | |
| `q₄` | SX's `q₀` | |
| `qs` | `qcan` | |
| `δmax`, `ρmax`, `εcap` | mins of SX's and M5's values | |
| `Dcap` | `max Dx Rcap` | |
| `mcap` | `max mx mw` | |
| `η` | `min η₃ ηX` | |

Every choice sits in a binder slot that comes after what it depends on:
- `Cx` and `Cw` depend on `ε` only;
- `Dx`, `θcap` and `qx` depend on `κ phi τmin` and `C1s C2s`;
- `Rcap` and `mw` depend on `Ctime Cgrad Dx θcap`.
```lean
theorem spatialCanonicalContinuation_of_spatialCrossing (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) (hX : SpatialCrossingContinuation P₀ g₀) :
    SpatialCanonicalContinuation P₀ g₀ := by          -- the I29 form
  obtain ⟨εbar, hεbar, hX⟩ := hX
  refine ⟨εbar, hεbar, ?_⟩
  intro B ε hB hε hε' hεb C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  obtain ⟨Cx, hCx, hX⟩ := hX B ε hB hε hε' hεb
  obtain ⟨Cw, hCw, hM5⟩ :=
    RetainedCoreHistory.exists_capWindowPoint_spatialCanonicalWitness P₀ g₀ hε hε'
  set C1s := max C1 (max Cw Cx); set C2s := max C2 (max (max Cw (Cgrad : ℝ)) Cx)
  -- hA1 hA2 : C1 ≤ C1s, C2 ≤ C2s;  hB1 hB2 : Cw ≤ C1s, max Cw Cgrad ≤ C2s;  hX1 hX2 : Cx ≤ C1s, C2s
  refine ⟨C1s, C2s, 1, le_max_of_le_left hC1, le_max_of_le_left hC2, le_rfl, ?_⟩
  intro κ phi hκ hphi
  obtain ⟨Dx, θcap, qx, mx, hDx, hθcap, hqx, hXq⟩ :=
    hX C1 C2 τmin Ctime Cgrad hC1 hC2 hτ C1s C2s 1 _ _ le_rfl κ phi τmin hκ hphi hτ
  obtain ⟨Rcap, mw, hRcap, hM5q⟩ := hM5 Ctime Cgrad Dx θcap hDx hθcap
  refine ⟨qx, hqx, fun qcan hqcan => ?_⟩
  obtain ⟨δx, ρx, εx, hδx, hρx, hεx, hXs⟩ := hXq qcan hqcan
  obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hM5s⟩ := hM5q qcan (hqx.trans_le hqcan)
  refine ⟨qcan, min δx δw, min ρx ρw, min εx εw, max Dx Rcap, max mx mw, le_rfl,
    (one_mul qcan).ge, lt_min hδx hδw, lt_min hρx hρw, lt_min hεx hεw, lt_max_of_lt_left hDx, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ H hH hpinch
  obtain ⟨p, records, hrec⟩ := (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
    p₀ δbound ρbound).mp hH.2.2.2.1
  have hXH := hXs qcan le_rfl (one_mul qcan).ge p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hD) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH p records hrec hpinch
  have hW := hM5s p₀ δbound ρbound (hacc.trans (min_le_right _ _)) ((le_max_right _ _).trans hD)
    ((le_max_right _ _).trans hm) (hδ.trans (min_le_right _ _)) (hρ.trans (min_le_right _ _))
    H hH.1 hH.2.2.2.2 p records hrec
  refine ⟨fun j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hC3 => ?_,
    fun s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn hC3 => ?_⟩
  · -- event branch; the terminal branch is identical with G, hG.2, hderL, Fin.last
    obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
    obtain ⟨ηX, hηX, hYoung⟩ := hXH.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn
      ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩
    refine ⟨min η₃ ηX, lt_min hη₃ hηX, fun y t hat ht₀' htη hts hR => ?_⟩
    -- htη₃ : t < t₀ + η₃,  htηX : t < t₀ + ηX
    rcases le_or_gt τmin (Gk.flow.scalar t y * (t - H.time j.castSucc)) with hold | hyoung
    · exact Gk.exists_spatialCanonicalWitness_of_canonicalOn hA1 hA2 le_rfl hcOn hat ht₀' htη₃
        hts hR hold                                                          -- (A)
    by_cases hcw : H.CapWindowPoint records j.castSucc y t Dx θcap
    · obtain ⟨W, hW'⟩ := hW j.castSucc (H.time j.succ) Gk (H.event_initial j) hderP t hat hts
        (Gk.derivativeBoundBefore_of_derivativeBoundOn hd hdOn htη₃.le hts.le) y hcw hR
        (hgOn y t hat ht₀' htη₃ hts hR)                                      -- (B) = M5
      exact ⟨W.enlargeConstants hB1 hB2, hW'.enlarge_constants hB1 hB2⟩
    · obtain ⟨W, hW'⟩ := hYoung y t hat ht₀' htηX hts hR hyoung hcw          -- (C) = SX
      exact ⟨W.enlargeConstants hX1 hX2, hW'.enlarge_constants hX1 hX2⟩
```
Here `Gk := (H.toHistory.event j).incoming`. In the elaborated text it is spelled out and the
`have`s are explicit. The endgame change is:
`theorem spatialCanonicalContinuation … := spatialCanonicalContinuation_of_spatialCrossing P₀ g₀
(spatialCrossingContinuation P₀ g₀)`, with the new skeleton leaf
`spatialCrossingContinuation : SpatialCrossingContinuation P₀ g₀` carrying the `sorry`.

## 2. Brick table

**Delivered** (uncommitted; acceptance registers them):

| Brick | File |
|---|---|
| M1a | `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMargins.lean` and `Perelman/StandardSolution/StandardSpatialCanonicalMargins.lean` |
| M1b | `Perelman/StandardSolution/StandardWindowBallPlacement.lean` |
| M4 | `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniformTransport.lean` |
| M4★ | `Perelman/StandardSolution/StandardWindowSpatialCanonical.lean` |
| M5 | `Surgery/Topology/CapWindowSpatialCanonicalWitness.lean:31` |

M2, M3 and G are already committed (9d37f6e47). Case (B) is **closed**.

**Remaining**, in order:

| # | Brick | Where (new unless noted) | Lines | Depends on |
|---|---|---|---|---|
| I29 | `εbar` in the leaf + `min` in the strong assembly | edits `SpatialCanonicalContinuation.lean:144`, `CanonicalNeighborhoodsThroughSurgeryStrong.lean:272` | 8 | — |
| P0+A | §1.1 (proofs exist in the probe) | `Surgery/Topology/SpatialCanonicalContinuationCases.lean` | 25 | — |
| SXdef | `SpatialCrossingContinuation` def + skeleton leaf stub | new file `Surgery/Topology/SpatialCrossingContinuation.lean`, `PoincareEndgame.lean` | 90 | I29 |
| L | `spatialCanonicalContinuation_of_spatialCrossing` (§1.4, probe-complete) | same file as P0+A | 90 | P0+A, M5, SXdef |
| X5s | spatial clause in BOTH age modes (see below) | `Surgery/Topology/CrossingAncientLimitSpatial.lean` | 300–600 | X5's inputs, B6b′/W1, B8 `AncientLimitCanonicalWitness.lean:117`, `TracedRegion.lean:598/722` |
| X6s | carry the witness to `Gk.flow.base.metric t` | `Surgery/Topology/CrossingSpatialClauseTransport.lean` | 100–200 | `toSpatial` (`Projection:92/110`), `pushforwardOfInjective` (`Transport:1048`), the `S t = (Gk t)|_U` clause of `TracedRegion.lean:598` |
| X7s | the SX leaf by contradiction: X7 with a spatial bad clause, and the sliver's derivative supply from the C3-output hypothesis instead of F9 | `Surgery/Topology/SpatialCrossingContinuationLeaf.lean` | 300–500 | X0–X4, X4ext, X5s, X6s |

X5s:
- Apply B8 to the **traced common flows** `S n` on `U n = B(yₙ, Aₙ/√Rₙ)` over
  `[tₙ − Tₙ/Rₙ, tₙ]`. Take `X.obj n := U n`, `Aₙ, Tₙ → ∞` diagonally, which is available in the
  `T* = ∞` branch.
- Then B8's window hypothesis holds in the young mode too, and no age split is needed.
- `toSpatial` gives the witness for `(Gk t)|_U`.
- Fallback (worse): take the limit's time-0 spatial witness and transport it with the witness-first
  lemmas. That route is blocked by the cap depth/sandwich margins (`DESIGN_C4B.md` §0.3).

Totals:
- C4 itself: about 210 lines, of which about 205 are already written in probes.
- New Crossing-side work for case (C): 0.7–1.3k lines. It reuses X0–X4, X4ext, W1, X5c and X5d from
  `DESIGN_CROSSING_ASSEMBLY.md` §3 (6.5–11.5k, counted under C3c).

Order:
1. I29, P0+A, SXdef and L now. This turns C4 into a closed reduction to SX.
2. X5s and X6s after W1 and B13.
3. X7s after X7, as a copy-edit of it.

## 3. Single-statement review prompt (SX, the only open piece of C4)

请审查下面这一个 Lean 陈述：`SpatialCrossingContinuation`，C4 情形 (C) 所用的年轻空间典范邻域。

**背景。** 这是 Lean 4/Mathlib 中带手术的三维 Ricci 流。`H` 为 cutoff 类的保留核历史，`Gk` 为第
`k` 片的入流，片起点记为 `a`。

**量词顺序。** `∃ εbar`，`∀ B ε ≤ εbar`，`∃ Cx ≥ 1`（只依赖 `ε`），`∀ C1 C2 τmin Ctime Cgrad`
（**无下界**），`∀ C1s C2s Cs ≥ 1`，`∀ κ phi θ > 0`，`∃ Dcap θcap < 1 q₀ mcap`，`∀ qcan ≥ q₀`，
`∃ δmax ρmax εcap`，`∀ qs ∈ [qcan, Cs·qcan]`，然后对类中所有历史、记录族与 pinching 断言下述结论。

**假设。**
- 此前各片的 `Before` 条款：强见证（龄 ≥ τmin）、导数界、梯度界，以及空间见证（`C1s C2s`，
  阈值 `qs`）。
- 当前片在 `t₀` 之前同样的四个条款。
- 截至 `t₀` 的 κ 非塌缩。
- C3 在 `[t₀, t₀+η)` 上的输出：导数界、梯度界，以及龄 ≥ τmin 处的强见证。

**结论。** 存在 `η > 0`，使得对 `t ∈ [t₀, t₀+η)` 中的每个点 `(y,t)`，只要满足
- `qs < R`，
- `R(t−a) < θ`，
- `¬CapWindowPoint(y, t, Dcap, θcap)`，

就存在 `SpatialCanonicalWitness (Gk t) ε Cx Cx y` 且 `capTubeHasNeckChart ε`。

**拟证路线。** 沿 Crossing 的反证序列进行：X0–X4 给出最大深度 `T* = ∞`。随后在追溯公共流
`S n : B(yₙ, Aₙ/√Rₙ) × [tₙ − Tₙ/Rₙ, tₙ]` 上应用 B8，得到时空见证；投影为空间见证后，沿
`U ↪ carrier` 推前。不做龄的分拆。

**请回答：**
1. 陈述是否为真？尤其是在无 `C1…Cgrad` 下界、只有 `ε ≤ εbar` 的条件下是否成立；`Cx` 能否只依赖
   `ε`，放在 `C1s C2s` 与 `κ` 之前。
2. 量词顺序是否正确：`Dcap θcap` 依赖 `θ = τmin` 与 `κ`；`η` 在 `t₀` 之后选取。以 C3 的导数输出
   替代 slab-start 延拓（Crossing 的 F9）是否足够。
3. 是否存在退化或空洞的情形。例如：刚过事件、位于帽窗口之外但仍在手术帽附近的点，其正规化龄介于
   `θcap` 与 1 之间。
4. 请尝试构造反例：年轻点的回溯跨越多个相距很近的事件；κ-解极限为紧致（三个 `S³` 分量）时
   `whole` 分支的连通分量不在 `U` 内；`2·radius < ρ/2` 的球捕获失败。
