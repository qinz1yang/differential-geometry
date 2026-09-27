# Design: the base slice of the Crossing contradiction sequence (flag F-g), 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ 9126abc30 plus uncommitted lanes (B3F slice files).
Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`. All statements in §2 were
elaborated with `sorry` bodies in one scratch probe outside the tree (`LEAN_NUM_THREADS=2`, 38 s).
Output: only `declaration uses sorry`. The probe has been deleted. The B3F slice modules have no
olean, so the probe imports `BoundedCurvatureAtDistanceConstants` (for `coneAccuracy`) and restates
nothing from B3F. The composed statements reuse B3F's signature shape verbatim.

The lead's note (H7 digest) is binding. The sliver `[t₀ₙ, tₙ]` and the slice `t₀ₙ` carry no
witness, no noncollapsing and no derivative data. `ηₙ` is shrunk first, then the point is picked.
`htraced` must be produced without B7/B13.

## 0. Failures first

**F1. "Choose `ηₙ` after `Hₙ`": TRUE, with one required order.**
- In `CrossingContinuation` (`Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean:232`),
  `∃ η` comes after `H`, `t₀` and every "before" hypothesis. So the negation, for fixed `n`, is
  `∀ η > 0, ∃ bad (y, t) ∈ [t₀ₙ, t₀ₙ + η)`.
- Every per-`n` smallness must be packed into the single `ηₙ`, fixed before the point is picked:
  - `Rₙ·ηₙ ≤ 1/(n+1)` (B1 / `hsliver`);
  - `C⁰` closeness `ζₙ := qcanₙ/4`;
  - the cap-age slack `Sₙ·ηₙ ≤ 1/(n+2)`;
  - the derivative extension window.
- BS2 below does this packing.
- Since `qcanₙ < Rₙ` for every bad point, the absolute tolerance `qcanₙ/4` is already a relative
  tolerance `≤ Rₙ/4`. The lead's `Kₙ`-normalisation (`Rₙ ≤ 2Kₙ`) is correct but not needed.

**F2. "The base point at `t₀` may lie in another carrier": FALSE as a worry.**
- `CanonicalBoundsOn` requires `a < t < s`. So `[t₀, t)` lies inside one slab `[a, s)`, over one
  carrier, and events occur only at `a` and `s`.
- The point `yₙ` is the same point at `t₀ₙ` and at `tₙ`.
- A carrier change happens only when a slice `σ < t₀` is used with `t₀ = a` (Case II, F4).

**F3. "Fresh-cap points are not in the Crossing core": FALSE in general, TRUE at `t₀ = a` after the
per-`n` choice.**
- A fresh cap point with age in `(θcap/scale, θ/R)` is young and is not a `CapWindowPoint`. So it is
  in the core whenever `θ > θcap·R/scale`, and `θ` is arbitrary.
- At `t₀ₙ = aₙ`, take `Sₙ·ηₙ ≤ θcapₙ` with `Sₙ := max scale` (BS4). A point without a backward trace
  is then captured by `exists_cap_capture` (`Surgery/Topology/EventCapCapture.lean:143`), with
  `‖x‖ ≤ transitionEnd < Dₙ + 1`, and its age is `≤ ηₙ ≤ θcapₙ/scale`. So it is a `CapWindowPoint`,
  hence not bad.
- Consequence: in Case II, `yₙ` is retained and has a `RegularCrossing` preimage
  (`exists_regularCrossing_of_not_mem_capRegion`, `MetricCutCapScalarLower.lean:544`).
- The same capture gives `¬ CapWindowPoint … y a …` ⇒ `y` is retained, at age 0.

**F4. The candidate's two continuity lemmas collapse to one, and the route FAILS at stage starts.**
- For `t₀ > a`, the window `[t₀ − δ, t₀ + δ]` is interior to `[a, s)`. One uniform-continuity
  statement (BS1) serves both the left transfer `σ ↑ t₀` and the sliver `[t₀, t]`.
- For `t₀ = a` there is no slice `σ < t₀` in the stage. The left transfer must cross the event
  (Case II). That needs:
  - the terminal convergence (`TerminalMetricConverges`, `Surgery/Topology/EventData.lean:231`),
    which holds only on compact subsets of `terminalRegularOpen`;
  - the cap records for the fresh part of the ball.
- This is a genuinely new brick (BS6) and the risk item of this design.

**F5. `C^p` sliver negligibility (candidate (a)) is not needed.** Every consumer at base `tₙ` is
`C⁰`:
- B3e's output is a scalar ball bound;
- `isTracedRegion` is an `|Rm|` bound along traces (`Surgery/Topology/TracedRegion.lean:76`);
- B6b′'s jets come from Shi on the traced region.

`C^p` would only matter for transporting witnesses onto sliver slices. This design avoids that, since
B6D_GLUE's time-shift device already samples below `t₀`. The `C^p` statement is elaborated (BS1′)
but is optional.

**F6. B5, the B7 step and X2 at base `tₙ` do NOT need a base shift.** Their only sliver input is
`DerivativeBoundBefore C qcan tₙ` (`hcurrent`).
- Per `n`, `exists_derivativeBoundBefore_extend_of_slice` (`DerivativeBoundExtension.lean:66`)
  supplies it with `(2·Ctime, 2·qcanₙ)` on `(a, t₀ₙ + η)`. So does its gradient twin (`:176`).
- B5 (`TracedRegionOrCapWindow.lean:665`) is `∀ C, ∃ Cbirth`, so the constant `2·Ctime` is legal. The
  threshold `2qcanₙ` enters `hbirth`, which the M6 order (`ρmax` after `qcan`) absorbs.
- This also resolves B6D_GLUE F-f: B12's cutoff restatement becomes unnecessary; feed `hcurrent`
  with the doubled constants instead.
- **The only base-slice consumer that cannot be fed on the sliver is B3e.** It needs witnesses on the
  whole slice and noncollapsing up to the slice.

**F7. `Rₙ → ∞` survives.** `qcanₙ < Rₙ` with `qcanₙ ≥ n`. Inside BS5 the auxiliary slice `σ`
satisfies `R(σ, yₙ) ∈ [Rₙ/2, 3Rₙ/2]`. Also `Rₙ·t₀ₙ ≥ Rₙ·tₙ − 1 → ∞` (M7(c)), because
`Rₙ(tₙ − t₀ₙ) ≤ 1/(n+1)`.

**F8. Derivative- or gradient-clause failure changes nothing here.**
- BS5 and BS6 ignore which clause fails.
- B8 derives all three clauses at `(yₙ, tₙ)` from the limit at time 0:
  - spatial `C^p` convergence at the base slice;
  - `tₙ` interior, so `derivWithin (Iic tₙ)` equals `ΔR + 2|Ric|²`.
- In Case II the witness clause is vacuous per `n` (`R(t − a) ≤ R·ηₙ ≤ 1/(n+1) < τmin`), so bad
  points there fail the derivative or gradient clause. This is consistent with LEAD_NOTES "L10b".

**F9. The C3 conclusion at exactly `t = t₀ = a` is never required.** `CanonicalBoundsOn` has
`a < t` (`CanonicalNeighborhoodContinuationLeaves.lean:28`). The post-surgery slice is only an
intermediate slice inside BS6.

**F10. `t₀ₙ = aₙ = 0` has no bad points once `qcanₙ > Q₀ + 1` (BS7).**
- `exists_scalar_lt_at_initial_slab_start` (`SlabStartDerivativeBounds.lean:19`) gives `R(0, ·) < Q₀`.
- BS1 with `ζ = 1` gives `R ≤ Q₀ + 1` on `[0, ηₙ]`, which contradicts "∀ η, ∃ bad point".
- This replaces the M7(c) argument for this case.

**F11. `hsliver` (B13) is orthogonal.**
- It is supplied by BS2's `R·η ≤ ζ` component.
- The `E n` device stays, because event times pin normalized times (B6D_GLUE F-b).
- Witnesses on sliver slices would need F5's `C^p` transport, which costs more than the device.
- The only simplification is F6: B12 is dropped.

## 1. Route (net)

| Base-slice use (DESIGN_MAXWINDOW) | Case I: `t₀ₙ > aₙ` | Case II: `t₀ₙ = aₙ > 0` |
|---|---|---|
| §3.2b step 1, B3e ball bound at `tₙ` | BS5: B3e at an internal slice `σ ∈ (a, t₀)` plus the `C⁰` transfer BS1 | BS6: B3e at `σ` in the previous stage, then across the event, then forward by BS1 |
| §3.2b step 2 / §3.3 / §4.3, B7 step and B5 at `tₙ` | unchanged at `tₙ`, `hcurrent` from BS2 `(2Ctime, 2qcanₙ)` | same (BS2 at `t₀ = a` via `exists_derivativeBoundBefore_extend_at_start`, `SlabStartSliceBounds.lean:288`, and `RetainedCoreHistory.exists_slice_bounds_at_slab_start`, `SlabStartDerivativeBounds.lean:94`) |
| B6b′/B13 `htraced` at `tₙ` | B5 at `tₙ` (right branch excluded by `¬CWP(tₙ)`, directly) | same |
| `¬CWP` input to B3e | `¬CWP(yₙ, t₀ₙ, Dₙ, θcapₙ − 1/(n+2))` from `¬CWP(tₙ)` by BS3 | `¬CWP(yₙ, aₙ, …)` from BS3, then the crossing preimage (inside BS6) |

Sequence order for fixed `n` (after the H7 instruction):
1. `Hₙ` and `t₀ₙ`.
2. BS4's `Sₙ`.
3. BS2 with `ζ := min (qcanₙ/4) (1/(n+1))` and slack `1/(n+2)`. This gives `ηₙ`.
4. The bad `(yₙ, tₙ)`.

`σ` never appears at the sequence level; it lives inside the proofs of BS5 and BS6.

## 2. Exact statements (all elaborated)

Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`; opens as in
`BoundedCurvatureAtDistanceSliceTerminal.lean:8–12`; `variable {P : OrientedThreeStage.{u}} {a s : ℝ}
(G : P.IncomingSlab a s)` for BS1/BS1′/BS2 (namespace `OrientedThreeStage.IncomingSlab`).

**BS1 (candidate (a) + (b) merged; `C⁰`, fixed slab, both sides of `t₀`):**
```lean
theorem exists_forall_Icc_scalar_riemannNorm_metric_close {t₀ ζ : ℝ} (ht₀ : t₀ ∈ Ico a s)
    (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ t₀ + δ < s ∧
      ∀ t ∈ Icc (max a (t₀ - δ)) (t₀ + δ), ∀ t' ∈ Icc (max a (t₀ - δ)) (t₀ + δ),
        ∀ x : P.Carrier,
          |G.flow.scalar t x - G.flow.scalar t' x| ≤ ζ ∧
          |G.riemannNorm t x - G.riemannNorm t' x| ≤ ζ ∧
          ∀ v : TangentSpace ThreeModel x,
            (G.flow.base.metric t).inner x v v ≤ (1 + ζ) * (G.flow.base.metric t').inner x v v
```

**BS1′ (optional `C^p` form of candidate (a); not consumed by this design):**
```lean
theorem exists_forall_Icc_metricDerivNorm_le {t₀ ζ : ℝ} (ht₀ : t₀ ∈ Ico a s) (hζ : 0 < ζ)
    (p : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ t₀ + δ < s ∧
      ∀ t ∈ Icc (max a (t₀ - δ)) (t₀ + δ), ∀ x : P.Carrier, ∀ k ≤ p,
        metricDerivNorm k (G.flow.base.metric t) (G.flow.base.metric t₀)
          (G.flow.base.metric t₀) x ≤ ζ
```

**BS2 (the per-`n` packing of `ηₙ`; supplies `hsliver`, `hcurrent` on the sliver and the BS5
hypotheses). `Ioo` form; the `t₀ = a` twin replaces `hder`/`hgrad` by the slab-start bounds:**
```lean
theorem exists_sliver_data {Ctime Cgrad : ℝ≥0} {q t₀ ζ : ℝ} (hCt : 0 < Ctime) (hCg : 0 < Cgrad)
    (hq : 0 < q) (hζ : 0 < ζ) (ht₀ : t₀ ∈ Ioo a s)
    (hder : G.DerivativeBoundBefore Ctime q t₀) (hgrad : G.GradientBoundBefore Cgrad q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * q) (t₀ + η) ∧
      G.GradientBoundBefore (2 * Cgrad) (2 * q) (t₀ + η) ∧
      ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : P.Carrier,
        G.flow.scalar t x * η ≤ ζ ∧
        |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ ζ ∧
        |G.riemannNorm t x - G.riemannNorm t₀ x| ≤ ζ ∧
        ∀ v : TangentSpace ThreeModel x,
          (G.flow.base.metric t).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
          (G.flow.base.metric t₀).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t).inner x v v
```
The cap-age slack is not part of BS2. The consumer intersects BS2's `η` with `min 1 ((n+2)⁻¹ / Sₙ)`,
and all of BS2's conclusions are monotone in `η`.

**BS3 (`CapWindowPoint` time slack) and BS4 (per-history scale bound):**
```lean
theorem RetainedCoreHistory.CapWindowPoint.of_le_time {P₀ : OrientedThreeStage.{u}}
    {H : RetainedCoreHistory P₀} {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    {k : Fin (H.eventCount + 1)} {y : (H.stage k).Carrier} {σ t D θ θ' S : ℝ}
    (h : H.CapWindowPoint records k y σ D θ) (hσt : σ ≤ t)
    (hS : ∀ i b, ((records i).static b).neck.scale ≤ S)
    (hslack : S * (t - σ) ≤ θ' - θ) :
    H.CapWindowPoint records k y t D θ'

theorem RetainedCoreHistory.exists_forall_neck_scale_le {P₀ : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory P₀) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) :
    ∃ S : ℝ, 0 < S ∧ ∀ i b, ((records i).static b).neck.scale ≤ S
```
- BS3 is true: `t − τ_j ≤ (σ − τ_j) + (t − σ) ≤ θ/scale + (θ' − θ)/S ≤ θ'/scale`, since
  `scale ≤ S` and `θ ≤ θ'`.
- BS4's `b` ranges over `RetainedBoundaryIndex`, a subtype of `transition.trace.tubes.Boundary`
  (`GeometricCutoff.lean:149`).
  - First choice: a `Fintype` on that `Boundary`, in the pattern of `SphericalRegion.lean:27`
    (`finiteBoundary`). Verify it for `tubes`.
  - Fallback: the cap scalar lower bound `scale/2 ≤ R(witness cap point)` (the `hscale` of B3F), with
    the witness metric identified with the compact post-surgery stage.

**BS5 = corrected §3.2b application of B3e (candidate (c)); event slab. The terminal twin is below.**
```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event_of_sliver
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (H : RetainedCoreHistory P₀)
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ (j : Fin H.eventCount) {t₀ t : ℝ} (_ : H.time j.castSucc < t₀) (_ : t₀ ≤ t)
        (_ : t < H.time j.succ) (y : (H.stage j.castSucc).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y * t₀ →
      (∀ x, |(H.toHistory.event j).incoming.flow.scalar t x -
          (H.toHistory.event j).incoming.flow.scalar t₀ x| ≤
        (H.toHistory.event j).incoming.flow.scalar t y / 4) →
      (∀ x (v : TangentSpace ThreeModel x),
        ((H.toHistory.event j).incoming.flow.base.metric t₀).inner x v v ≤
          Real.exp 1 * ((H.toHistory.event j).incoming.flow.base.metric t).inner x v v) →
      (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1 C2 q t₀ →
      H.EventSlabsDerivative Ctime q j.castSucc →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime q t₀ →
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad q t₀ →
      H.EventSlabsPinched phi → H.NoncollapsedBefore κ ρ t₀ →
      Λ ≤ ρ * Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y) →
      ¬ H.CapWindowPoint records j.castSucc y t₀ Dcap θ →
      ∀ z ∈ riemannianBallOf ((H.toHistory.event j).incoming.flow.base.metric t) y
        (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y)),
        (H.toHistory.event j).incoming.flow.scalar t z ≤
          Q * (H.toHistory.event j).incoming.flow.scalar t y
```
Terminal twin `…_terminal_of_sliver`: the same, with `hend G hG` and `t < s` as in
`exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal` (`…SliceTerminal.lean:249`), plus
`PhiAlmostNonnegative G.flow (Ico (H.time last) s) phi` and `H.TerminalNoncollapsedBefore hend G hG κ ρ t₀`.
This form is also elaborated.

Proof of BS5 (single history; the sequence never sees `σ`):
1. Choose the constants. `(Q_B, Λ_B, Dcap, Rrad, ζ₀)` come from the event B3e
   (`…SliceEvent.lean:18`) at `(A_B, Cq_B, θ_B) := (2·√e·A, 2·Cq, θ/2)`. Output `Q := 2·Q_B + 1`
   and `Λ := 4·Λ_B`.
2. Choose `σ ∈ (max a (t₀ − δ), t₀)` with `σ ≥ t₀/2`. Here `δ` is from BS1 at
   `ζ := R(t, y)/4 ∧ (inner factor 2)`, and `S·(t₀ − σ) ≤ θ/2` with `S` from BS4.
3. At `σ`:
   - `R(σ, y) ∈ [R_t/2, 3R_t/2]`, so `q ≤ Cq_B·R(σ, y)`;
   - `Λ_B ≤ R(σ, y)·σ`;
   - `Λ_B ≤ ρ√R(σ, y)`.
4. The data at `σ` are the `…Before t₀` hypotheses restricted by `…_mono`
   (`CanonicalNeighborhoodInduction.lean:67–75`, `noncollapsedBefore_mono`).
5. `¬CWP(y, σ, Dcap, θ/2)` is the contrapositive of BS3 applied from `σ` to `t₀`.
6. Ball chain: `B_t(y, A/√R_t) ⊆ B_{t₀}(y, √e·A/√R_t) ⊆ B_σ(y, √(2e)·A/√R_t) ⊆ B_σ(y, A_B/√R_σ)`,
   by `riemannianBallOf_subset_of_inner_le_mul` (`Perelman/Noncollapsing/ForwardTransfer.lean:22`).
7. Scalar chain: `R_t(z) ≤ R_{t₀}(z) + R_t/4 ≤ R_σ(z) + R_t/2 ≤ Q_B·R_σ(y) + R_t/2 ≤ (2Q_B + 1)·R_t`.

**BS6 = Case II (`t₀ = a` an event time), across the event:**
```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (H : RetainedCoreHistory P₀)
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ (j : Fin H.eventCount) {s : ℝ}
        (Gk : (H.stage j.succ).IncomingSlab (H.time j.succ) s),
        Gk.flow.base.metric (H.time j.succ) = H.initialMetric j.succ →
      ∀ {t : ℝ} (_ : H.time j.succ < t) (_ : t < s)
        (y : (H.stage j.succ).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * Gk.flow.scalar t y → Λ ≤ Gk.flow.scalar t y →
      Λ ≤ Gk.flow.scalar t y * H.time j.succ →
      (∀ x, |Gk.flow.scalar t x - Gk.flow.scalar (H.time j.succ) x| ≤ Gk.flow.scalar t y / 4) →
      (∀ x (v : TangentSpace ThreeModel x),
        (Gk.flow.base.metric (H.time j.succ)).inner x v v ≤
          Real.exp 1 * (Gk.flow.base.metric t).inner x v v) →
      H.EventSlabsSpatiallyCanonical ε C1 C2 q j.succ →
      H.EventSlabsDerivative Ctime q j.succ → H.EventSlabsGradient Cgrad q j.succ →
      H.EventSlabsPinched phi → H.NoncollapsedBefore κ ρ (H.time j.succ) →
      Λ ≤ ρ * Real.sqrt (Gk.flow.scalar t y) →
      ¬ H.CapWindowPoint records j.succ y (H.time j.succ) Dcap θ →
      ∀ z ∈ riemannianBallOf (Gk.flow.base.metric t) y (A / Real.sqrt (Gk.flow.scalar t y)),
        Gk.flow.scalar t z ≤ Q * Gk.flow.scalar t y
```
`Gk` is generic, so this covers both the event slab and the terminal slab starting at `H.time j.succ`.
The leaf supplies `k = j'.succ` via `Fin.eq_zero_or_eq_succ`, as `SlabStartDerivativeBounds.lean:115`
does.

Proof route (to be verified by the proof lane; this is the risk):
1. **`y` is retained.** Otherwise `exists_cap_capture` gives `CWP(y, a)` at age 0 (F3). Let `y'` be
   its crossing preimage.
2. **B3e before the event.** Apply the event B3e at every `σ ∈ (a − δ, a)` in stage `j.castSucc`.
   - The inputs are `EventSlabs*` at `j.succ`, which include slab `j`, restricted by mono.
   - `¬CWP(y', σ)` comes from `¬CWP(y, a)`: prepend the crossing to the trace (a new
     10–40-line lemma) and apply BS3.
   - The constant `Q` is uniform in `σ`.
3. **Regularity.** The uniform bound and pinching give `|Rm| ≤ C·Q·R` on `B_σ(y', r)` for all
   `σ ∈ (a − δ, a)`, with the balls nested by the `e^{C·Q·R·δ}` comparison. Hence a closed ball
   around `y'` is a compact subset of `terminalRegularRegion`, by the definition at `EventData.lean:215`.
4. **Retained part of `B_a(y, r)`.** Paths that avoid the caps are pulled back isometrically
   (`oldTerminal`, `EventData.lean:321–328`) and compared with `g(σ)` by `TerminalMetricConverges`
   (`EventData.lean:231`).
5. **Caps met by the ball.**
   - The entry point on the cut sphere is retained. By step 4 it has `R ≤ 2QR`, so
     `scale ≤ C·Q·R` from the cap records (`hscale`).
   - The standard-cap window bound gives `R ≤ C·scale` on the cap.
   - Retained points reached through a cap are bounded by the rebased B3e (DESIGN_MAXWINDOW §3.1,
     second display) centred at the cut sphere.
6. **Forward.** Go from `a` to `t` with the two slice hypotheses.

**BS7 (the case `t₀ = a = 0`).** In its proof, BS1 is applied at `t₀ := 0` with `ζ := 1` and
combined with `Q₀`. The statement is a four-line specialisation, not separately probed.
```lean
-- ∀ P₀ g₀, ∃ Q₀, ∀ H (InitialIdentification) (G : (H.stage 0).IncomingSlab (H.time 0) s) hG,
--   ∃ η > 0, ∀ t ∈ Icc (H.time 0) (H.time 0 + η), ∀ y, G.flow.scalar t y ≤ Q₀ + 1
```

## 3. Suppliers, bricks, order

| Brick | Suppliers (`file:line`) | Lines |
|---|---|---|
| BS1 | `curvDerivNormSq_continuousOn` (`SlabStartSliceBounds.lean:84`; `k = 0` is `riemannNorm²`); `MetricSmoothUpTo.jointContMDiffOn` (`SlabJointSmoothness.lean:67`, Gram, hence joint continuity of `scalar` and of the inner product); compactness of `Icc × Carrier`; `metric_inner_exp_bounds_of_curvature_bound` (`Estimates/CurvatureMetricComparison.lean:19`) | 150–300 |
| BS1′ (optional) | `chartGramMatrix_joint_contMDiffOn` (`Geometry/Metric/Family/JointSmoothness.lean:77`) and the `metricDerivNorm` chart bridge used by `TerminalMetricConverges` | 200–400, skip |
| BS2 | `exists_derivativeBoundBefore_extend_of_slice` / `exists_gradientBoundBefore_extend_of_slice` (`DerivativeBoundExtension.lean:66`, `:176`); `exists_sliver_forward_comparison` (`SliverForwardComparison.lean:262`); BS1. `t₀ = a` twin: `exists_derivativeBoundBefore_extend_at_start` (`SlabStartSliceBounds.lean:288`) + `RetainedCoreHistory.exists_slice_bounds_at_slab_start` (`SlabStartDerivativeBounds.lean:94`) | 60–150 |
| BS3 | `CapWindowPoint` (`CanonicalNeighborhoodContinuationLeaves.lean:136`); pattern `CapWindowPoint.mono` (`…SliceTerminal.lean:326`) | 20–40 |
| BS4 | `RetainedBoundaryIndex` (`GeometricCutoff.lean:149`), `finiteBoundary` pattern (`SphericalRegion.lean:27`); fallback `hscale` (`…SliceTerminal.lean`, `exists_presented_cap_scalar_lower_bound_of_canonical_window_core`) | 30–80 |
| BS5 (event + terminal) | B3e event/terminal (`…SliceEvent.lean:18`, `…SliceTerminal.lean:249`); BS1, BS3, BS4; `riemannianBallOf_subset_of_inner_le_mul` (`Perelman/Noncollapsing/ForwardTransfer.lean:22`); `…Before_mono` (`CanonicalNeighborhoodInduction.lean:67–75`), `noncollapsedBefore_mono`; a `TerminalNoncollapsedBefore` mono (new, ~10 lines) | 250–450 |
| BS6 | as in its proof route; also `exists_regularCrossing_of_not_mem_capRegion` (`MetricCutCapScalarLower.lean:544`), `exists_cap_capture` (`EventCapCapture.lean:143`), `exists_window_point_of_edist_le` (`BackwardTraceDistortion.lean`), and the rebased B3e (not yet public) | 900–1600 (risk) |
| BS7 | `exists_scalar_lt_at_initial_slab_start` (`SlabStartDerivativeBounds.lean:19`), BS1 | 40–80 |
| BS8 (consumer rewiring) | DESIGN_MAXWINDOW §3.2b step 1 → BS5/BS6/BS7 case split; §3.2b step 2, §3.3 and §4.3 → B5/B7 step at `tₙ` with `hcurrent` from BS2; B6D_GLUE B12 dropped, B6B3 lemmas 3/4 fed from BS2 | 100–250 |

Order:
1. BS1, BS3 and BS4, in parallel now.
2. BS2.
3. BS5, which needs the B3F event and terminal files accepted.
4. BS7.
5. BS8, the Case I closure. It is independent of BS6.
6. BS6 last, as its own lane.

Without BS6 the leaf closes only under `t₀ₙ > aₙ` eventually. The sequence can split along a
subsequence, and both branches must close.

Total 1.6–2.9k lines, excluding BS1′.

## 4. Single-statement review prompt (BS5)

> Setting: Lean 4 / Mathlib, Ricci flow with surgery. `H : RetainedCoreHistory P₀` is a finite
> history of compact oriented 3-dimensional stages. `(H.toHistory.event j).incoming` is the smooth
> Ricci flow on the stage `j.castSucc` over `[H.time j.castSucc, H.time j.succ)`, smooth up to its
> closed start. `CapWindowPoint records k y t D θ` means that `y` traces back to a standard-cap
> window point `x` of some earlier surgery `j'`, with `‖x‖ < D + 1` and
> `t − H.time j'.succ ≤ θ·scale⁻¹`. `…Before t₀` predicates hold on the open interval `(a, t₀)` only.
> The existing theorem B3e (`exists_scalar_bound_at_distance_of_not_capWindowPoint_event`) is the
> same statement as below with `t₀ = t`, spatial witnesses on the slice `t` itself (instead of
> `SpatiallyCanonicalBefore … t₀`), `DerivativeBoundBefore/GradientBoundBefore … t`,
> `NoncollapsedBefore κ ρ t`, `Λ ≤ R(t,y)·t` and `¬ CapWindowPoint … y t Dcap θ`.
> Claim: the following corollary holds, with the proof "apply B3e at an interior slice
> `σ ∈ (a, t₀)`, `σ ↑ t₀`, chosen for this fixed history by uniform continuity of `R`, of the
> metric and of `|Rm|` on a compact time window of the slab, then transfer the ball bound from
> `σ` to `t` using the two sliver hypotheses". Please check truth, the constant bookkeeping
> (`A_B = 2√e·A`, `Cq_B = 2Cq`, `θ_B = θ/2`, `Q = 2Q_B + 1`, `Λ = 4Λ_B`), and whether any hypothesis
> is unsuppliable by a contradiction sequence in which `ηₙ` is fixed first
> (`Rₙηₙ ≤ 1/(n+1)`, `|R(t,·) − R(t₀,·)| ≤ qcanₙ/4 < Rₙ/4` on `[t₀ₙ, t₀ₙ + ηₙ]`, cap-age slack
> `Sₙηₙ ≤ 1/(n+2)`) and then the bad point `(yₙ, tₙ)` with `tₙ ∈ [t₀ₙ, t₀ₙ + ηₙ)` is picked.
>
> (the BS5 statement of §2, verbatim)
