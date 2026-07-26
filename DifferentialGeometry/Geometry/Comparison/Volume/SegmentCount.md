# SegmentCount.lean — B6 counting core (A0′ lane)

Brick **B6** of `HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`: the member-level
`ballMult` counting theorem, consuming `segBall_vol_rel` + `segBall_vol_fin`
(SegmentPolar) as stated, adding **no `sorry`**.

## Public API (for B7)

- `segImult (n : ℕ) (q r0 m : ℝ) : ℕ` — `⌈e^{8q(n-1)r0}(16m+8)ⁿ⌉ + 1`.  Pure
  ℝ/ℕ function; depends only on dimension `n`, Ricci scale `q`, cap `r0`, ratio
  `m`.  Not on member/point/radius/centers.
- `le_segImult` : `e^{8q(n-1)r0}(16m+8)ⁿ ≤ (segImult n q r0 m : ℝ)`.
- `one_le_segImult` : `1 ≤ segImult n q r0 m`.
- `segBall_card` (main): for a member with `RicciBoundedBelow g (-((finrank-1)q²))`,
  `0 ≤ q`, `0 < r`, `m*r ≤ r0`, `0 < r0`, a finite family `centers : α → M`
  with edist-separation `i ≠ j → ofReal r ≤ riemannianEDist I (centers i)(centers j)`,
  `z : M`, `J : Finset α` with `j ∈ J → riemannianEDist I (centers j) z ≤ ofReal (m*r)`,
  concludes `J.card ≤ segImult (finrank ℝ E) q r0 m`.  Stated entirely in
  `riemannianEDist`/`ENNReal.ofReal` terms (B7 converts supplied `dist` via
  `RealizesEdist.edist_eq` + `dist_nonneg`).
- Reusable model-volume + edist-ball helpers: `hypRadVol_le`, `hypRadVol_ge`,
  `hypRadVol_ratio_le`, `hypSn_le_mul_exp`, `hypSn_ge_self`, `hypDen_le`,
  `sinh_le_mul_exp`, `edistBall_open/_mono/_shift/_disj`.

## Route that worked

- **Ball type.** Members carry only `[PseudoEMetricSpace M]`; there is NO
  real-distance `PseudoMetricSpace` (the project's real distance is
  `(riemannianEDist I x y).toReal`, MinimizingGeodesic.lean:2199).  So the
  `Metric.ball`-specific Packing lemmas (`balls_disjoint`, `balls_subset_ball`,
  `ball_card_le_of_vol`) do NOT apply.  Route instead through the type-agnostic
  `mul_lower_le_upper` + `card_le_of_mul_lt` (Packing.lean) using raw
  `riemannianEDist`-balls `{y | riemannianEDist I c y < ofReal ρ}`, with local
  edist-ball disjoint/subset/open helpers (triangle + `riemannianEDist_comm`).
- **Positivity of the big ball around `z`** via `IsOpenPosMeasure` of
  `riemannianVolumeMeasure` (`riemannianVolumeMeasure_isOpenPosMeasure`, needs
  only `T2 + SigmaCompact`, NOT `CompactSpace`), + finiteness from
  `segBall_vol_fin`.  Copied the openness idiom from `SmallBall.edist_vol_pos`
  but WITHOUT `CompactSpace` (members lack it) and with `riemannianEDist I`
  (not `riemannianEDistOf g`).
- **The `r`-independent model ratio** `v(R')/v(s)`.  Elementary, no closed-form
  integral: `hypSn q τ ≥ τ` (`Real.self_le_sinh_iff`) and `hypSn q τ ≤ τ e^{qτ}`
  (from `sinh x ≤ x eˣ`, itself `e^{2x}(1-2x) ≤ 1` ⇐ `Real.add_one_le_exp(-2x)`),
  then a CONSTANT upper bound on `[0,R']` and a CONSTANT lower bound on the
  subinterval `[s/2,s]`, integrated by `intervalIntegral.integral_const`.  Gives
  `v(R') ≤ R'^{d+1}e^{qdR'}`, `v(s) ≥ (s/2)^{d+1}`, hence
  `v(R') ≤ e^{qdR'}(R'/(s/2))^{d+1} v(s)`.  With `s=r/2`, `R'=(4m+2)r`:
  `R'/(s/2)=16m+8`, `qdR' ≤ 8q(n-1)r0` (cap `(4m+2)r ≤ 8r0` from `m≥1/2, mr≤r0`).
- **Packing.**  `L := U·v(s)/v(R')` (uniform per-ball lower mass, `U=(μ(bigball)).toReal`);
  `mul_lower_le_upper` gives `card·L ≤ U`; `card_le_of_mul_lt` with
  `v(R') ≤ segImult·v(s) < (segImult+1)·v(s)` closes `card ≤ segImult`.
- **Degenerate `m < 1/2`** handled first: two centers give
  `r ≤ d(cᵢ,cⱼ) ≤ 2mr < r`, so `card ≤ 1 ≤ segImult`.

## What failed / detours (durable)

- **`integral_pow` / FTC unavailable.**  `Mathlib.Analysis.SpecialFunctions.Integrals`
  AND `MeasureTheory.Integral.FundThmCalculus` oleans are NOT built in this
  checkout (the project only ever needs interval-integral *monotonicity*, never
  closed forms).  So no `∫ t^d = R^{d+1}/(d+1)` and no
  `integral_eq_sub_of_hasDerivAt`.  Rerouted to `integral_const` +
  `integral_mono_on` + `integral_add_adjacent_intervals` + `integral_nonneg`
  (all in the built `IntervalIntegral`), at the cost of a factor-2 cruder
  constant (`16m+8` vs `8m+4`) — irrelevant to the counting bound.
- **Norm-instance diamond.**  `riemannianEDist` is parameterized by the tangent
  ENorm.  The counting theorem (and SegmentPolar) elaborate under
  `attribute [-instance] Tensor0SBundle.tangentSpace_normed{AddCommGroup,Space}`
  (→ Riemannian norm); the edist-ball helpers must use the SAME instance or
  `riemannianEDist` terms mismatch (`instNormedAddCommGroupOfRiemannianBundle…`
  vs `Tensor0SBundle.tangentSpace_normedAddCommGroup`).  Fix: file-scoped bare
  `attribute [-instance] …` after the local `borel` instances, covering all
  geometric declarations.
- **`MeasurableSpace M` must be `borel M`.**  `riemannianVolumeMeasure` pins
  `borel M` internally (Invariance.lean:69).  Declare the matching
  `private local instance : MeasurableSpace M := borel M` (+ `BorelSpace M`) so
  `mul_lower_le_upper`'s `[MeasurableSpace M]` unifies.
- Small elaboration nits: `IsLocallyFiniteMeasure ?m` when
  `integral_add_adjacent_intervals` had no expected type (give `hsplit` an
  explicit type to pin `μ = volume`); `add_le_add_right` orientation surprise on
  ℝ≥0∞ (use `gcongr`); eager `le_of_eq (by ring)` inside `.trans` runs before the
  target radius is unified (bind it as an explicit `have hle` first); `lt_or_le`
  not the current name (`by_cases … ; rw [not_lt]`).
- Dropped `[Fintype α] [DecidableEq α]`: the Packing chain needs neither
  (`unusedFintype/DecidableInType` linter).  B7 has them in scope when it calls
  `segBall_card`, so mirroring stays mechanical.

## Verification

Focused check GREEN, sorry-free, warning-clean.  Targeted build of
`+…Volume.SegmentCount` GREEN; only `sorry`s in the import chain are the two
intended SegmentPolar frontiers.  No new axioms/classes/instances/notation;
consumers untouched.
