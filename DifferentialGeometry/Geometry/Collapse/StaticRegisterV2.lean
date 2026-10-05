import DifferentialGeometry.Geometry.Collapse.StaticRegister

/-!
# The staged closed register, version 2 (chapter 14, PBR01; external review 52, R-a)

Blueprint 207B, PBR01 (B:10067–10255) with LPA04's order (207A, A:30473–30496), as decided in
external review 52, item R-a (`docs/geometrization/chapter14/out/dispositions-task52-fc39-threshold-
validity.md`): the adapter route (family built with `τ·b'`, `τ·s'`, `τ·s`, `σ_col` bound to LC09
only) is rejected; the register itself is STAGED so that every parameter of the final chapter-13
family `LocalChartPacketsC14` is a value the register records, and every producer threshold sees
exactly the values chosen before it:

`circle/collar requests → β₃, β₂ → Δ → coordinate/error choices → (τ, μ) → (b', s') → s → σ_col →
Λ → w → b → β₁ → T₀ → V → L_max → tail`.

Changes with respect to `StaticRegister.lean` (kept unchanged as history; its early data
`ClosedEarlyData`, stage block `ClosedStage`, `ClosedExclusions`, `ClosedScales` and
`ClosedSplittings` are reused verbatim):

* PR11: the collar qualities `γc, βc` of the final family are register values (TCP02–TCP04 choose
  "their circle/collar qualities", B:10131), with the producer's `βc < γc/1000` displayed.
* PR14–PR17: the coordinate/error block records the edge quality `qe` (`σc`), the slim quality `qs`
  (`σs`, EGP04's qualities bound, B:10153), the separate value error `ve` (`v_s`, B:10154), the
  distance-smoothing error `ε` and LC73's slim quality `ζ` (A:30474–30480: chosen with the slim and
  value tolerances, before `β₁`), `e₀` and the zero radial Lipschitz tolerance `ε₀` (the family's
  requested cap).
* PR18 is split into its four steps: `(τ, μ)` below `sectionUp`, which reads the coordinate block;
  `(b', s')` below LFR29.1's `W` (`lfr29W`), which reads `τ, μ` (the producer needs
  `b', s' < τΔ/10⁹`); `s` below `endpointUp`, which reads `b', s'`; and `σ_col` below `σcolUp`,
  which reads `s` (LPA04: `σ_col < min{a_*/4, a₂/4, η₁₈/4}` with `a_* = a_*(Δ, β₂, s)`, A:30486–
  30490). `σ_col` is a register value, no longer a constant slot; LC09 (`wUp`) runs with it.
* PR21: `β₁ < min{β₁Up, β₂, ζ}` (A:30496 "smaller than `β₂` and `ζ_slim`").
* PR24: the upper test range `L_max` of the family is a register value, chosen after `V` with
  `L_max > 400V` (B:10234) and above the rows' finite lower request `LmaxLow`; the common tail
  reads it.

`exists_closedRegisterV2` proves that for EVERY early data and EVERY positive threshold record one
register exists. No producer conclusion is assumed; binding the slots to the actual producers is
the validity record's obligation.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- PR11 (B:10127–10135): the early circle comparison requests, TCP03's raw requests and the
collar qualities `γc, βc` of the final family (TCP02–TCP04's "circle/collar qualities"). -/
structure ClosedCircleRequestsV2 where
  /-- SGP03's comparison request `θ_s`. -/
  θs : ℝ
  /-- EGP04's comparison request `θ_e`. -/
  θe : ℝ
  /-- TCP03's comparison request `θ₂`. -/
  θ₂ : ℝ
  /-- TCP03's circle quality `γ`. -/
  γ : ℝ
  /-- TCP03's raw reference error `E`. -/
  E : ℝ
  /-- TCP03's raw reference error `δ`. -/
  δ : ℝ
  /-- The collar quality `γc` of the final family. -/
  γc : ℝ
  /-- The collar transversality `βc` of the final family. -/
  βc : ℝ

/-- PR14–PR17 (B:10148–10160; A:30473–30481): the coordinate and error choices. -/
structure ClosedCoordErrorsV2 where
  /-- The original edge quality (`σc` of the final family). -/
  qe : ℝ
  /-- The original slim quality (`σs` of the final family). -/
  qs : ℝ
  /-- The separate value error (`v_s` of the final family, LFR19). -/
  ve : ℝ
  /-- The distance-smoothing error (`ε` of the final family). -/
  ε : ℝ
  /-- LC73's slim quality `ζ_slim` (`ζ` of the final family). -/
  ζ : ℝ
  /-- ZSP's radial error `e₀` (`e` of the final family). -/
  e₀ : ℝ
  /-- The zero radial Lipschitz tolerance `ε₀` (the requested cap of the final family). -/
  ε₀ : ℝ

/-- PR18, first step (B:10165–10167): the coarse-border and full-collar errors. -/
structure ClosedBorderV2 where
  /-- The coarse-border error `τ`. -/
  τ : ℝ
  /-- The full-collar error `μ`. -/
  μ : ℝ

/-- PR18, second step (B:10168): the weak qualities. -/
structure ClosedWeakV2 where
  /-- The weak edge quality `b'`. -/
  b' : ℝ
  /-- The weak slim quality `s'`. -/
  s' : ℝ

/-- PR14–PR18: all error choices, in their order: coordinate block, `(τ, μ)`, `(b', s')`, the
strong endpoint quality `s`, the collapsed-model error `σ_col`. -/
structure ClosedErrorsV2 where
  /-- PR14–PR17. -/
  co : ClosedCoordErrorsV2
  /-- PR18 `(τ, μ)`. -/
  bd : ClosedBorderV2
  /-- PR18 `(b', s')`. -/
  wk : ClosedWeakV2
  /-- PR18 the strong endpoint quality. -/
  s : ℝ
  /-- PR18 / LPA04 the collapsed-model error. -/
  σcol : ℝ

/-- The producer thresholds consumed by the staged closed register; every upper slot is positive
and every slot sees only earlier register values. -/
structure ClosedThresholdsV2 (D : ClosedEarlyData) where
  /-- PR10 (B:10118): CFS11–CFS12's finite `N_b`. -/
  Nb : ClosedStage D → ℝ
  Nb_nonneg : ∀ st, 0 ≤ Nb st
  /-- PR10 (B:10118): CFS11–CFS12's finite `c_w`. -/
  cw : ClosedStage D → ℝ
  cw_nonneg : ∀ st, 0 ≤ cw st
  /-- PR11 (B:10131–10135): TCP02–TCP04 circle/collar qualities and raw reference errors, TCP01
  Gram and LFR35–LFR38 anchor requests, at the fixed comparison requests. -/
  circleUp : ClosedStage D → ℝ → ℝ → ℝ → ℝ
  circleUp_pos : ∀ st θs θe θ₂, 0 < circleUp st θs θe θ₂
  /-- PR12 (B:10136): LC18's three-splitting obstruction. -/
  lc18 : ℝ
  lc18_pos : 0 < lc18
  /-- PR12 (B:10137–10138): LPA03's noncollapse-independent circle threshold and TCP02's
  compatibility threshold. -/
  β₂Up : ClosedStage D → ClosedCircleRequestsV2 → ℝ → ℝ
  β₂Up_pos : ∀ st ci β₃, 0 < β₂Up st ci β₃
  /-- PR13 (B:10139–10141): the fixed short-buffer lower bounds of TCP01–TCP04, FC22 and
  LFR35–LFR38. -/
  ΔLow : ClosedStage D → ClosedCircleRequestsV2 → ℝ → ℝ → ℝ
  /-- PR14–PR17 (B:10148–10160): original edge/slim qualities, value errors, smoothing error,
  LC73's slim quality and ZSP's radial tolerances of LFR19–LFR20, LFR27–LFR28, LFR34–LFR38,
  CGP01–CGP03, EGP04–EGP05, SGP03, TCP03–TCP04, LC67/LC73. -/
  errorsUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ℝ
  errorsUp_pos : ∀ st ci ex, 0 < errorsUp st ci ex
  /-- PR18 (B:10165–10167): original edge enclosure, full-collar and EGP05 section thresholds, at
  the coordinate block. -/
  sectionUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedCoordErrorsV2 → ℝ
  sectionUp_pos : ∀ st ci ex co, 0 < sectionUp st ci ex co
  /-- PR18 (B:10168): LFR29.1's `W`, at the coarse-border error `τ` (review 52, R-a). -/
  lfr29W : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedCoordErrorsV2 →
    ClosedBorderV2 → ℝ
  lfr29W_pos : ∀ st ci ex co bd, 0 < lfr29W st ci ex co bd
  /-- PR18 (B:10169–10170): the original endpoint thresholds, after `b', s'`. -/
  endpointUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedCoordErrorsV2 →
    ClosedBorderV2 → ClosedWeakV2 → ℝ
  endpointUp_pos : ∀ st ci ex co bd wk, 0 < endpointUp st ci ex co bd wk
  /-- PR18 (B:10172) / LPA04 (A:30486–30490): `min{a_*/4, a₂/4, η₁₈/4}` after `s`. -/
  σcolUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedCoordErrorsV2 →
    ClosedBorderV2 → ClosedWeakV2 → ℝ → ℝ
  σcolUp_pos : ∀ st ci ex co bd wk s, 0 < σcolUp st ci ex co bd wk s
  /-- PR20 (B:10200): the constant `I(1)` in `v_* = w' / (24 I(1))`. -/
  I₁ : ℝ
  I₁_pos : 0 < I₁
  /-- PR19 (B:10181–10182): support, comparison and smoothing bounds of LPA04 and the three
  producers, including TCP04's and the directional comparisons' requests. -/
  scaleUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 → ℝ
  scaleUp_pos : ∀ st ci ex er, 0 < scaleUp st ci ex er
  /-- PR20 (B:10192–10193): LC09's threshold `w_*(σ_col, Λ)` as a function of `Λ`. -/
  wUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 → ℝ → ℝ
  wUp_pos : ∀ st ci ex er Λ, 0 < wUp st ci ex er Λ
  /-- PR21 (B:10205–10208): LFR29.1, LFR28/LFR38/EGP05 at `v_*, 𝒜`, EGP03/TCP02 raw alignment and
  coverage requests, LFR44's `a_*`. -/
  splitUp : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ℝ
  splitUp_pos : ∀ st ci ex er sc, 0 < splitUp st ci ex er sc
  /-- PR21 (B:10209–10211): LFR20, LFR44's `b_{1,*}(b)`, SGP02/EGP03/TCP02, as a function of the
  strong splitting quality `b`. -/
  β₁Up : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ℝ → ℝ
  β₁Up_pos : ∀ st ci ex er sc b, 0 < β₁Up st ci ex er sc b
  /-- PR23 (B:10214–10216): LC73's reference quality, cone error, lower zero scale and every
  shell/normal-flow lower bound, after `b, β₁`. -/
  T₀Low : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ℝ → ℝ → ℝ
  /-- PR23 (B:10217–10220): LPA02's proved finite output `V ≥ T₀` (not a free choice). -/
  lpa02V : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ℝ → ℝ → ℝ → ℝ
  T₀_le_lpa02V : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ lpa02V st ci ex er sc b β₁ T₀
  /-- PR24 (B:10232–10234): the rows' finite lower request on the upper test range `L_max`. -/
  LmaxLow : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ClosedSplittings → ℝ
  /-- PR24 (B:10226–10229): the finite maximum of LPA04's and the comparison producers' uniform
  tails, at `L_max`. -/
  tailLow : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
    ClosedScales → ClosedSplittings → ℝ → ℕ
  /-- PR24 (B:10229–10230): LPA01's test radius `H_α` at sequence index `α`. -/
  H : ℕ → ℝ
  H_tendsto : Tendsto H atTop atTop

/-- PR10 (B:10120–10121): `C_ρ = 100(L₀+1)(1 + b_cut + N_b c_w / Σ₁)`. -/
def closedScaleConstantV2 (D : ClosedEarlyData) (T : ClosedThresholdsV2 D)
    (st : ClosedStage D) : ℝ :=
  100 * (D.L₀ + 1) * (1 + D.bcut + T.Nb st * T.cw st / st.Sig 0)

/-- PR20 (B:10199): `v_* = w' / (24 I(1))`. -/
def closedVStarV2 {D : ClosedEarlyData} (T : ClosedThresholdsV2 D) (sc : ClosedScales) : ℝ :=
  closedWPrime sc / (24 * T.I₁)

/-- PR10–PR28 (B:10118–10255) after the stage choices, staged as in review 52 (R-a), in the active
CAA01 reading (B:10684–10700: `β₂ < 10⁻⁶`, `b < 10⁻⁶`). -/
structure ClosedLaterV2 (D : ClosedEarlyData) (T : ClosedThresholdsV2 D) (st : ClosedStage D)
    where
  circle : ClosedCircleRequestsV2
  excl : ClosedExclusions
  err : ClosedErrorsV2
  scale : ClosedScales
  split : ClosedSplittings
  /-- PR24: the upper test range of the final family. -/
  Lmax : ℝ
  tail : ℕ
  edpβ : ℝ
  edpH : ℝ
  -- PR11 (B:10127–10135)
  θs_pos : 0 < circle.θs
  θs_lt : circle.θs < st.e 2 / (10 * D.C 2)
  θe_pos : 0 < circle.θe
  θe_lt : circle.θe < min (st.e 1 / (10 * D.C 1)) (1 / 100)
  θ₂_pos : 0 < circle.θ₂
  θ₂_lt : circle.θ₂ < st.e 0 / (100 * D.C 0 ^ 2)
  γ_pos : 0 < circle.γ
  γ_lt : circle.γ < min (circle.θ₂ ^ 2 / 10 ^ 12) (T.circleUp st circle.θs circle.θe circle.θ₂)
  E_pos : 0 < circle.E
  E_lt : circle.E < min (circle.θ₂ ^ 2 / 10 ^ 8) (T.circleUp st circle.θs circle.θe circle.θ₂)
  δ_pos : 0 < circle.δ
  δ_lt : circle.δ < min (circle.θ₂ ^ 2 / 10 ^ 8) (T.circleUp st circle.θs circle.θe circle.θ₂)
  γc_pos : 0 < circle.γc
  γc_lt : circle.γc < T.circleUp st circle.θs circle.θe circle.θ₂
  βc_pos : 0 < circle.βc
  βc_lt : circle.βc < min (circle.γc / 1000) (T.circleUp st circle.θs circle.θe circle.θ₂)
  -- PR12 (B:10136–10138) with CAA01 (B:10684, B:10690)
  β₃_pos : 0 < excl.β₃
  β₃_lt : excl.β₃ < T.lc18
  β₂_pos : 0 < excl.β₂
  β₂_lt : excl.β₂ < min (T.β₂Up st circle excl.β₃) (1 / 10 ^ 6)
  -- PR13 (B:10139–10141)
  Δ_gt : max (10 ^ 6) (max (100 / excl.β₂) (T.ΔLow st circle excl.β₃ excl.β₂)) < excl.Δ
  -- PR14–PR17 (B:10148–10160)
  qe_pos : 0 < err.co.qe
  qe_lt : err.co.qe < min (min (circle.θe ^ 2 / 10 ^ 8) (1 / (1000 * closedLongLength excl)))
    (T.errorsUp st circle excl)
  qs_pos : 0 < err.co.qs
  qs_lt : err.co.qs < min (min (circle.θe ^ 2 / 10 ^ 8) (1 / (1000 * closedLongLength excl)))
    (T.errorsUp st circle excl)
  ve_pos : 0 < err.co.ve
  ve_lt : err.co.ve < min (circle.θe / 100) (T.errorsUp st circle excl)
  ε_pos : 0 < err.co.ε
  ε_lt : err.co.ε < T.errorsUp st circle excl
  ζ_pos : 0 < err.co.ζ
  ζ_lt : err.co.ζ < T.errorsUp st circle excl
  e₀_pos : 0 < err.co.e₀
  e₀_lt : err.co.e₀ < min (1 / 1000) (T.errorsUp st circle excl)
  ε₀_pos : 0 < err.co.ε₀
  ε₀_lt : err.co.ε₀ < min (1 / 100) (T.errorsUp st circle excl)
  -- PR18 (B:10165–10172), staged (review 52, R-a)
  τ_pos : 0 < err.bd.τ
  τ_lt : err.bd.τ < min (1 / 10 ^ 8) (T.sectionUp st circle excl err.co)
  τ_Δ : 4 * err.bd.τ * excl.Δ < excl.β₂
  μ_pos : 0 < err.bd.μ
  μ_lt : err.bd.μ < min (1 / 10 ^ 8) (T.sectionUp st circle excl err.co)
  b'_pos : 0 < err.wk.b'
  b'_lt : err.wk.b' < min (T.lfr29W st circle excl err.co err.bd) (1 / 10 ^ 8)
  s'_pos : 0 < err.wk.s'
  s'_lt : err.wk.s' < min (T.lfr29W st circle excl err.co err.bd) (1 / 10 ^ 8)
  s_pos : 0 < err.s
  s_lt : err.s < min (1 / 10 ^ 5 * min err.wk.b' err.wk.s')
    (T.endpointUp st circle excl err.co err.bd err.wk)
  σcol_pos : 0 < err.σcol
  σcol_lt : err.σcol < min (T.σcolUp st circle excl err.co err.bd err.wk err.s) 1
  -- PR19 (B:10180–10190): (RegScale) and LFR29.1
  Λ_pos : 0 < scale.Λ
  Λ_lt : scale.Λ < T.scaleUp st circle excl err
  regScale_L : closedLongLength excl * scale.Λ < 1 / 10 ^ 5
  regScale_100 : 100 * excl.Δ * scale.Λ < 1 / 10 ^ 8
  regScale_Cρ : closedScaleConstantV2 D T st * excl.Δ * scale.Λ < 1 / 10 ^ 6
  regScale_e : excl.Δ * scale.Λ < st.e 0 / (1000 * D.C 0)
  regScale_two : 100 * (2 * 10 ^ 6) * excl.Δ * scale.Λ < 1
  lfr29_Λ : scale.Λ < err.wk.s' / (10 ^ 8 * excl.Δ ^ 2)
  -- PR20 (B:10192–10193): LC09 at `σ_col, Λ`
  w_pos : 0 < scale.w
  w_lt : scale.w < min (T.wUp st circle excl err scale.Λ) euclideanThreeUnitBallVolume
  -- PR21–PR23 (B:10205–10220) with CAA01 (B:10700–10704) and A:30496
  b_pos : 0 < split.b
  b_lt : split.b < min (T.splitUp st circle excl err scale) (1 / 10 ^ 6)
  β₁_pos : 0 < split.β₁
  β₁_lt : split.β₁ < min (T.β₁Up st circle excl err scale split.b) (min excl.β₂ err.co.ζ)
  T₀_ge : max (1600 * closedLongLength excl) (T.T₀Low st circle excl err scale split.b split.β₁)
    ≤ split.T₀
  V_eq : split.V = T.lpa02V st circle excl err scale split.b split.β₁ split.T₀
  -- PR24–PR25 (B:10226–10241)
  Lmax_gt : max (400 * split.V) (T.LmaxLow st circle excl err scale split) < Lmax
  tail_ge : T.tailLow st circle excl err scale split Lmax ≤ tail
  H_gt : ∀ α, tail ≤ α → 400 * split.V < T.H α
  -- PR26–PR28 (B:10247–10250)
  edpβ_pos : 0 < edpβ
  edpβ_lt : edpβ < 1 / 1000
  edpH_pos : 0 < edpH
  edpH_lt : edpH < 1 / 1000

/-- PBR01's staged register: one stage choice followed by the later choices. -/
structure ClosedRegisterV2 (D : ClosedEarlyData) (T : ClosedThresholdsV2 D) where
  stage : ClosedStage D
  later : ClosedLaterV2 D T stage

/-! ### Existence (PBR01) -/

private theorem exists_pos_lt_VAL2 {b : ℝ} (hb : 0 < b) : ∃ x, 0 < x ∧ x < b :=
  ⟨b / 2, half_pos hb, half_lt_self hb⟩

/-- PR10–PR28, staged: for every stage choice, the later choices are admissible. -/
theorem exists_closedLaterV2 (D : ClosedEarlyData) (T : ClosedThresholdsV2 D)
    (st : ClosedStage D) : Nonempty (ClosedLaterV2 D T st) := by
  have hC := D.C_pos
  have he := st.e_pos
  -- PR11
  obtain ⟨θs, hθs, hθsl⟩ := exists_pos_lt_VAL2 (show 0 < st.e 2 / (10 * D.C 2) by
    have := hC 2; have := he 2; positivity)
  obtain ⟨θe, hθe, hθel⟩ := exists_pos_lt_VAL2
    (show 0 < min (st.e 1 / (10 * D.C 1)) (1 / 100) by
      have := hC 1; have := he 1; exact lt_min (by positivity) (by norm_num))
  obtain ⟨θ₂, hθ₂, hθ₂l⟩ := exists_pos_lt_VAL2 (show 0 < st.e 0 / (100 * D.C 0 ^ 2) by
    have := hC 0; have := he 0; positivity)
  have hcu := T.circleUp_pos st θs θe θ₂
  obtain ⟨γ, hγ, hγl⟩ := exists_pos_lt_VAL2
    (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 12 by positivity) hcu)
  obtain ⟨E, hE, hEl⟩ := exists_pos_lt_VAL2 (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  obtain ⟨δ, hδ, hδl⟩ := exists_pos_lt_VAL2 (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  obtain ⟨γc, hγc, hγcl⟩ := exists_pos_lt_VAL2 hcu
  obtain ⟨βc, hβc, hβcl⟩ := exists_pos_lt_VAL2 (lt_min (show 0 < γc / 1000 by positivity) hcu)
  let ci : ClosedCircleRequestsV2 := ⟨θs, θe, θ₂, γ, E, δ, γc, βc⟩
  -- PR12–PR13
  obtain ⟨β₃, hβ₃, hβ₃l⟩ := exists_pos_lt_VAL2 T.lc18_pos
  obtain ⟨β₂, hβ₂, hβ₂l⟩ := exists_pos_lt_VAL2
    (lt_min (T.β₂Up_pos st ci β₃) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨Δ, hΔ⟩ : ∃ x, max (10 ^ 6) (max (100 / β₂) (T.ΔLow st ci β₃ β₂)) < x :=
    ⟨_, lt_add_one _⟩
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hΔ.le)
  let ex : ClosedExclusions := ⟨β₃, β₂, Δ⟩
  -- PR14–PR17
  have heu := T.errorsUp_pos st ci ex
  have hLpos : 0 < closedLongLength ex := by unfold closedLongLength; positivity
  have hqb : 0 < min (min (θe ^ 2 / 10 ^ 8) (1 / (1000 * closedLongLength ex)))
      (T.errorsUp st ci ex) :=
    lt_min (lt_min (by positivity) (by positivity)) heu
  obtain ⟨qe, hqe, hqel⟩ := exists_pos_lt_VAL2 hqb
  obtain ⟨qs, hqs, hqsl⟩ := exists_pos_lt_VAL2 hqb
  obtain ⟨ve, hve, hvel⟩ := exists_pos_lt_VAL2 (lt_min (show 0 < θe / 100 by positivity) heu)
  obtain ⟨ε, hε, hεl⟩ := exists_pos_lt_VAL2 heu
  obtain ⟨ζ, hζ, hζl⟩ := exists_pos_lt_VAL2 heu
  obtain ⟨e₀, he₀, he₀l⟩ := exists_pos_lt_VAL2
    (lt_min (show (0 : ℝ) < 1 / 1000 by norm_num) heu)
  obtain ⟨ε₀, hε₀, hε₀l⟩ := exists_pos_lt_VAL2 (lt_min (show (0 : ℝ) < 1 / 100 by norm_num) heu)
  let co : ClosedCoordErrorsV2 := ⟨qe, qs, ve, ε, ζ, e₀, ε₀⟩
  -- PR18: (τ, μ), then (b', s'), then s, then σ_col
  have hsu := T.sectionUp_pos st ci ex co
  obtain ⟨τ, hτ, hτl⟩ := exists_pos_lt_VAL2
    (lt_min (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
      (show 0 < β₂ / (4 * Δ) by positivity))
  obtain ⟨μ, hμ, hμl⟩ := exists_pos_lt_VAL2
    (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
  let bd : ClosedBorderV2 := ⟨τ, μ⟩
  have hW := T.lfr29W_pos st ci ex co bd
  obtain ⟨b', hb', hb'l⟩ := exists_pos_lt_VAL2
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  obtain ⟨s', hs', hs'l⟩ := exists_pos_lt_VAL2
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  let wk : ClosedWeakV2 := ⟨b', s'⟩
  obtain ⟨s, hs, hsl⟩ := exists_pos_lt_VAL2
    (lt_min (show 0 < 1 / 10 ^ 5 * min b' s' by have := lt_min hb' hs'; positivity)
      (T.endpointUp_pos st ci ex co bd wk))
  obtain ⟨σ, hσ, hσl⟩ := exists_pos_lt_VAL2
    (lt_min (T.σcolUp_pos st ci ex co bd wk s) one_pos)
  let er : ClosedErrorsV2 := ⟨co, bd, wk, s, σ⟩
  -- PR19 (RegScale)
  set Cρ := closedScaleConstantV2 D T st with hCρ
  have hCρpos : 0 < Cρ := by
    have := D.bcut_pos
    have := D.one_le_L₀
    have := T.Nb_nonneg st
    have := T.cw_nonneg st
    have := st.Sig_pos 0
    rw [hCρ]
    unfold closedScaleConstantV2
    positivity
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_pos_lt_VAL2 (show 0 < min (T.scaleUp st ci ex er)
      (min (1 / 10 ^ 5 / closedLongLength ex) (min (1 / 10 ^ 8 / (100 * Δ))
        (min (1 / 10 ^ 6 / (Cρ * Δ)) (min (st.e 0 / (1000 * D.C 0) / Δ)
          (min (1 / (100 * (2 * 10 ^ 6) * Δ)) (s' / (10 ^ 8 * Δ ^ 2))))))) by
    have := hC 0; have := he 0
    exact lt_min (T.scaleUp_pos st ci ex er) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  simp only [lt_min_iff] at hΛl
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7⟩ := hΛl
  -- PR20
  obtain ⟨w, hw, hwl⟩ := exists_pos_lt_VAL2 (lt_min (T.wUp_pos st ci ex er Λ)
    (show 0 < euclideanThreeUnitBallVolume by unfold euclideanThreeUnitBallVolume; positivity))
  let sc : ClosedScales := ⟨Λ, w⟩
  -- PR21–PR23
  obtain ⟨b, hb, hbl⟩ := exists_pos_lt_VAL2
    (lt_min (T.splitUp_pos st ci ex er sc) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨β₁, hβ₁, hβ₁l⟩ := exists_pos_lt_VAL2
    (lt_min (T.β₁Up_pos st ci ex er sc b) (lt_min hβ₂ hζ))
  let T₀ := max (1600 * closedLongLength ex) (T.T₀Low st ci ex er sc b β₁)
  let sp : ClosedSplittings := ⟨b, β₁, T₀, T.lpa02V st ci ex er sc b β₁ T₀⟩
  -- PR24–PR25
  let Lm := max (400 * sp.V) (T.LmaxLow st ci ex er sc sp) + 1
  obtain ⟨α₀, hα₀⟩ := (tendsto_atTop.mp T.H_tendsto (400 * sp.V + 1)).exists_forall_of_atTop
  refine ⟨{
    circle := ci, excl := ex, err := er, scale := sc, split := sp, Lmax := Lm
    tail := max (T.tailLow st ci ex er sc sp Lm) α₀
    edpβ := 1 / 2000, edpH := 1 / 2000
    θs_pos := hθs, θs_lt := hθsl, θe_pos := hθe, θe_lt := hθel, θ₂_pos := hθ₂, θ₂_lt := hθ₂l
    γ_pos := hγ, γ_lt := hγl, E_pos := hE, E_lt := hEl, δ_pos := hδ, δ_lt := hδl
    γc_pos := hγc, γc_lt := hγcl, βc_pos := hβc, βc_lt := hβcl
    β₃_pos := hβ₃, β₃_lt := hβ₃l, β₂_pos := hβ₂, β₂_lt := hβ₂l, Δ_gt := hΔ
    qe_pos := hqe, qe_lt := hqel, qs_pos := hqs, qs_lt := hqsl, ve_pos := hve, ve_lt := hvel
    ε_pos := hε, ε_lt := hεl, ζ_pos := hζ, ζ_lt := hζl
    e₀_pos := he₀, e₀_lt := he₀l, ε₀_pos := hε₀, ε₀_lt := hε₀l
    τ_pos := hτ, τ_lt := (lt_min_iff.mp hτl).1
    τ_Δ := ?_, μ_pos := hμ, μ_lt := hμl, b'_pos := hb', b'_lt := hb'l
    s'_pos := hs', s'_lt := hs'l, s_pos := hs, s_lt := hsl, σcol_pos := hσ, σcol_lt := hσl
    Λ_pos := hΛ, Λ_lt := hΛ1, regScale_L := ?_, regScale_100 := ?_, regScale_Cρ := ?_
    regScale_e := ?_, regScale_two := ?_, lfr29_Λ := hΛ7
    w_pos := hw, w_lt := hwl, b_pos := hb, b_lt := hbl, β₁_pos := hβ₁, β₁_lt := hβ₁l
    T₀_ge := le_rfl, V_eq := rfl, Lmax_gt := lt_add_one _, tail_ge := le_max_left _ _
    H_gt := ?_
    edpβ_pos := by norm_num, edpβ_lt := by norm_num
    edpH_pos := by norm_num, edpH_lt := by norm_num }⟩
  · have h := (lt_div_iff₀ (show 0 < 4 * Δ by positivity)).mp (lt_min_iff.mp hτl).2
    change 4 * τ * Δ < β₂
    calc 4 * τ * Δ = τ * (4 * Δ) := by ring
      _ < β₂ := h
  · have h := (lt_div_iff₀ hLpos).mp hΛ2
    change closedLongLength ex * Λ < 1 / 10 ^ 5
    rwa [mul_comm]
  · have h := (lt_div_iff₀ (show 0 < 100 * Δ by positivity)).mp hΛ3
    change 100 * Δ * Λ < 1 / 10 ^ 8
    rwa [mul_comm]
  · have h := (lt_div_iff₀ (show 0 < Cρ * Δ by positivity)).mp hΛ4
    change Cρ * Δ * Λ < 1 / 10 ^ 6
    rwa [mul_comm]
  · have h := (lt_div_iff₀ hΔpos).mp hΛ5
    change Δ * Λ < st.e 0 / (1000 * D.C 0)
    rwa [mul_comm]
  · have h := (lt_div_iff₀ (show 0 < 100 * (2 * 10 ^ 6) * Δ by positivity)).mp hΛ6
    change 100 * (2 * 10 ^ 6) * Δ * Λ < 1
    rwa [mul_comm]
  · intro α hα
    have := hα₀ α ((le_max_right _ _).trans hα)
    linarith

/-- **PBR01, staged** (B:10067; review 52, R-a): for every early data and every positive
producer-threshold record the staged closed register admits one assignment. -/
theorem exists_closedRegisterV2 (D : ClosedEarlyData) (T : ClosedThresholdsV2 D) :
    Nonempty (ClosedRegisterV2 D T) := by
  obtain ⟨st⟩ := exists_closedStage D
  obtain ⟨la⟩ := exists_closedLaterV2 D T st
  exact ⟨⟨st, la⟩⟩

/-! ### The parameters of the final family recorded by the register -/

namespace ClosedRegisterV2

variable {D : ClosedEarlyData} {T : ClosedThresholdsV2 D} (R : ClosedRegisterV2 D T)

/-- The splitting vector of the final family: `β 1 = β₁`, `β 2 = β₂`, `β 3 = β₃` (the register's
three splitting values; `0` at the unused indices). -/
def β (n : ℕ) : ℝ :=
  if n = 1 then R.later.split.β₁ else if n = 2 then R.later.excl.β₂
    else if n = 3 then R.later.excl.β₃ else 0

@[simp] theorem β_one_VAL2 : R.β 1 = R.later.split.β₁ := by simp [β]

@[simp] theorem β_two_VAL2 : R.β 2 = R.later.excl.β₂ := by simp [β]

@[simp] theorem β_three_VAL2 : R.β 3 = R.later.excl.β₃ := by simp [β]

end ClosedRegisterV2

/-! ### Elementary consequences used by the consumers -/

namespace ClosedLaterV2

variable {D : ClosedEarlyData} {T : ClosedThresholdsV2 D} {st : ClosedStage D}

theorem Δ_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < la.excl.Δ :=
  lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans la.Δ_gt.le)

/-- FDC01 (B:10251): `Δ > 100`. -/
theorem hundred_lt_Δ_VAL2 (la : ClosedLaterV2 D T st) : 100 < la.excl.Δ :=
  lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans la.Δ_gt.le)

/-- PR13 (B:10139): `Δ > 100 / β₂`. -/
theorem hundred_div_β₂_lt_Δ_VAL2 (la : ClosedLaterV2 D T st) : 100 / la.excl.β₂ < la.excl.Δ :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans_lt la.Δ_gt

theorem longLength_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < closedLongLength la.excl := by
  have := la.Δ_pos_VAL2
  unfold closedLongLength
  positivity

/-- FDC01 (B:10251): `θ_e < 1/100`. -/
theorem θe_lt_hundredth_VAL2 (la : ClosedLaterV2 D T st) : la.circle.θe < 1 / 100 :=
  la.θe_lt.trans_le (min_le_right _ _)

/-- CAA01 (B:10684): `β₂ < 10⁻⁶`. -/
theorem β₂_lt_audit_VAL2 (la : ClosedLaterV2 D T st) : la.excl.β₂ < 1 / 10 ^ 6 :=
  la.β₂_lt.trans_le (min_le_right _ _)

/-- CAA01 (B:10684): `b < 10⁻⁶`. -/
theorem b_lt_audit_VAL2 (la : ClosedLaterV2 D T st) : la.split.b < 1 / 10 ^ 6 :=
  la.b_lt.trans_le (min_le_right _ _)

theorem τ_lt_VAL2 (la : ClosedLaterV2 D T st) : la.err.bd.τ < 1 / 10 ^ 8 :=
  la.τ_lt.trans_le (min_le_left _ _)

theorem μ_lt_VAL2 (la : ClosedLaterV2 D T st) : la.err.bd.μ < 1 / 10 ^ 8 :=
  la.μ_lt.trans_le (min_le_left _ _)

theorem b'_lt_VAL2 (la : ClosedLaterV2 D T st) : la.err.wk.b' < 1 / 10 ^ 8 :=
  la.b'_lt.trans_le (min_le_right _ _)

theorem s'_lt_VAL2 (la : ClosedLaterV2 D T st) : la.err.wk.s' < 1 / 10 ^ 8 :=
  la.s'_lt.trans_le (min_le_right _ _)

/-- PR18 (B:10169): `s < 10⁻⁵ b'`. -/
theorem s_lt_b'_VAL2 (la : ClosedLaterV2 D T st) : la.err.s < la.err.wk.b' / 100000 := by
  have hs : la.err.s < 1 / 10 ^ 5 * min la.err.wk.b' la.err.wk.s' :=
    la.s_lt.trans_le (min_le_left _ _)
  have hm : min la.err.wk.b' la.err.wk.s' ≤ la.err.wk.b' := min_le_left _ _
  linarith

/-- PR18 (B:10169): `s < 10⁻⁵ s'`. -/
theorem s_lt_s'_VAL2 (la : ClosedLaterV2 D T st) : la.err.s < la.err.wk.s' / 100000 := by
  have hs : la.err.s < 1 / 10 ^ 5 * min la.err.wk.b' la.err.wk.s' :=
    la.s_lt.trans_le (min_le_left _ _)
  have hm : min la.err.wk.b' la.err.wk.s' ≤ la.err.wk.s' := min_le_right _ _
  linarith

/-- CAA01 (B:10697–10699): `s < 10⁻⁶` follows from `s < 10⁻⁵ min{b', s'}` and `b' < 10⁻⁸`. -/
theorem s_lt_audit_VAL2 (la : ClosedLaterV2 D T st) : la.err.s < 1 / 10 ^ 6 := by
  have := la.s_lt_b'_VAL2
  have := la.b'_lt_VAL2
  linarith

/-- CAA01 (B:10709): EGP01's four-target error `5β₂ + b + s < 7·10⁻⁶`. -/
theorem edgeError_lt_VAL2 (la : ClosedLaterV2 D T st) :
    5 * la.excl.β₂ + la.split.b + la.err.s < 7 / 10 ^ 6 := by
  have := la.β₂_lt_audit_VAL2
  have := la.b_lt_audit_VAL2
  have := la.s_lt_audit_VAL2
  linarith

/-- CAA01 (B:10709–10710): the four-target error lies within LFR29's obstruction `10⁻³`. -/
theorem edgeError_lt_obstruction_VAL2 (la : ClosedLaterV2 D T st) :
    5 * la.excl.β₂ + la.split.b + la.err.s < 1 / 1000 :=
  la.edgeError_lt_VAL2.trans (by norm_num)

/-- LPA04 (A:30486): `σ_col < 1` (LC09's range). -/
theorem σcol_lt_one_VAL2 (la : ClosedLaterV2 D T st) : la.err.σcol < 1 :=
  la.σcol_lt.trans_le (min_le_right _ _)

/-- LPA04 (A:30486–30490): `σ_col` lies below its slot, read after `s`. -/
theorem σcol_lt_up_VAL2 (la : ClosedLaterV2 D T st) :
    la.err.σcol < T.σcolUp st la.circle la.excl la.err.co la.err.bd la.err.wk la.err.s :=
  la.σcol_lt.trans_le (min_le_left _ _)

/-- PR21 (B:10210): `β₁ < β₂`. -/
theorem β₁_lt_β₂_VAL2 (la : ClosedLaterV2 D T st) : la.split.β₁ < la.excl.β₂ :=
  la.β₁_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))

/-- A:30496: `β₁ < ζ_slim`. -/
theorem β₁_lt_ζ_VAL2 (la : ClosedLaterV2 D T st) : la.split.β₁ < la.err.co.ζ :=
  la.β₁_lt.trans_le ((min_le_right _ _).trans (min_le_right _ _))

/-- PR23 (B:10215): `T₀ ≥ 1600 L`. -/
theorem longLength_le_T₀_VAL2 (la : ClosedLaterV2 D T st) :
    1600 * closedLongLength la.excl ≤ la.split.T₀ :=
  (le_max_left _ _).trans la.T₀_ge

theorem T₀_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < la.split.T₀ := by
  have := la.longLength_pos_VAL2
  have := la.longLength_le_T₀_VAL2
  linarith

/-- PR23 (B:10217): the LPA02 output satisfies `V ≥ T₀`. -/
theorem T₀_le_V_VAL2 (la : ClosedLaterV2 D T st) : la.split.T₀ ≤ la.split.V := by
  rw [la.V_eq]
  exact T.T₀_le_lpa02V _ _ _ _ _ _ _ _

/-- PR24 (B:10234, "Include H_α > 400V"): `400 V < L_max`. -/
theorem Lmax_gt_VAL2 (la : ClosedLaterV2 D T st) : 400 * la.split.V < la.Lmax :=
  (le_max_left _ _).trans_lt la.Lmax_gt

theorem Lmax_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < la.Lmax := by
  have := la.T₀_pos_VAL2
  have := la.T₀_le_V_VAL2
  have := la.Lmax_gt_VAL2
  linarith

/-- PR20 (B:10193): `w < ω₃`. -/
theorem w_lt_volume_VAL2 (la : ClosedLaterV2 D T st) :
    la.scale.w < euclideanThreeUnitBallVolume :=
  la.w_lt.trans_le (min_le_right _ _)

/-- PR20 (B:10198): `0 < w'`. -/
theorem wPrime_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < closedWPrime la.scale := by
  have := la.w_pos
  have := la.Λ_pos
  unfold closedWPrime
  positivity

/-- PR20 (B:10198): `w' < w`. -/
theorem wPrime_lt_w_VAL2 (la : ClosedLaterV2 D T st) : closedWPrime la.scale < la.scale.w := by
  have hw := la.w_pos
  have hΛ := la.Λ_pos
  have hd : 1 < 2 * (1 + 2 * la.scale.Λ⁻¹) ^ 3 := by
    have : 1 ≤ (1 + 2 * la.scale.Λ⁻¹) ^ 3 := one_le_pow₀ (by have := inv_pos.mpr hΛ; linarith)
    linarith
  unfold closedWPrime
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- PR20 (B:10199): `0 < v_*`. -/
theorem vStar_pos_VAL2 (la : ClosedLaterV2 D T st) : 0 < closedVStarV2 T la.scale := by
  have := la.wPrime_pos_VAL2
  have := T.I₁_pos
  unfold closedVStarV2
  positivity

/-- PR14 (B:10153): the slim quality is below `θ_e²/10⁸ < 1/100`. -/
theorem qs_le_hundredth_VAL2 (la : ClosedLaterV2 D T st) : la.err.co.qs ≤ 1 / 100 := by
  have h1 : la.err.co.qs < la.circle.θe ^ 2 / 10 ^ 8 :=
    la.qs_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := la.θe_lt_hundredth_VAL2
  have h3 := la.θe_pos
  have : la.circle.θe ^ 2 / 10 ^ 8 < 1 / 100 := by
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  linarith

/-- PR14 (B:10153): the edge quality is below `θ_e²/10⁸ < 1`. -/
theorem qe_lt_one_VAL2 (la : ClosedLaterV2 D T st) : la.err.co.qe < 1 := by
  have h1 : la.err.co.qe < la.circle.θe ^ 2 / 10 ^ 8 :=
    la.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := la.θe_lt_hundredth_VAL2
  have h3 := la.θe_pos
  have : la.circle.θe ^ 2 / 10 ^ 8 < 1 := by
    rw [div_lt_one (by norm_num)]
    nlinarith
  linarith

/-- ZSP (B:10158): `e₀ < 1/1000 < 1/40`. -/
theorem e₀_lt_VAL2 (la : ClosedLaterV2 D T st) : la.err.co.e₀ < 1 / 40 :=
  (la.e₀_lt.trans_le (min_le_left _ _)).trans (by norm_num)

/-- The producer's collar transversality condition `βc < γc/1000` (C14P:221). -/
theorem βc_lt_γc_VAL2 (la : ClosedLaterV2 D T st) : la.circle.βc < la.circle.γc / 1000 :=
  la.βc_lt.trans_le (min_le_left _ _)

end ClosedLaterV2

end DifferentialGeometry.Geometry.Collapse
