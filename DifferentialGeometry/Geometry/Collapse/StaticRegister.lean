import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The closed static register (chapter 14, PBR01 and CAA01)

Blueprint 207B, `prop:fibration-closed-register-admissibility` (PBR01, B:10067–10255) with the
active edge-exclusion reading of CAA01 (B:10679–10722). The register is DATA: the free real
parameters of the closed route in their dependency order, with every explicitly displayed
inequality as a field. It is indexed by

* `ClosedEarlyData`: the producer constants fixed before any choice (PR01–PR03, B:10085–10096,
  GAF01 B:5719–5734), and
* `ClosedThresholds D`: the proved positive thresholds of the named producers, each a function of
  the earlier register values only (B:10073–10075 "its proved POSITIVE threshold with the earlier
  arguments"). One slot per parameter aggregates the finitely many named producers (their finite
  minimum, as in the blueprint); every slot names its producers.

`exists_closedRegister` (PBR01) proves that for EVERY such early data and EVERY positive threshold
record one register exists. No producer conclusion is assumed; binding the slots to the actual
producers is a separate obligation.

Stage indices: `Fin 3` index `0, 1, 2` is the adjustment stage `1, 2, 3` (the same convention as
W4-GAF's GAF01 kernel). The stage block restates GAF01's (JA)/(JB) and EDP01's (SE).
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- PR01 (B:10085): the early adjustment target `c_adjust = 1/1000`. -/
def closedAdjustTolerance : ℝ := 1 / 1000

/-- PR01–PR03 (B:10085–10096; GAF01 B:5719–5743): the early constants fixed by the producers
before every free choice. `N` dominates the LPA06/SGP01/EGP02/TCP01 whole support-list counts,
`P ≥ 1` the profile derivatives, `C j` are the graph moduli of TCP05/EGP06/SGP04, `L₀ ≥ 1` is
CGP02's global derivative bound and `Ξ j` is CFS15's modulus (`ε_j = Ξ_j(Γ_j)`, tending to zero). -/
structure ClosedEarlyData where
  N : ℕ
  P : ℝ
  one_le_P : 1 ≤ P
  C : Fin 3 → ℝ
  C_pos : ∀ j, 0 < C j
  L₀ : ℝ
  one_le_L₀ : 1 ≤ L₀
  Ξ : Fin 3 → ℝ → ℝ
  Ξ_pos : ∀ j Γ, 0 < Γ → 0 < Ξ j Γ
  Ξ_tendsto : ∀ j, Tendsto (Ξ j) (𝓝[>] 0) (𝓝 0)

namespace ClosedEarlyData

variable (D : ClosedEarlyData)

/-- GAF01 (B:5722): `Ω = max{1, C₁, C₂, C₃}`. -/
def Ω : ℝ := max 1 (max (D.C 0) (max (D.C 1) (D.C 2)))

/-- GAF01 (B:5729): `b_cut = 10000 (N+1)² P⁴`. -/
def bcut : ℝ := 10000 * ((D.N : ℝ) + 1) ^ 2 * D.P ^ 4

/-- GAF01 (B:5730): `κ = 1 / (1000 (N+1) P²)`. -/
def κ : ℝ := 1 / (1000 * ((D.N : ℝ) + 1) * D.P ^ 2)

/-- GAF01 (B:5737): `α_j = min{c_j / (16(1+b_cut)(1+L₀)), 1/(16(1+L₀))}`. -/
def α (c : ℝ) : ℝ := min (c / (16 * (1 + D.bcut) * (1 + D.L₀))) (1 / (16 * (1 + D.L₀)))

theorem one_le_Ω : 1 ≤ D.Ω := le_max_left _ _

theorem Ω_pos : 0 < D.Ω := zero_lt_one.trans_le D.one_le_Ω

theorem P_pos : 0 < D.P := zero_lt_one.trans_le D.one_le_P

theorem bcut_pos : 0 < D.bcut := by
  have := D.P_pos
  unfold bcut
  positivity

theorem κ_pos : 0 < D.κ := by
  have := D.P_pos
  unfold κ
  positivity

theorem α_pos {c : ℝ} (hc : 0 < c) : 0 < D.α c := by
  have := D.bcut_pos
  have := D.one_le_L₀
  unfold α
  exact lt_min (by positivity) (by positivity)

end ClosedEarlyData

/-- GAF01 (B:5753): `t_j = min{3Σ_j/10, α_j, 1}`. -/
def stageT (α Sig : ℝ) : ℝ := min (3 * Sig / 10) (min α 1)

theorem stageT_pos {α Sig : ℝ} (hα : 0 < α) (hSig : 0 < Sig) : 0 < stageT α Sig :=
  lt_min (by positivity) (lt_min hα one_pos)

/-- The (JA)+(SE)+PR27 upper bound on `c₃` (B:5711, B:6676, B:10247), with `P₀ ≤ P` (B:10091). -/
def closedC₃Bound (D : ClosedEarlyData) : ℝ :=
  min (min closedAdjustTolerance (min (1 / 1000) (1 / 512)))
    (min (1 / 10 ^ 5) (1 / (10 ^ 5 * (D.P + 1))))

/-- The upper bound on the next stage target `c_{j-1}` (GAF01 B:5755–5757; PR04–PR09
B:10103–10104): `min{c_j, t_j, 4κ/5, 1/1000, 1/512}`. -/
def closedNextTargetBound (D : ClosedEarlyData) (c Sig : ℝ) : ℝ :=
  min c (min (stageT (D.α c) Sig) (min (4 * D.κ / 5) (min (1 / 1000) (1 / 512))))

/-- The CFS15 accuracy bound on `ε_j = Ξ_j(Γ_j)` (GAF01 B:5741–5743). -/
def closedAccuracyBound (D : ClosedEarlyData) (c : ℝ) : ℝ :=
  min (1 / 10) (min (D.α c) (1 / (1000 * (D.Ω + 1))))

/-- (RegStage)/(JB), B:10106–10111 and B:5745–5751: the bound on `Σ_j`. -/
def closedSigmaBound (D : ClosedEarlyData) (j : Fin 3) (Γ : ℝ) : ℝ :=
  min (1 / 2) (min (D.Ξ j Γ / 10000) (min (Γ / 200) (Γ ^ 3 / (100 * D.C j))))

/-- (RegStage)/(JB), B:10106–10111 and B:5745–5751: the bound on `e_j`. -/
def closedErrorBound (D : ClosedEarlyData) (Γ Sig : ℝ) : ℝ :=
  min (1 / 100) (min (Γ * Sig / 100) (min (Sig / 1000) (1 / (200 * D.Ω))))

/-- PR04–PR09 (B:10099–10116): the three reverse stage choices of GAF01. -/
structure ClosedStage (D : ClosedEarlyData) where
  c : Fin 3 → ℝ
  Γ : Fin 3 → ℝ
  Sig : Fin 3 → ℝ
  e : Fin 3 → ℝ
  c_pos : ∀ j, 0 < c j
  c₃_lt : c 2 < closedC₃Bound D
  c₂_le : c 1 ≤ closedNextTargetBound D (c 2) (Sig 2)
  c₁_le : c 0 ≤ closedNextTargetBound D (c 1) (Sig 1)
  Γ_pos : ∀ j, 0 < Γ j
  Γ_le : ∀ j, Γ j ≤ c j / 16
  Ξ_lt : ∀ j, D.Ξ j (Γ j) < closedAccuracyBound D (c j)
  Sig_pos : ∀ j, 0 < Sig j
  Sig_lt : ∀ j, Sig j < closedSigmaBound D j (Γ j)
  e_pos : ∀ j, 0 < e j
  e_lt : ∀ j, e j < closedErrorBound D (Γ j) (Sig j)

/-- PR11 (B:10127–10135): the early circle comparison requests and TCP03's raw requests. -/
structure ClosedCircleRequests where
  θs : ℝ
  θe : ℝ
  θ₂ : ℝ
  γ : ℝ
  E : ℝ
  δ : ℝ

/-- PR12–PR13 (B:10136–10146): the splitting exclusions and the long scale. -/
structure ClosedExclusions where
  β₃ : ℝ
  β₂ : ℝ
  Δ : ℝ

/-- PR14–PR18 (B:10148–10178): coordinate, border, section and endpoint errors. -/
structure ClosedErrors where
  qe : ℝ
  ve : ℝ
  e₀ : ℝ
  ε₀ : ℝ
  τ : ℝ
  μ : ℝ
  b' : ℝ
  s' : ℝ
  s : ℝ

/-- PR19–PR20 (B:10180–10203): the scale variation and the volume parameter. -/
structure ClosedScales where
  Λ : ℝ
  w : ℝ

/-- PR21–PR23 (B:10205–10224): strong splitting, splitting quality, lower zero scale and the
LPA02 output scale. -/
structure ClosedSplittings where
  b : ℝ
  β₁ : ℝ
  T₀ : ℝ
  V : ℝ

/-- The producer thresholds consumed by the closed register; every upper slot is positive and
every slot sees only earlier register values. -/
structure ClosedThresholds (D : ClosedEarlyData) where
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
  β₂Up : ClosedStage D → ClosedCircleRequests → ℝ → ℝ
  β₂Up_pos : ∀ st ci β₃, 0 < β₂Up st ci β₃
  /-- PR13 (B:10139–10141): the fixed short-buffer lower bounds of TCP01–TCP04, FC22 and
  LFR35–LFR38. -/
  ΔLow : ClosedStage D → ClosedCircleRequests → ℝ → ℝ → ℝ
  /-- PR14–PR17 (B:10148–10160): original edge/slim qualities and value errors of LFR19–LFR20,
  LFR27–LFR28, LFR34–LFR38, CGP01–CGP03, EGP04–EGP05, SGP03, TCP03–TCP04, LC67/LC73. -/
  errorsUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ℝ
  errorsUp_pos : ∀ st ci ex, 0 < errorsUp st ci ex
  /-- PR18 (B:10165–10167): original edge enclosure, full-collar and EGP05 section thresholds. -/
  sectionUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ℝ
  sectionUp_pos : ∀ st ci ex, 0 < sectionUp st ci ex
  /-- PR18 (B:10168): LFR29.1's `W`. -/
  lfr29W : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ℝ
  lfr29W_pos : ∀ st ci ex, 0 < lfr29W st ci ex
  /-- PR18 (B:10169–10170): the original endpoint thresholds. -/
  endpointUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ℝ
  endpointUp_pos : ∀ st ci ex, 0 < endpointUp st ci ex
  /-- PR18 (B:10172): LPA04's collar ratio `σ_col`. -/
  σcol : ℝ
  σcol_pos : 0 < σcol
  σcol_lt_one : σcol < 1
  /-- PR20 (B:10200): the constant `I(1)` in `v_* = w' / (24 I(1))`. -/
  I₁ : ℝ
  I₁_pos : 0 < I₁
  /-- PR19 (B:10181–10182): support, comparison and smoothing bounds of LPA04 and the three
  producers, including TCP04's and the directional comparisons' requests. -/
  scaleUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors → ℝ
  scaleUp_pos : ∀ st ci ex er, 0 < scaleUp st ci ex er
  /-- PR20 (B:10192–10193): LC09's threshold `w_*(σ_col, Λ)` as a function of `Λ`. -/
  wUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors → ℝ → ℝ
  wUp_pos : ∀ st ci ex er Λ, 0 < wUp st ci ex er Λ
  /-- PR21 (B:10205–10208): LFR29.1, LFR28/LFR38/EGP05 at `v_*, 𝒜`, EGP03/TCP02 raw alignment and
  coverage requests, LFR44's `a_*`. -/
  splitUp : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors →
    ClosedScales → ℝ
  splitUp_pos : ∀ st ci ex er sc, 0 < splitUp st ci ex er sc
  /-- PR21 (B:10209–10211): LFR20, LFR44's `b_{1,*}(b)`, SGP02/EGP03/TCP02 and the slim quality,
  as a function of the strong splitting quality `b`. -/
  β₁Up : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors →
    ClosedScales → ℝ → ℝ
  β₁Up_pos : ∀ st ci ex er sc b, 0 < β₁Up st ci ex er sc b
  /-- PR23 (B:10214–10216): LC73's reference quality, cone error, lower zero scale and every
  shell/normal-flow lower bound, after `b, β₁`. -/
  T₀Low : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors →
    ClosedScales → ℝ → ℝ → ℝ
  /-- PR23 (B:10217–10220): LPA02's proved finite output `V ≥ T₀` (not a free choice). -/
  lpa02V : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors →
    ClosedScales → ℝ → ℝ → ℝ → ℝ
  T₀_le_lpa02V : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ lpa02V st ci ex er sc b β₁ T₀
  /-- PR24 (B:10226–10229): the finite maximum of LPA04's and the comparison producers' uniform
  tails. -/
  tailLow : ClosedStage D → ClosedCircleRequests → ClosedExclusions → ClosedErrors →
    ClosedScales → ClosedSplittings → ℕ
  /-- PR24 (B:10229–10230): LPA01's test radius `H_α` at sequence index `α`. -/
  H : ℕ → ℝ
  H_tendsto : Tendsto H atTop atTop

/-- PR10 (B:10120–10121): `C_ρ = 100(L₀+1)(1 + b_cut + N_b c_w / Σ₁)`. -/
def closedScaleConstant (D : ClosedEarlyData) (T : ClosedThresholds D) (st : ClosedStage D) : ℝ :=
  100 * (D.L₀ + 1) * (1 + D.bcut + T.Nb st * T.cw st / st.Sig 0)

/-- PR13 (B:10146): `L = 10⁶ Δ`. -/
def closedLongLength (ex : ClosedExclusions) : ℝ := 10 ^ 6 * ex.Δ

/-- PR13 (B:10146): `ℓ = 10⁵ Δ`. -/
def closedShortLength (ex : ClosedExclusions) : ℝ := 10 ^ 5 * ex.Δ

/-- PR20 (B:10198): `w' = w / (2 (1 + 2Λ⁻¹)³)`. -/
def closedWPrime (sc : ClosedScales) : ℝ := sc.w / (2 * (1 + 2 * sc.Λ⁻¹) ^ 3)

/-- PR20 (B:10199): `v_* = w' / (24 I(1))`. -/
def closedVStar {D : ClosedEarlyData} (T : ClosedThresholds D) (sc : ClosedScales) : ℝ :=
  closedWPrime sc / (24 * T.I₁)

/-- PR20 (B:10200): `𝒜(R) = 2^{K+2} A'(2R+2, w')`. -/
def closedAnalyticBound (K : ℕ) (A' : ℝ → ℝ → ℝ) (sc : ClosedScales) (R : ℝ) : ℝ :=
  2 ^ (K + 2) * A' (2 * R + 2) (closedWPrime sc)

/-- PR10–PR28 (B:10118–10255) after the stage choices, in the active CAA01 reading
(B:10684–10700: `β₂ < 10⁻⁶`, `b < 10⁻⁶`). -/
structure ClosedLater (D : ClosedEarlyData) (T : ClosedThresholds D) (st : ClosedStage D) where
  circle : ClosedCircleRequests
  excl : ClosedExclusions
  err : ClosedErrors
  scale : ClosedScales
  split : ClosedSplittings
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
  -- PR12 (B:10136–10138) with CAA01 (B:10684, B:10690)
  β₃_pos : 0 < excl.β₃
  β₃_lt : excl.β₃ < T.lc18
  β₂_pos : 0 < excl.β₂
  β₂_lt : excl.β₂ < min (T.β₂Up st circle excl.β₃) (1 / 10 ^ 6)
  -- PR13 (B:10139–10141)
  Δ_gt : max (10 ^ 6) (max (100 / excl.β₂) (T.ΔLow st circle excl.β₃ excl.β₂)) < excl.Δ
  -- PR14–PR17 (B:10148–10160)
  qe_pos : 0 < err.qe
  qe_lt : err.qe < min (min (circle.θe ^ 2 / 10 ^ 8) (1 / (1000 * closedLongLength excl)))
    (T.errorsUp st circle excl)
  ve_pos : 0 < err.ve
  ve_lt : err.ve < min (circle.θe / 100) (T.errorsUp st circle excl)
  e₀_pos : 0 < err.e₀
  e₀_lt : err.e₀ < min (1 / 1000) (T.errorsUp st circle excl)
  ε₀_pos : 0 < err.ε₀
  ε₀_lt : err.ε₀ < min (1 / 100) (T.errorsUp st circle excl)
  -- PR18 (B:10165–10172)
  τ_pos : 0 < err.τ
  τ_lt : err.τ < min (1 / 10 ^ 8) (T.sectionUp st circle excl)
  τ_Δ : 4 * err.τ * excl.Δ < excl.β₂
  μ_pos : 0 < err.μ
  μ_lt : err.μ < min (1 / 10 ^ 8) (T.sectionUp st circle excl)
  b'_pos : 0 < err.b'
  b'_lt : err.b' < min (T.lfr29W st circle excl) (1 / 10 ^ 8)
  s'_pos : 0 < err.s'
  s'_lt : err.s' < min (T.lfr29W st circle excl) (1 / 10 ^ 8)
  s_pos : 0 < err.s
  s_lt : err.s < min (1 / 10 ^ 5 * min err.b' err.s') (T.endpointUp st circle excl)
  -- PR19 (B:10180–10190): (RegScale) and LFR29.1
  Λ_pos : 0 < scale.Λ
  Λ_lt : scale.Λ < T.scaleUp st circle excl err
  regScale_L : closedLongLength excl * scale.Λ < 1 / 10 ^ 5
  regScale_100 : 100 * excl.Δ * scale.Λ < 1 / 10 ^ 8
  regScale_Cρ : closedScaleConstant D T st * excl.Δ * scale.Λ < 1 / 10 ^ 6
  regScale_e : excl.Δ * scale.Λ < st.e 0 / (1000 * D.C 0)
  regScale_two : 100 * (2 * 10 ^ 6) * excl.Δ * scale.Λ < 1
  lfr29_Λ : scale.Λ < err.s' / (10 ^ 8 * excl.Δ ^ 2)
  -- PR20 (B:10192–10193)
  w_pos : 0 < scale.w
  w_lt : scale.w < min (T.wUp st circle excl err scale.Λ) euclideanThreeUnitBallVolume
  -- PR21–PR23 (B:10205–10220) with CAA01 (B:10700–10704)
  b_pos : 0 < split.b
  b_lt : split.b < min (T.splitUp st circle excl err scale) (1 / 10 ^ 6)
  β₁_pos : 0 < split.β₁
  β₁_lt : split.β₁ < min (T.β₁Up st circle excl err scale split.b) excl.β₂
  T₀_ge : max (1600 * closedLongLength excl) (T.T₀Low st circle excl err scale split.b split.β₁)
    ≤ split.T₀
  V_eq : split.V = T.lpa02V st circle excl err scale split.b split.β₁ split.T₀
  -- PR24–PR25 (B:10226–10241)
  tail_ge : T.tailLow st circle excl err scale split ≤ tail
  H_gt : ∀ α, tail ≤ α → 400 * split.V < T.H α
  -- PR26–PR28 (B:10247–10250)
  edpβ_pos : 0 < edpβ
  edpβ_lt : edpβ < 1 / 1000
  edpH_pos : 0 < edpH
  edpH_lt : edpH < 1 / 1000

/-- PBR01's register: one stage choice followed by the later choices. -/
structure ClosedRegister (D : ClosedEarlyData) (T : ClosedThresholds D) where
  stage : ClosedStage D
  later : ClosedLater D T stage

/-! ### Existence of the stage block -/

private theorem exists_pos_lt {b : ℝ} (hb : 0 < b) : ∃ x, 0 < x ∧ x < b :=
  ⟨b / 2, half_pos hb, half_lt_self hb⟩

theorem closedC₃Bound_pos (D : ClosedEarlyData) : 0 < closedC₃Bound D := by
  have := D.P_pos
  unfold closedC₃Bound closedAdjustTolerance
  exact lt_min (lt_min (by norm_num) (lt_min (by norm_num) (by norm_num)))
    (lt_min (by norm_num) (by positivity))

theorem closedNextTargetBound_pos (D : ClosedEarlyData) {c Sig : ℝ} (hc : 0 < c)
    (hSig : 0 < Sig) : 0 < closedNextTargetBound D c Sig := by
  have := D.κ_pos
  exact lt_min hc (lt_min (stageT_pos (D.α_pos hc) hSig)
    (lt_min (by positivity) (lt_min (by norm_num) (by norm_num))))

theorem closedAccuracyBound_pos (D : ClosedEarlyData) {c : ℝ} (hc : 0 < c) :
    0 < closedAccuracyBound D c := by
  have := D.Ω_pos
  exact lt_min (by norm_num) (lt_min (D.α_pos hc) (by positivity))

theorem closedSigmaBound_pos (D : ClosedEarlyData) (j : Fin 3) {Γ : ℝ} (hΓ : 0 < Γ) :
    0 < closedSigmaBound D j Γ := by
  have := D.Ξ_pos j Γ hΓ
  have := D.C_pos j
  exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

theorem closedErrorBound_pos (D : ClosedEarlyData) {Γ Sig : ℝ} (hΓ : 0 < Γ) (hSig : 0 < Sig) :
    0 < closedErrorBound D Γ Sig := by
  have := D.Ω_pos
  exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

/-- One GAF01 stage (B:5739–5754) at a fixed positive target: the CFS15 modulus tends to zero,
so `Γ` exists before `Σ` and `e`. -/
theorem exists_closed_stage_step (D : ClosedEarlyData) (j : Fin 3) {c : ℝ} (hc : 0 < c) :
    ∃ Γ Sig e : ℝ, 0 < Γ ∧ Γ ≤ c / 16 ∧ D.Ξ j Γ < closedAccuracyBound D c ∧
      0 < Sig ∧ Sig < closedSigmaBound D j Γ ∧ 0 < e ∧ e < closedErrorBound D Γ Sig := by
  have hev : ∀ᶠ Γ in 𝓝[>] (0 : ℝ), D.Ξ j Γ < closedAccuracyBound D c ∧ Γ ∈ Ioo 0 (c / 16) :=
    ((D.Ξ_tendsto j).eventually (gt_mem_nhds (closedAccuracyBound_pos D hc))).and
      (Ioo_mem_nhdsGT (by positivity))
  obtain ⟨Γ, hΞ, hΓ⟩ := hev.exists
  obtain ⟨Sig, hSig, hSigl⟩ := exists_pos_lt (closedSigmaBound_pos D j hΓ.1)
  obtain ⟨e, he, hel⟩ := exists_pos_lt (closedErrorBound_pos D hΓ.1 hSig)
  exact ⟨Γ, Sig, e, hΓ.1, hΓ.2.le, hΞ, hSig, hSigl, he, hel⟩

/-- PR04–PR09: the stage block is admissible (GAF01's reverse order: `c₃`, stage three, `c₂`,
stage two, `c₁`, stage one). -/
theorem exists_closedStage (D : ClosedEarlyData) : Nonempty (ClosedStage D) := by
  obtain ⟨c₃, hc₃, hc₃l⟩ := exists_pos_lt (closedC₃Bound_pos D)
  obtain ⟨Γ₃, S₃, e₃, hΓ₃, hΓ₃c, hΞ₃, hS₃, hS₃l, he₃, he₃l⟩ := exists_closed_stage_step D 2 hc₃
  have hc₂ := closedNextTargetBound_pos D hc₃ hS₃
  obtain ⟨Γ₂, S₂, e₂, hΓ₂, hΓ₂c, hΞ₂, hS₂, hS₂l, he₂, he₂l⟩ := exists_closed_stage_step D 1 hc₂
  have hc₁ := closedNextTargetBound_pos D hc₂ hS₂
  obtain ⟨Γ₁, S₁, e₁, hΓ₁, hΓ₁c, hΞ₁, hS₁, hS₁l, he₁, he₁l⟩ := exists_closed_stage_step D 0 hc₁
  refine ⟨{
    c := ![closedNextTargetBound D (closedNextTargetBound D c₃ S₃) S₂,
      closedNextTargetBound D c₃ S₃, c₃]
    Γ := ![Γ₁, Γ₂, Γ₃]
    Sig := ![S₁, S₂, S₃]
    e := ![e₁, e₂, e₃]
    c_pos := ?_, c₃_lt := hc₃l, c₂_le := le_rfl, c₁_le := le_rfl
    Γ_pos := ?_, Γ_le := ?_, Ξ_lt := ?_, Sig_pos := ?_, Sig_lt := ?_, e_pos := ?_, e_lt := ?_ }⟩
  all_goals intro j; fin_cases j <;> simpa

/-! ### Existence of the later block -/

private theorem exists_gt_max (a : ℝ) : ∃ x, a < x := ⟨a + 1, lt_add_one a⟩

/-- PR10–PR28: for every stage choice, the later choices are admissible. -/
theorem exists_closedLater (D : ClosedEarlyData) (T : ClosedThresholds D) (st : ClosedStage D) :
    Nonempty (ClosedLater D T st) := by
  have hC := D.C_pos
  have he := st.e_pos
  -- PR11
  obtain ⟨θs, hθs, hθsl⟩ := exists_pos_lt (show 0 < st.e 2 / (10 * D.C 2) by
    have := hC 2; have := he 2; positivity)
  obtain ⟨θe, hθe, hθel⟩ := exists_pos_lt (show 0 < min (st.e 1 / (10 * D.C 1)) (1 / 100) by
    have := hC 1; have := he 1; exact lt_min (by positivity) (by norm_num))
  obtain ⟨θ₂, hθ₂, hθ₂l⟩ := exists_pos_lt (show 0 < st.e 0 / (100 * D.C 0 ^ 2) by
    have := hC 0; have := he 0; positivity)
  have hcu := T.circleUp_pos st θs θe θ₂
  obtain ⟨γ, hγ, hγl⟩ := exists_pos_lt (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 12 by positivity) hcu)
  obtain ⟨E, hE, hEl⟩ := exists_pos_lt (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  obtain ⟨δ, hδ, hδl⟩ := exists_pos_lt (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  let ci : ClosedCircleRequests := ⟨θs, θe, θ₂, γ, E, δ⟩
  -- PR12–PR13
  obtain ⟨β₃, hβ₃, hβ₃l⟩ := exists_pos_lt T.lc18_pos
  obtain ⟨β₂, hβ₂, hβ₂l⟩ := exists_pos_lt
    (lt_min (T.β₂Up_pos st ci β₃) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨Δ, hΔ⟩ := exists_gt_max (max (10 ^ 6) (max (100 / β₂) (T.ΔLow st ci β₃ β₂)))
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hΔ.le)
  let ex : ClosedExclusions := ⟨β₃, β₂, Δ⟩
  -- PR14–PR18
  have heu := T.errorsUp_pos st ci ex
  have hsu := T.sectionUp_pos st ci ex
  have hLpos : 0 < closedLongLength ex := by unfold closedLongLength; positivity
  obtain ⟨qe, hqe, hqel⟩ := exists_pos_lt
    (lt_min (lt_min (show 0 < θe ^ 2 / 10 ^ 8 by positivity)
      (show 0 < 1 / (1000 * closedLongLength ex) by positivity)) heu)
  obtain ⟨ve, hve, hvel⟩ := exists_pos_lt (lt_min (show 0 < θe / 100 by positivity) heu)
  obtain ⟨e₀, he₀, he₀l⟩ := exists_pos_lt (lt_min (show (0 : ℝ) < 1 / 1000 by norm_num) heu)
  obtain ⟨ε₀, hε₀, hε₀l⟩ := exists_pos_lt (lt_min (show (0 : ℝ) < 1 / 100 by norm_num) heu)
  obtain ⟨τ, hτ, hτl⟩ := exists_pos_lt
    (lt_min (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
      (show 0 < β₂ / (4 * Δ) by positivity))
  obtain ⟨μ, hμ, hμl⟩ := exists_pos_lt (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
  have hW := T.lfr29W_pos st ci ex
  obtain ⟨b', hb', hb'l⟩ := exists_pos_lt (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  obtain ⟨s', hs', hs'l⟩ := exists_pos_lt (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  obtain ⟨s, hs, hsl⟩ := exists_pos_lt
    (lt_min (show 0 < 1 / 10 ^ 5 * min b' s' by have := lt_min hb' hs'; positivity)
      (T.endpointUp_pos st ci ex))
  let er : ClosedErrors := ⟨qe, ve, e₀, ε₀, τ, μ, b', s', s⟩
  -- PR19 (RegScale)
  set Cρ := closedScaleConstant D T st with hCρ
  have hCρpos : 0 < Cρ := by
    have := D.bcut_pos
    have := D.one_le_L₀
    have := T.Nb_nonneg st
    have := T.cw_nonneg st
    have := st.Sig_pos 0
    rw [hCρ]
    unfold closedScaleConstant
    positivity
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_pos_lt (show 0 < min (T.scaleUp st ci ex er)
      (min (1 / 10 ^ 5 / closedLongLength ex) (min (1 / 10 ^ 8 / (100 * Δ))
        (min (1 / 10 ^ 6 / (Cρ * Δ)) (min (st.e 0 / (1000 * D.C 0) / Δ)
          (min (1 / (100 * (2 * 10 ^ 6) * Δ)) (s' / (10 ^ 8 * Δ ^ 2))))))) by
    have := hC 0; have := he 0
    exact lt_min (T.scaleUp_pos st ci ex er) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  simp only [lt_min_iff] at hΛl
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7⟩ := hΛl
  -- PR20
  obtain ⟨w, hw, hwl⟩ := exists_pos_lt (lt_min (T.wUp_pos st ci ex er Λ)
    (show 0 < euclideanThreeUnitBallVolume by unfold euclideanThreeUnitBallVolume; positivity))
  let sc : ClosedScales := ⟨Λ, w⟩
  -- PR21–PR23
  obtain ⟨b, hb, hbl⟩ := exists_pos_lt
    (lt_min (T.splitUp_pos st ci ex er sc) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨β₁, hβ₁, hβ₁l⟩ := exists_pos_lt (lt_min (T.β₁Up_pos st ci ex er sc b) hβ₂)
  let T₀ := max (1600 * closedLongLength ex) (T.T₀Low st ci ex er sc b β₁)
  let sp : ClosedSplittings := ⟨b, β₁, T₀, T.lpa02V st ci ex er sc b β₁ T₀⟩
  -- PR24–PR25
  obtain ⟨α₀, hα₀⟩ := (tendsto_atTop.mp T.H_tendsto (400 * sp.V + 1)).exists_forall_of_atTop
  refine ⟨{
    circle := ci, excl := ex, err := er, scale := sc, split := sp
    tail := max (T.tailLow st ci ex er sc sp) α₀
    edpβ := 1 / 2000, edpH := 1 / 2000
    θs_pos := hθs, θs_lt := hθsl, θe_pos := hθe, θe_lt := hθel, θ₂_pos := hθ₂, θ₂_lt := hθ₂l
    γ_pos := hγ, γ_lt := hγl, E_pos := hE, E_lt := hEl, δ_pos := hδ, δ_lt := hδl
    β₃_pos := hβ₃, β₃_lt := hβ₃l, β₂_pos := hβ₂, β₂_lt := hβ₂l, Δ_gt := hΔ
    qe_pos := hqe, qe_lt := hqel, ve_pos := hve, ve_lt := hvel, e₀_pos := he₀, e₀_lt := he₀l
    ε₀_pos := hε₀, ε₀_lt := hε₀l, τ_pos := hτ, τ_lt := (lt_min_iff.mp hτl).1
    τ_Δ := ?_, μ_pos := hμ, μ_lt := hμl, b'_pos := hb', b'_lt := hb'l
    s'_pos := hs', s'_lt := hs'l, s_pos := hs, s_lt := hsl
    Λ_pos := hΛ, Λ_lt := hΛ1, regScale_L := ?_, regScale_100 := ?_, regScale_Cρ := ?_
    regScale_e := ?_, regScale_two := ?_, lfr29_Λ := hΛ7
    w_pos := hw, w_lt := hwl, b_pos := hb, b_lt := hbl, β₁_pos := hβ₁, β₁_lt := hβ₁l
    T₀_ge := le_rfl, V_eq := rfl, tail_ge := le_max_left _ _
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

/-- **PBR01** (B:10067): for every early data and every positive producer-threshold record the
closed register admits one assignment. -/
theorem exists_closedRegister (D : ClosedEarlyData) (T : ClosedThresholds D) :
    Nonempty (ClosedRegister D T) := by
  obtain ⟨st⟩ := exists_closedStage D
  obtain ⟨la⟩ := exists_closedLater D T st
  exact ⟨⟨st, la⟩⟩


/-! ### Elementary consequences used by the consumers -/

/-- PR27 (B:10247): `c₃ < 10⁻⁵`. -/
theorem ClosedStage.c₃_lt_audit {D : ClosedEarlyData} (st : ClosedStage D) : st.c 2 < 1 / 10 ^ 5 :=
  st.c₃_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))

/-- (JA) (B:5711): `c₃ < c_adjust`. -/
theorem ClosedStage.c₃_lt_adjust {D : ClosedEarlyData} (st : ClosedStage D) :
    st.c 2 < closedAdjustTolerance :=
  st.c₃_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))

/-- (JB) (B:5745): `Σ_j < ε_j / 10000`, with `ε_j = Ξ_j(Γ_j)`. -/
theorem ClosedStage.Sig_lt_accuracy {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) :
    st.Sig j < D.Ξ j (st.Γ j) / 10000 :=
  (st.Sig_lt j).trans_le ((min_le_right _ _).trans (min_le_left _ _))

namespace ClosedLater

variable {D : ClosedEarlyData} {T : ClosedThresholds D} {st : ClosedStage D}

theorem Δ_pos (la : ClosedLater D T st) : 0 < la.excl.Δ :=
  lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans la.Δ_gt.le)

/-- FDC01 (B:10251): `Δ > 100`. -/
theorem hundred_lt_Δ (la : ClosedLater D T st) : 100 < la.excl.Δ :=
  lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans la.Δ_gt.le)

/-- PR13 (B:10139): `Δ > 100 / β₂`. -/
theorem hundred_div_β₂_lt_Δ (la : ClosedLater D T st) : 100 / la.excl.β₂ < la.excl.Δ :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans_lt la.Δ_gt

/-- FDC01 (B:10251): `θ_e < 1/100`. -/
theorem θe_lt_hundredth (la : ClosedLater D T st) : la.circle.θe < 1 / 100 :=
  la.θe_lt.trans_le (min_le_right _ _)

/-- CAA01 (B:10684): `β₂ < 10⁻⁶`. -/
theorem β₂_lt_audit (la : ClosedLater D T st) : la.excl.β₂ < 1 / 10 ^ 6 :=
  la.β₂_lt.trans_le (min_le_right _ _)

/-- CAA01 (B:10684): `b < 10⁻⁶`. -/
theorem b_lt_audit (la : ClosedLater D T st) : la.split.b < 1 / 10 ^ 6 :=
  la.b_lt.trans_le (min_le_right _ _)

/-- CAA01 (B:10697–10699): `s < 10⁻⁶` follows from `s < 10⁻⁵ min{b', s'}` and `b' < 10⁻⁸`. -/
theorem s_lt_audit (la : ClosedLater D T st) : la.err.s < 1 / 10 ^ 6 := by
  have h1 := la.s_lt.trans_le (min_le_left _ _)
  have h2 : min la.err.b' la.err.s' < 1 / 10 ^ 8 :=
    (min_le_left _ _).trans_lt (la.b'_lt.trans_le (min_le_right _ _))
  have h3 : 0 ≤ min la.err.b' la.err.s' := (lt_min la.b'_pos la.s'_pos).le
  nlinarith

/-- CAA01 (B:10709): EGP01's four-target error `5β₂ + b + s < 7·10⁻⁶`. -/
theorem edgeError_lt (la : ClosedLater D T st) :
    5 * la.excl.β₂ + la.split.b + la.err.s < 7 / 10 ^ 6 := by
  have := la.β₂_lt_audit
  have := la.b_lt_audit
  have := la.s_lt_audit
  linarith

/-- CAA01 (B:10709–10710): the four-target error lies within LFR29's obstruction `10⁻³`. -/
theorem edgeError_lt_obstruction (la : ClosedLater D T st) :
    5 * la.excl.β₂ + la.split.b + la.err.s < 1 / 1000 :=
  la.edgeError_lt.trans (by norm_num)

/-- PR21 (B:10210): `β₁ < β₂`. -/
theorem β₁_lt_β₂ (la : ClosedLater D T st) : la.split.β₁ < la.excl.β₂ :=
  la.β₁_lt.trans_le (min_le_right _ _)

/-- PR23 (B:10215): `T₀ ≥ 1600 L`. -/
theorem longLength_le_T₀ (la : ClosedLater D T st) :
    1600 * closedLongLength la.excl ≤ la.split.T₀ :=
  (le_max_left _ _).trans la.T₀_ge

/-- PR23 (B:10217): the LPA02 output satisfies `V ≥ T₀`. -/
theorem T₀_le_V (la : ClosedLater D T st) : la.split.T₀ ≤ la.split.V := by
  rw [la.V_eq]
  exact T.T₀_le_lpa02V _ _ _ _ _ _ _ _

/-- PR20 (B:10193): `w < ω₃`. -/
theorem w_lt_volume (la : ClosedLater D T st) : la.scale.w < euclideanThreeUnitBallVolume :=
  la.w_lt.trans_le (min_le_right _ _)

/-- PR20 (B:10198): `0 < w'`. -/
theorem wPrime_pos (la : ClosedLater D T st) : 0 < closedWPrime la.scale := by
  have := la.w_pos
  have := la.Λ_pos
  unfold closedWPrime
  positivity

/-- PR20 (B:10198): `w' < w`. -/
theorem wPrime_lt_w (la : ClosedLater D T st) : closedWPrime la.scale < la.scale.w := by
  have hw := la.w_pos
  have hΛ := la.Λ_pos
  have hd : 1 < 2 * (1 + 2 * la.scale.Λ⁻¹) ^ 3 := by
    have : 1 ≤ (1 + 2 * la.scale.Λ⁻¹) ^ 3 := one_le_pow₀ (by have := inv_pos.mpr hΛ; linarith)
    linarith
  unfold closedWPrime
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- PR20 (B:10199): `0 < v_*`. -/
theorem vStar_pos (la : ClosedLater D T st) : 0 < closedVStar T la.scale := by
  have := la.wPrime_pos
  have := T.I₁_pos
  unfold closedVStar
  positivity

/-- PR19 (B:10186): `C_ρ Δ Λ < 10⁻⁶` (EDP01's (SE) bound on the adjusted scale). -/
theorem scaleConstant_mul_lt (la : ClosedLater D T st) :
    closedScaleConstant D T st * la.excl.Δ * la.scale.Λ < 1 / 10 ^ 6 :=
  la.regScale_Cρ

end ClosedLater

/-- **CAA01** (B:10679): the refined closed assignment exists, and EGP01's four-target error is
below `7·10⁻⁶ < 10⁻³`. -/
theorem exists_closedRegister_edgeError_lt (D : ClosedEarlyData) (T : ClosedThresholds D) :
    ∃ R : ClosedRegister D T,
      5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 7 / 10 ^ 6 ∧
        5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 1 / 1000 := by
  obtain ⟨R⟩ := exists_closedRegister D T
  exact ⟨R, R.later.edgeError_lt, R.later.edgeError_lt_obstruction⟩

end DifferentialGeometry.Geometry.Collapse
