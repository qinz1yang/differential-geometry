import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4

/-!
# Register V4: the fixed total order and the `β₂` merge check (lane FC39-V4C; review 57)

**The total order of the closed register** (external review 57, §3.1, adopted by the dispositions
of task 57, item 3; it extends the order written in `StaticRegisterV4.lean`'s header, which is not
edited):

`K`, profiles, `N, P, C_j, L₀, Ξ_j`
→ `(c₃, Γ₃, Σ₃, e₃)` → `(c₂, Γ₂, Σ₂, e₂)` → `(c₁, Γ₁, Σ₁, e₁)`
→ `N_b, c_w, C_ρ`
→ `β₃`
→ `θ_s, θ_e, θ₂`
→ `γ, E, δ_raw, γ_c`
→ `β₂`
→ `β_c`
→ the producer values reading these (`σ₀, Δ₀`) → `Δ`, `L = 10⁶Δ`
→ `q_e, q_s, v_e, v_s, ε, ζ, e₀, ε₀`
→ `τ, μ` → `b', s'` → `s` → `σ_col` → `Λ` → `w, w', v_*, 𝒜`
→ `b` → `β₁` → `ε_r, δ'_cone, Λ_z` (producer prefix OUTPUTS) → `T₀`
→ `(V, δ_cone)` (producer OUTPUTS of ONE LPA02 call) → `L_max` → common tail
→ one actual family, smoothing, graphs and adjustment chain
→ compact restrictions, endpoint choices and exact face assembly on those objects.

In register V4 the slots are: `circleUp` (PR11, reads `β₃, θ_s, θ_e, θ₂`), the circle prefix
`ClosedCirclePrefixV4` (`θ_s, θ_e, θ₂, γ, E, δ = δ_raw, γ_c`), `β₂Up` (reads the prefix and
`β₃` only), then `β_c < min (min (γ_c/1000) circleUp) (β₂/3)`, then `ΔLow` and the later slots.
`ε_r, δ'_cone, Λ_z` are the prefix witness functions of the validity record (`ClosedFamilyAtV4`),
`δ_cone < δ'_cone` and `V = lpa02V …` come from the same LPA02 call (realization).

**The `β₂` merge check** (review 57, §2.3: "all `β₂` upper bounds are merged before `β₂` is
reserved and `β_c` is chosen"). In register V4 the only display with `β₂` on the SMALL side is
`β₂_lt : β₂ < min (β₂Up st prefix β₃) 10⁻⁶`; every other display containing `β₂` has it on the
large side (`βc_lt`: `β_c < β₂/3`; `Δ_gt`: `100/β₂ < Δ`; `τ_Δ`: `4τΔ < β₂`; `β₁_lt`: `β₁ < β₂`).
This file proves it as a statement about EVERY threshold record `T` (hence about every strategy,
cap, finite meet or refinement, whatever its later slots read):

* `ClosedLaterV4.exists_rechoose_β₂_V4C`: for every later choice `la₀` and every `β₂'` with
  `0 < β₂' < min (β₂Up st la₀.prefix la₀.β₃) 10⁻⁶` there is a later choice with the same `β₃`,
  the same circle prefix and `β₂ = β₂'` (all later values, `β_c` included, re-chosen);
* `ClosedLaterV4.β₂_realized_iff_V4C`: the `β₂` values realized over a fixed `(st, β₃, prefix)`
  are EXACTLY the pre-`β_c` interval `(0, min (β₂Up st prefix β₃) 10⁻⁶)`;
* `ClosedLaterV4.β₂_bound_eq_of_prefix_V4C`: two later choices with the same `β₃` and prefix have
  the same `β₂` bound (it does not read `β_c`).

So no slot chosen after `β₂` — in particular no request a strategy places on `β_c` or later —
can lower the admissible `β₂`; a `β₂` request must sit in `β₂Up`, which reads only
`ClosedCirclePrefixV4` and `β₃` by its type.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

private theorem exists_pos_lt_V4C {b : ℝ} (hb : 0 < b) : ∃ x, 0 < x ∧ x < b :=
  ⟨b / 2, half_pos hb, half_lt_self hb⟩

namespace ClosedLaterV4

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} {st : ClosedStage D}

/-- **`β₂` re-choice (review 57, §2.3)**: over a fixed stage, `β₃` and circle prefix, every `β₂'`
below the pre-`β_c` bound `min (β₂Up st prefix β₃) 10⁻⁶` extends to a complete later choice (the
collar tolerance `β_c` and every later value re-chosen). For EVERY threshold record `T`. -/
theorem exists_rechoose_β₂_V4C (la₀ : ClosedLaterV4 D T st) {β₂ : ℝ} (hβ₂ : 0 < β₂)
    (hβ₂l : β₂ < min (T.β₂Up st la₀.circle.toPrefixV4 la₀.excl.β₃) (1 / 10 ^ 6)) :
    ∃ la : ClosedLaterV4 D T st, la.excl.β₃ = la₀.excl.β₃ ∧
      la.circle.toPrefixV4 = la₀.circle.toPrefixV4 ∧ la.excl.β₂ = β₂ := by
  have hC := D.C_pos
  have he := st.e_pos
  set β₃ := la₀.excl.β₃ with hβ₃def
  set θs := la₀.circle.θs
  set θe := la₀.circle.θe
  set θ₂ := la₀.circle.θ₂
  set γ := la₀.circle.γ
  set E := la₀.circle.E
  set δ := la₀.circle.δ
  set γc := la₀.circle.γc
  have hγc := la₀.γc_pos
  have hcu := T.circleUp_pos st β₃ θs θe θ₂
  obtain ⟨βc, hβc, hβcl⟩ := exists_pos_lt_V4C
    (lt_min (lt_min (show 0 < γc / 1000 by positivity) hcu) (show 0 < β₂ / 3 by positivity))
  let ci : ClosedCircleRequestsV2 := ⟨θs, θe, θ₂, γ, E, δ, γc, βc⟩
  obtain ⟨Δ, hΔ⟩ : ∃ x, max (10 ^ 6) (max (100 / β₂) (T.ΔLow st ci β₃ β₂)) < x :=
    ⟨_, lt_add_one _⟩
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hΔ.le)
  let ex : ClosedExclusions := ⟨β₃, β₂, Δ⟩
  have heu := T.errorsUp_pos st ci ex
  have hLpos : 0 < closedLongLength ex := by unfold closedLongLength; positivity
  have hθe := la₀.θe_pos
  have hqb : 0 < min (min (θe ^ 2 / 10 ^ 8) (1 / (1000 * closedLongLength ex)))
      (T.errorsUp st ci ex) :=
    lt_min (lt_min (by positivity) (by positivity)) heu
  obtain ⟨qe, hqe, hqel⟩ := exists_pos_lt_V4C hqb
  obtain ⟨qs, hqs, hqsl⟩ := exists_pos_lt_V4C hqb
  obtain ⟨ve, hve, hvel⟩ := exists_pos_lt_V4C (lt_min (show 0 < θe / 100 by positivity) heu)
  obtain ⟨ε, hε, hεl⟩ := exists_pos_lt_V4C heu
  obtain ⟨ζ, hζ, hζl⟩ := exists_pos_lt_V4C heu
  obtain ⟨e₀, he₀, he₀l⟩ := exists_pos_lt_V4C
    (lt_min (show (0 : ℝ) < 1 / 1000 by norm_num) heu)
  obtain ⟨ε₀, hε₀, hε₀l⟩ := exists_pos_lt_V4C (lt_min (show (0 : ℝ) < 1 / 100 by norm_num) heu)
  let co : ClosedCoordErrorsV2 := ⟨qe, qs, ve, ε, ζ, e₀, ε₀⟩
  have hsu := T.sectionUp_pos st ci ex co
  obtain ⟨τ, hτ, hτl⟩ := exists_pos_lt_V4C
    (lt_min (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
      (show 0 < β₂ / (4 * Δ) by positivity))
  obtain ⟨μ, hμ, hμl⟩ := exists_pos_lt_V4C
    (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
  let bd : ClosedBorderV2 := ⟨τ, μ⟩
  have hW := T.lfr29W_pos st ci ex co bd
  obtain ⟨b', hb', hb'l⟩ := exists_pos_lt_V4C
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  obtain ⟨s', hs', hs'l⟩ := exists_pos_lt_V4C
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  let wk : ClosedWeakV2 := ⟨b', s'⟩
  obtain ⟨s, hs, hsl⟩ := exists_pos_lt_V4C
    (lt_min (show 0 < 1 / 10 ^ 5 * min b' s' by have := lt_min hb' hs'; positivity)
      (T.endpointUp_pos st ci ex co bd wk))
  obtain ⟨σ, hσ, hσl⟩ := exists_pos_lt_V4C
    (lt_min (T.σcolUp_pos st ci ex co bd wk s) one_pos)
  let er : ClosedErrorsV2 := ⟨co, bd, wk, s, σ⟩
  set Cρ := closedScaleConstantV4 D T st with hCρ
  have hCρpos : 0 < Cρ := by
    have := D.bcut_pos
    have := D.one_le_L₀
    have := T.Nb_nonneg st
    have := T.cw_nonneg st
    have := st.Sig_pos 0
    rw [hCρ]
    unfold closedScaleConstantV4
    positivity
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_pos_lt_V4C (show 0 < min (T.scaleUp st ci ex er)
      (min (1 / 10 ^ 5 / closedLongLength ex) (min (1 / 10 ^ 8 / (100 * Δ))
        (min (1 / 10 ^ 6 / (Cρ * Δ)) (min (st.e 0 / (1000 * D.C 0) / Δ)
          (min (1 / (100 * (2 * 10 ^ 6) * Δ)) (s' / (10 ^ 8 * Δ ^ 2))))))) by
    have := hC 0; have := he 0
    exact lt_min (T.scaleUp_pos st ci ex er) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  simp only [lt_min_iff] at hΛl
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7⟩ := hΛl
  obtain ⟨w, hw, hwl⟩ := exists_pos_lt_V4C (lt_min (T.wUp_pos st ci ex er Λ)
    (show 0 < euclideanThreeUnitBallVolume by unfold euclideanThreeUnitBallVolume; positivity))
  let sc : ClosedScales := ⟨Λ, w⟩
  obtain ⟨b, hb, hbl⟩ := exists_pos_lt_V4C
    (lt_min (T.splitUp_pos st ci ex er sc) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨β₁, hβ₁, hβ₁l⟩ := exists_pos_lt_V4C
    (lt_min (T.β₁Up_pos st ci ex er sc b) (lt_min hβ₂ hζ))
  let T₀ := max (1600 * closedLongLength ex) (T.T₀Low st ci ex er sc b β₁)
  let sp : ClosedSplittings := ⟨b, β₁, T₀, T.lpa02V st ci ex er sc b β₁ T₀⟩
  let Lm := max (400 * sp.V) (T.LmaxLow st ci ex er sc sp) + 1
  obtain ⟨α₀, hα₀⟩ := (tendsto_atTop.mp T.H_tendsto (400 * sp.V + 1)).exists_forall_of_atTop
  refine ⟨{
    circle := ci, excl := ex, err := er, scale := sc, split := sp, Lmax := Lm
    tail := max (T.tailLow st ci ex er sc sp Lm) α₀
    edpβ := 1 / 2000, edpH := 1 / 2000
    β₃_pos := la₀.β₃_pos, β₃_lt := la₀.β₃_lt
    θs_pos := la₀.θs_pos, θs_lt := la₀.θs_lt, θe_pos := la₀.θe_pos, θe_lt := la₀.θe_lt
    θ₂_pos := la₀.θ₂_pos, θ₂_lt := la₀.θ₂_lt
    γ_pos := la₀.γ_pos, γ_lt := la₀.γ_lt, E_pos := la₀.E_pos, E_lt := la₀.E_lt
    δ_pos := la₀.δ_pos, δ_lt := la₀.δ_lt
    γc_pos := la₀.γc_pos, γc_lt := la₀.γc_lt
    β₂_pos := hβ₂, β₂_lt := hβ₂l, βc_pos := hβc, βc_lt := hβcl, Δ_gt := hΔ
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
    edpH_pos := by norm_num, edpH_lt := by norm_num }, rfl, rfl, rfl⟩
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

/-- **The `β₂` bound reads no value after the prefix**: two later choices with the same `β₃` and
the same circle prefix have the same `β₂` bound (in particular it does not read `β_c`). -/
theorem β₂_bound_eq_of_prefix_V4C (la₀ la : ClosedLaterV4 D T st) (h₃ : la.excl.β₃ = la₀.excl.β₃)
    (hp : la.circle.toPrefixV4 = la₀.circle.toPrefixV4) :
    min (T.β₂Up st la.circle.toPrefixV4 la.excl.β₃) (1 / 10 ^ 6) =
      min (T.β₂Up st la₀.circle.toPrefixV4 la₀.excl.β₃) (1 / 10 ^ 6) := by
  rw [h₃, hp]

/-- **All `β₂` upper bounds are merged before `β_c` (review 57, §2.3)**: over a fixed stage, `β₃`
and circle prefix, the `β₂` values of complete later choices are exactly the pre-`β_c` interval
`(0, min (β₂Up st prefix β₃) 10⁻⁶)`. For EVERY threshold record `T`: no slot after `β₂` lowers
it. -/
theorem β₂_realized_iff_V4C {la₀ : ClosedLaterV4 D T st} {β₂ : ℝ} :
    (∃ la : ClosedLaterV4 D T st, la.excl.β₃ = la₀.excl.β₃ ∧
      la.circle.toPrefixV4 = la₀.circle.toPrefixV4 ∧ la.excl.β₂ = β₂) ↔
      0 < β₂ ∧ β₂ < min (T.β₂Up st la₀.circle.toPrefixV4 la₀.excl.β₃) (1 / 10 ^ 6) := by
  constructor
  · rintro ⟨la, h₃, hp, rfl⟩
    exact ⟨la.β₂_pos, (β₂_bound_eq_of_prefix_V4C la₀ la h₃ hp) ▸ la.β₂_lt⟩
  · rintro ⟨h0, hl⟩
    exact exists_rechoose_β₂_V4C la₀ h0 hl

end ClosedLaterV4

/-- **Consumer (the merge check at a register)**: for every register `R` of every threshold record
and every `β₂'` in `R`'s pre-`β_c` interval there is a register with the same stage, `β₃`, circle
prefix and `β₂ = β₂'`; at it `3β_c < β₂'` (EDP06's collar request holds for the re-chosen `β_c`). -/
theorem ClosedRegisterV4.exists_rechoose_β₂_V4C {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) {β₂ : ℝ} (hβ₂ : 0 < β₂)
    (hβ₂l : β₂ < min (T.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃) (1 / 10 ^ 6)) :
    ∃ R' : ClosedRegisterV4 D T, R'.stage = R.stage ∧ R'.later.excl.β₃ = R.later.excl.β₃ ∧
      R'.later.circle.toPrefixV4 = R.later.circle.toPrefixV4 ∧ R'.β 2 = β₂ ∧
      3 * R'.later.circle.βc < β₂ := by
  obtain ⟨la, h₃, hp, h₂⟩ := R.later.exists_rechoose_β₂_V4C hβ₂ hβ₂l
  refine ⟨⟨R.stage, la⟩, rfl, h₃, hp, ?_, ?_⟩
  · rw [ClosedRegisterV4.β_two_VAL6]
    exact h₂
  · have := la.three_mul_βc_lt_β₂_VAL6
    rw [h₂] at this
    exact this

end DifferentialGeometry.Geometry.Collapse
