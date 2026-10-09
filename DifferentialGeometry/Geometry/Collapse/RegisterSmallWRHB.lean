import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4

/-!
# Registers with a small volume parameter (lane S-RHOBOUNDS, finding F-REG-1, G2)

`ClosedLaterV4` bounds `w` only from ABOVE (`w_pos`, `w_lt : w < min (wUp ..) c₃`), `w` is chosen
after `β₂`: the existence proof of `exists_closedLaterV4` (StaticRegisterV4.lean) picks `w` by
`∃ x, 0 < x ∧ x < b`, so any smaller positive `w` is equally admissible.  This module re-runs that
proof with the extra bound `w ≤ (3/10) β₂`: the registers at which the existing torus fixture
(fibre `β₂`) fails LPA01's window (`ClosedLaterV4.torWindowOld_fails_RHB`) exist.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

private theorem exists_pos_lt_RHB {b : ℝ} (hb : 0 < b) : ∃ x, 0 < x ∧ x < b :=
  ⟨b / 2, half_pos hb, half_lt_self hb⟩

/-- **A register with `w ≤ (3/10) β₂` exists** (for every stage choice): the later choices are
admissible with a volume parameter far below the circle tolerance. -/
theorem exists_closedLaterV4_smallW_RHB (D : ClosedEarlyData) (T : ClosedThresholdsV4 D)
    (st : ClosedStage D) :
    ∃ la : ClosedLaterV4 D T st, la.scale.w ≤ 3 / 10 * la.excl.β₂ := by
  have hC := D.C_pos
  have he := st.e_pos
  -- PR12, first step (register V4)
  obtain ⟨β₃, hβ₃, hβ₃l⟩ := exists_pos_lt_RHB T.lc18_pos
  -- PR11, at `β₃`
  obtain ⟨θs, hθs, hθsl⟩ := exists_pos_lt_RHB (show 0 < st.e 2 / (10 * D.C 2) by
    have := hC 2; have := he 2; positivity)
  obtain ⟨θe, hθe, hθel⟩ := exists_pos_lt_RHB
    (show 0 < min (st.e 1 / (10 * D.C 1)) (1 / 100) by
      have := hC 1; have := he 1; exact lt_min (by positivity) (by norm_num))
  obtain ⟨θ₂, hθ₂, hθ₂l⟩ := exists_pos_lt_RHB (show 0 < st.e 0 / (100 * D.C 0 ^ 2) by
    have := hC 0; have := he 0; positivity)
  have hcu := T.circleUp_pos st β₃ θs θe θ₂
  obtain ⟨γ, hγ, hγl⟩ := exists_pos_lt_RHB
    (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 12 by positivity) hcu)
  obtain ⟨E, hE, hEl⟩ := exists_pos_lt_RHB (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  obtain ⟨δ, hδ, hδl⟩ := exists_pos_lt_RHB (lt_min (show 0 < θ₂ ^ 2 / 10 ^ 8 by positivity) hcu)
  obtain ⟨γc, hγc, hγcl⟩ := exists_pos_lt_RHB hcu
  let cp : ClosedCirclePrefixV4 := ⟨θs, θe, θ₂, γ, E, δ, γc⟩
  -- PR12, second step, at the prefix without `βc`
  obtain ⟨β₂, hβ₂, hβ₂l⟩ := exists_pos_lt_RHB
    (lt_min (T.β₂Up_pos st cp β₃) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  -- register V4: `βc` after `β₂`, below `β₂ / 3`
  obtain ⟨βc, hβc, hβcl⟩ := exists_pos_lt_RHB
    (lt_min (lt_min (show 0 < γc / 1000 by positivity) hcu) (show 0 < β₂ / 3 by positivity))
  let ci : ClosedCircleRequestsV2 := ⟨θs, θe, θ₂, γ, E, δ, γc, βc⟩
  -- PR13
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
  obtain ⟨qe, hqe, hqel⟩ := exists_pos_lt_RHB hqb
  obtain ⟨qs, hqs, hqsl⟩ := exists_pos_lt_RHB hqb
  obtain ⟨ve, hve, hvel⟩ := exists_pos_lt_RHB (lt_min (show 0 < θe / 100 by positivity) heu)
  obtain ⟨ε, hε, hεl⟩ := exists_pos_lt_RHB heu
  obtain ⟨ζ, hζ, hζl⟩ := exists_pos_lt_RHB heu
  obtain ⟨e₀, he₀, he₀l⟩ := exists_pos_lt_RHB
    (lt_min (show (0 : ℝ) < 1 / 1000 by norm_num) heu)
  obtain ⟨ε₀, hε₀, hε₀l⟩ := exists_pos_lt_RHB (lt_min (show (0 : ℝ) < 1 / 100 by norm_num) heu)
  let co : ClosedCoordErrorsV2 := ⟨qe, qs, ve, ε, ζ, e₀, ε₀⟩
  -- PR18: (τ, μ), then (b', s'), then s, then σ_col
  have hsu := T.sectionUp_pos st ci ex co
  obtain ⟨τ, hτ, hτl⟩ := exists_pos_lt_RHB
    (lt_min (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
      (show 0 < β₂ / (4 * Δ) by positivity))
  obtain ⟨μ, hμ, hμl⟩ := exists_pos_lt_RHB
    (lt_min (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) hsu)
  let bd : ClosedBorderV2 := ⟨τ, μ⟩
  have hW := T.lfr29W_pos st ci ex co bd
  obtain ⟨b', hb', hb'l⟩ := exists_pos_lt_RHB
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  obtain ⟨s', hs', hs'l⟩ := exists_pos_lt_RHB
    (lt_min hW (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))
  let wk : ClosedWeakV2 := ⟨b', s'⟩
  obtain ⟨s, hs, hsl⟩ := exists_pos_lt_RHB
    (lt_min (show 0 < 1 / 10 ^ 5 * min b' s' by have := lt_min hb' hs'; positivity)
      (T.endpointUp_pos st ci ex co bd wk))
  obtain ⟨σ, hσ, hσl⟩ := exists_pos_lt_RHB
    (lt_min (T.σcolUp_pos st ci ex co bd wk s) one_pos)
  let er : ClosedErrorsV2 := ⟨co, bd, wk, s, σ⟩
  -- PR19 (RegScale)
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
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_pos_lt_RHB (show 0 < min (T.scaleUp st ci ex er)
      (min (1 / 10 ^ 5 / closedLongLength ex) (min (1 / 10 ^ 8 / (100 * Δ))
        (min (1 / 10 ^ 6 / (Cρ * Δ)) (min (st.e 0 / (1000 * D.C 0) / Δ)
          (min (1 / (100 * (2 * 10 ^ 6) * Δ)) (s' / (10 ^ 8 * Δ ^ 2))))))) by
    have := hC 0; have := he 0
    exact lt_min (T.scaleUp_pos st ci ex er) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  simp only [lt_min_iff] at hΛl
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4, hΛ5, hΛ6, hΛ7⟩ := hΛl
  -- PR20
  obtain ⟨w, hw, hwl'⟩ := exists_pos_lt_RHB (lt_min (lt_min (T.wUp_pos st ci ex er Λ)
    (show 0 < euclideanThreeUnitBallVolume by unfold euclideanThreeUnitBallVolume; positivity))
    (show 0 < 3 / 10 * β₂ by positivity))
  have hwl : w < min (T.wUp st ci ex er Λ) euclideanThreeUnitBallVolume :=
    lt_of_lt_of_le hwl' (min_le_left _ _)
  have hwβ : w ≤ 3 / 10 * β₂ := (lt_of_lt_of_le hwl' (min_le_right _ _)).le
  let sc : ClosedScales := ⟨Λ, w⟩
  -- PR21–PR23
  obtain ⟨b, hb, hbl⟩ := exists_pos_lt_RHB
    (lt_min (T.splitUp_pos st ci ex er sc) (show (0 : ℝ) < 1 / 10 ^ 6 by norm_num))
  obtain ⟨β₁, hβ₁, hβ₁l⟩ := exists_pos_lt_RHB
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
    β₃_pos := hβ₃, β₃_lt := hβ₃l
    θs_pos := hθs, θs_lt := hθsl, θe_pos := hθe, θe_lt := hθel, θ₂_pos := hθ₂, θ₂_lt := hθ₂l
    γ_pos := hγ, γ_lt := hγl, E_pos := hE, E_lt := hEl, δ_pos := hδ, δ_lt := hδl
    γc_pos := hγc, γc_lt := hγcl
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
    edpH_pos := by norm_num, edpH_lt := by norm_num }, hwβ⟩
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

end DifferentialGeometry.Geometry.Collapse
