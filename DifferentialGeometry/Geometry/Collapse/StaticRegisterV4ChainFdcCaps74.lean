import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCaps

/-!
# The FDC caps: the numeric premises of the eventual FDC theorems in the register's slots

Lane S-REG-NUM (`_RNUM`), G2 (D74-18). The eventual FDC theorems
(`eventually_fdc02_M1_C14Z_EFC`, `eventually_fdc04_M1_C14Z_EFC`) take, for `Δ ≥ 100`,
`0 < β₂ < 10⁻⁶`, `0 < Λ₀`, a triple `(L_c, η₀, w₀)` (in THIS order: first `Δ, β₂, Λ₀`, then the
triple, then `w < w₀`, then the standing sequence and the tail), and on every packet at the
register's values the premises

`b < 10⁻⁶`, `b ≤ η₀`, `β₁ ≤ η₀`, `L_c ≤ L_max`, `μΔ < 10⁻⁴`, `w < w₀`

(the rest — `β₃ ≤ lc18`, `β₂ < 10⁻⁶`, `s < 10⁻⁶`, `μ, τ ≤ 10⁻⁸`, `σ_c ≤ 10⁻¹²`, `ε_r < 1/2`,
`e ≤ 1/1000` — are already register facts, see `register_yields_numerics_RNUM`).
Register V4 as it stands has NO slot carrying them: the chain caps give `μΔ < θ/100` only, and
`η₀, L_c, w₀` there are the PLANES producers' (a different triple, at `(st, Δ, β₂)`). They are read
at slots chosen AFTER their arguments (no change of quantifier):

* `sectionUp ≤ 1/(10⁴ Δ)` (read at `Δ`): `μΔ < 10⁻⁴`;
* `wUp ≤ w₀(Δ, β₂, Λ)` (read at `Λ`): `w < w₀`;
* `splitUp ≤ η₀(Δ, β₂, Λ)` and `β₁Up ≤ η₀(Δ, β₂, Λ)` (read at the scale `sc ∋ Λ`): `b, β₁ ≤ η₀`;
* `T₀Low ≥ L_c(Δ, β₂, Λ)`: `L_c ≤ T₀ ≤ V < L_max`.

* `ClosedThresholdsV4.withFdcCaps_RNUM`, `…withFdcCaps_refines_RNUM` (the caps keep `N_b, c_w, I₁,
  LmaxLow, endpointUp`; `tailLow` unchanged — the FDC tail is taken AFTER the register, see
  `StaticRegisterV4ChainFdcFacts74`);
* `ClosedRegisterV4.fdcCaps_RNUM`: the register inequalities below the caps.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse

/-- **The FDC caps**: `Lcf, η₀f, w₀f : (Δ, β₂, Λ) ↦ ℝ` placed in the slots that read their
arguments (module header). -/
def ClosedThresholdsV4.withFdcCaps_RNUM {D : ClosedEarlyData} (U : ClosedThresholdsV4 D)
    (Lcf η₀f w₀f : ℝ → ℝ → ℝ → ℝ) : ClosedThresholdsV4 D :=
  { U with
    sectionUp := fun st ci ex co => min (U.sectionUp st ci ex co)
      (posOr_VAL3 (1 / (10 ^ 4 * ex.Δ)))
    sectionUp_pos := fun st ci ex co => lt_min (U.sectionUp_pos st ci ex co) (posOr_pos_VAL3 _)
    wUp := fun st ci ex er Λ => min (U.wUp st ci ex er Λ) (posOr_VAL3 (w₀f ex.Δ ex.β₂ Λ))
    wUp_pos := fun st ci ex er Λ => lt_min (U.wUp_pos st ci ex er Λ) (posOr_pos_VAL3 _)
    splitUp := fun st ci ex er sc => min (U.splitUp st ci ex er sc)
      (posOr_VAL3 (η₀f ex.Δ ex.β₂ sc.Λ))
    splitUp_pos := fun st ci ex er sc => lt_min (U.splitUp_pos st ci ex er sc) (posOr_pos_VAL3 _)
    β₁Up := fun st ci ex er sc b => min (U.β₁Up st ci ex er sc b)
      (posOr_VAL3 (η₀f ex.Δ ex.β₂ sc.Λ))
    β₁Up_pos := fun st ci ex er sc b => lt_min (U.β₁Up_pos st ci ex er sc b) (posOr_pos_VAL3 _)
    T₀Low := fun st ci ex er sc b β₁ => max (U.T₀Low st ci ex er sc b β₁)
      (Lcf ex.Δ ex.β₂ sc.Λ) }

/-- The FDC caps refine `U` (`N_b, c_w, I₁, LmaxLow, endpointUp` unchanged). -/
theorem ClosedThresholdsV4.withFdcCaps_refines_RNUM {D : ClosedEarlyData}
    (U : ClosedThresholdsV4 D) (Lcf η₀f w₀f : ℝ → ℝ → ℝ → ℝ) :
    ClosedStrategyRefinesV4 (U.withFdcCaps_RNUM Lcf η₀f w₀f) U where
  Nb_eq := rfl
  cw_eq := rfl
  I₁_eq := rfl
  LmaxLow_eq := rfl
  endpointUp_eq := rfl
  circleUp_le := fun _ _ _ _ _ => le_rfl
  lc18_le := le_rfl
  β₂Up_le := fun _ _ _ => le_rfl
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => min_le_left _ _
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => min_le_left _ _
  splitUp_le := fun _ _ _ _ _ => min_le_left _ _
  β₁Up_le := fun _ _ _ _ _ _ => min_le_left _ _
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_max_left _ _
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **The register inequalities below the FDC caps**: at a register of a strategy below the caps,
with the three cap values positive at the register's `(Δ, β₂, Λ)`: `μΔ < 10⁻⁴`, `w < w₀`,
`b < η₀`, `β₁ < η₀` and `L_c ≤ T₀` (hence `L_c ≤ V < L_max`). -/
theorem ClosedRegisterV4.fdcCaps_RNUM {D : ClosedEarlyData} {U T : ClosedThresholdsV4 D}
    {Lcf η₀f w₀f : ℝ → ℝ → ℝ → ℝ}
    (h : ClosedStrategyBelowV4 T (U.withFdcCaps_RNUM Lcf η₀f w₀f)) (R : ClosedRegisterV4 D T)
    (hη₀ : 0 < η₀f R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ)
    (hw₀ : 0 < w₀f R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ) :
    R.later.err.bd.μ * R.later.excl.Δ < 1 / 10 ^ 4 ∧
      R.later.scale.w < w₀f R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ ∧
      R.later.split.b < η₀f R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ ∧
      R.later.split.β₁ < η₀f R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ ∧
      Lcf R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ ≤ R.later.split.T₀ := by
  have hΔ := R.later.Δ_pos_VAL6
  -- the section slot
  have hsu := h.sectionUp_le R.stage R.later.circle R.later.excl R.later.err.co
  change _ ≤ min _ (posOr_VAL3 _) at hsu
  rw [posOr_eq_VAL3 (by positivity : 0 < 1 / (10 ^ 4 * R.later.excl.Δ))] at hsu
  have hμ : R.later.err.bd.μ < 1 / (10 ^ 4 * R.later.excl.Δ) :=
    (R.later.μ_lt.trans_le (min_le_right _ _)).trans_le (hsu.trans (min_le_right _ _))
  have hμΔ : R.later.err.bd.μ * R.later.excl.Δ < 1 / 10 ^ 4 := by
    have := mul_lt_mul_of_pos_right hμ hΔ
    have e : 1 / (10 ^ 4 * R.later.excl.Δ) * R.later.excl.Δ = 1 / 10 ^ 4 := by field_simp
    rwa [e] at this
  -- the scale slot
  have hwu := h.wUp_le R.stage R.later.circle R.later.excl R.later.err R.later.scale.Λ
  change _ ≤ min _ (posOr_VAL3 _) at hwu
  rw [posOr_eq_VAL3 hw₀] at hwu
  -- the splitting slots
  have hpu := h.splitUp_le R.stage R.later.circle R.later.excl R.later.err R.later.scale
  change _ ≤ min _ (posOr_VAL3 _) at hpu
  rw [posOr_eq_VAL3 hη₀] at hpu
  have hqu := h.β₁Up_le R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b
  change _ ≤ min _ (posOr_VAL3 _) at hqu
  rw [posOr_eq_VAL3 hη₀] at hqu
  -- the lower slot
  have htu := h.T₀Low_ge R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁
  change max _ _ ≤ _ at htu
  have hT₀ : T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ ≤ R.later.split.T₀ := (le_max_right _ _).trans R.later.T₀_ge
  exact ⟨hμΔ, (R.later.w_lt.trans_le (min_le_left _ _)).trans_le (hwu.trans (min_le_right _ _)),
    (R.later.b_lt.trans_le (min_le_left _ _)).trans_le (hpu.trans (min_le_right _ _)),
    (R.later.β₁_lt.trans_le (min_le_left _ _)).trans_le (hqu.trans (min_le_right _ _)),
    ((le_max_right _ _).trans htu).trans hT₀⟩

end DifferentialGeometry.Geometry.Collapse
