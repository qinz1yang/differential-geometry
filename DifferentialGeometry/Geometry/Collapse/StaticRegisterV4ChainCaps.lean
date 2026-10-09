import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlots
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4RowsStrategy
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraph

/-!
# The chain caps of register V4: FC27's three stage tests in the register's slots

Lane C14-REG-CHAIN (review 66, D66-5). The chain object needs, on the packet, the hypotheses of
FC27's three stage tests at the register's stage values (first test with (PP) and the scale clause,
`fc27_first_test_pps_GAF5`; edge test, `fc27_edge_test_pp_GAF4`; slim test,
`fc27_slim_test_pp_C14_GAF4`). Their thresholds are functions of earlier register values only:

* first test, at `(st, ν)` with `ν = β₃/3`: `σ, η₂, γ₀, η_c, θ` (and `η₁` at `(st, ν, Δ)`);
* edge test, at `(st, Δ, β₂)`: `L_c, η₀`; slim test, at `(st, Δ, β₂)`: `θ_s, L_c', η₀'`.

`ClosedThresholdsV4.withChainCaps_RGC U …` places each of them in the slot that reads its arguments:
`lc18 ≤ 1` (`β₃ < 1`), `circleUp ≤ γ₀, η_c, 1` (read at `β₃`), `β₂Up ≤ σ/3, η₂` (read at `β₃`),
`errorsUp ≤ chainErrCap_RGC` (read at `Δ, β₂, β₃`), `sectionUp ≤ chainSectionCap_RGC` (`μΔ`),
`splitUp ≤ η₁, η₀`, `β₁Up ≤ η₁, η₀, η₀'`, and the lower slot `T₀Low ≥ σ⁻¹, L_c, L_c'` (so the
tests' `σ⁻¹, L_c, L_c' ≤ L_max` follow from `T₀ ≤ V < L_max`). The caps keep `N_b, c_w, I₁,
LmaxLow, endpointUp`, so a strategy refining them refines `U` (`withChainCaps_refines_RGC`).
No order conflict: every threshold is read at a slot chosen after its arguments.

* `chainErrCap_RGC`, `chainSectionCap_RGC` and their extraction lemmas;
* `ClosedThresholdsV4.withChainCaps_RGC`, `…withChainCaps_refines_RGC`;
* `ClosedStrategyRefinesV4.trans_RGC`;
* `ClosedRegisterV4.chainCaps_RGC`: the register inequalities below the caps.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The errors cap of the chain: FC27's first-test requests at `θ`, the edge test's at
`e = e₂` (`e/(20C_EGP)`), the slim test's at `θ_s`, and the `Δ`-requests on `ζ, ε_r`. -/
def chainErrCap_RGC (θ θs eg Δ : ℝ) : ℝ :=
  min (min 1 (min (θ ^ 2 / 1000) (θ / 100)))
    (min (min ((eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8) (min (eg / (20 * egpGraphConst) / 100)
      (min (1 / (1000 * (1000000 * Δ))) (eg / (20 * egpGraphConst) / (100 * (1000000 * Δ))))))
      (min (θs ^ 2 / 10 ^ 6) (min (θs / 100)
        (min (1 / (100 * (1000000 * Δ))) (θs / (100 * (1000000 * Δ)))))))

theorem chainErrCap_pos_RGC {θ θs eg Δ : ℝ} (hθ : 0 < θ) (hθs : 0 < θs) (heg : 0 < eg)
    (hΔ : 0 < Δ) : 0 < chainErrCap_RGC θ θs eg Δ := by
  have hC := egpGraphConst_pos_KC4
  unfold chainErrCap_RGC
  simp only [lt_min_iff]
  refine ⟨⟨one_pos, by positivity, by positivity⟩, ⟨by positivity, by positivity, by positivity,
    by positivity⟩, by positivity, by positivity, by positivity, by positivity⟩

/-- Every request inside the errors cap. -/
theorem lt_of_lt_chainErrCap_RGC {x θ θs eg Δ : ℝ} (h : x < chainErrCap_RGC θ θs eg Δ) :
    x < 1 ∧ x < θ ^ 2 / 1000 ∧ x < θ / 100 ∧ x < (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
      x < eg / (20 * egpGraphConst) / 100 ∧ x < 1 / (1000 * (1000000 * Δ)) ∧
      x < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) ∧ x < θs ^ 2 / 10 ^ 6 ∧
      x < θs / 100 ∧ x < 1 / (100 * (1000000 * Δ)) ∧ x < θs / (100 * (1000000 * Δ)) := by
  unfold chainErrCap_RGC at h
  simp only [lt_min_iff] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The full-collar cap of the chain: `μΔ ≤ θ/100` (first test) and `μΔ < e/(20C_EGP)/100` (edge
test). -/
def chainSectionCap_RGC (θ eg Δ : ℝ) : ℝ :=
  min (θ / (100 * Δ)) (eg / (20 * egpGraphConst) / (100 * Δ))

theorem chainSectionCap_pos_RGC {θ eg Δ : ℝ} (hθ : 0 < θ) (heg : 0 < eg) (hΔ : 0 < Δ) :
    0 < chainSectionCap_RGC θ eg Δ := by
  have hC := egpGraphConst_pos_KC4
  unfold chainSectionCap_RGC
  exact lt_min (by positivity) (by positivity)

/-- The two `μΔ` requests below the full-collar cap. -/
theorem mul_lt_of_lt_chainSectionCap_RGC {μ θ eg Δ : ℝ} (hΔ : 0 < Δ)
    (h : μ < chainSectionCap_RGC θ eg Δ) :
    μ * Δ < θ / 100 ∧ μ * Δ < eg / (20 * egpGraphConst) / 100 := by
  unfold chainSectionCap_RGC at h
  simp only [lt_min_iff] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : θ / (100 * Δ) * Δ = θ / 100 := by field_simp
  have e2 : eg / (20 * egpGraphConst) / (100 * Δ) * Δ = eg / (20 * egpGraphConst) / 100 := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← e1]
    exact mul_lt_mul_of_pos_right h1 hΔ
  · rw [← e2]
    exact mul_lt_mul_of_pos_right h2 hΔ

/-- **The chain caps** (see the module header): FC27's three test thresholds, as functions of the
earlier register values, placed in the slots that read them. -/
def ClosedThresholdsV4.withChainCaps_RGC {D : ClosedEarlyData} (U : ClosedThresholdsV4 D)
    (σf η₂f γ₀f ηcf θf : ClosedStage D → ℝ → ℝ)
    (η₁f Lc₁f η₀₁f θsf Lc₂f η₀₂f : ClosedStage D → ℝ → ℝ → ℝ) : ClosedThresholdsV4 D :=
  { U with
    lc18 := min U.lc18 1
    lc18_pos := lt_min U.lc18_pos one_pos
    circleUp := fun st β₃ θs θe θ₂ => min (U.circleUp st β₃ θs θe θ₂)
      (min (posOr_VAL3 (γ₀f st (β₃ / 3))) (min (posOr_VAL3 (ηcf st (β₃ / 3))) 1))
    circleUp_pos := fun st β₃ θs θe θ₂ => lt_min (U.circleUp_pos st β₃ θs θe θ₂)
      (lt_min (posOr_pos_VAL3 _) (lt_min (posOr_pos_VAL3 _) one_pos))
    β₂Up := fun st ci β₃ => min (U.β₂Up st ci β₃)
      (min (posOr_VAL3 (σf st (β₃ / 3) / 3)) (posOr_VAL3 (η₂f st (β₃ / 3))))
    β₂Up_pos := fun st ci β₃ => lt_min (U.β₂Up_pos st ci β₃)
      (lt_min (posOr_pos_VAL3 _) (posOr_pos_VAL3 _))
    errorsUp := fun st ci ex => min (U.errorsUp st ci ex)
      (posOr_VAL3 (chainErrCap_RGC (θf st (ex.β₃ / 3)) (θsf st ex.Δ ex.β₂) (st.e 1) ex.Δ))
    errorsUp_pos := fun st ci ex => lt_min (U.errorsUp_pos st ci ex) (posOr_pos_VAL3 _)
    sectionUp := fun st ci ex co => min (U.sectionUp st ci ex co)
      (posOr_VAL3 (chainSectionCap_RGC (θf st (ex.β₃ / 3)) (st.e 1) ex.Δ))
    sectionUp_pos := fun st ci ex co => lt_min (U.sectionUp_pos st ci ex co) (posOr_pos_VAL3 _)
    splitUp := fun st ci ex er sc => min (U.splitUp st ci ex er sc)
      (posOr_VAL3 (min (η₁f st (ex.β₃ / 3) ex.Δ) (η₀₁f st ex.Δ ex.β₂)))
    splitUp_pos := fun st ci ex er sc => lt_min (U.splitUp_pos st ci ex er sc) (posOr_pos_VAL3 _)
    β₁Up := fun st ci ex er sc b => min (U.β₁Up st ci ex er sc b)
      (posOr_VAL3 (min (η₁f st (ex.β₃ / 3) ex.Δ) (min (η₀₁f st ex.Δ ex.β₂) (η₀₂f st ex.Δ ex.β₂))))
    β₁Up_pos := fun st ci ex er sc b => lt_min (U.β₁Up_pos st ci ex er sc b) (posOr_pos_VAL3 _)
    T₀Low := fun st ci ex er sc b β₁ => max (U.T₀Low st ci ex er sc b β₁)
      (max (σf st (ex.β₃ / 3))⁻¹ (max (Lc₁f st ex.Δ ex.β₂) (Lc₂f st ex.Δ ex.β₂))) }

/-- The chain caps refine `U` (`N_b, c_w, I₁, LmaxLow, endpointUp` unchanged). -/
theorem ClosedThresholdsV4.withChainCaps_refines_RGC {D : ClosedEarlyData}
    (U : ClosedThresholdsV4 D) (σf η₂f γ₀f ηcf θf : ClosedStage D → ℝ → ℝ)
    (η₁f Lc₁f η₀₁f θsf Lc₂f η₀₂f : ClosedStage D → ℝ → ℝ → ℝ) :
    ClosedStrategyRefinesV4 (U.withChainCaps_RGC σf η₂f γ₀f ηcf θf η₁f Lc₁f η₀₁f θsf Lc₂f η₀₂f)
      U where
  Nb_eq := rfl
  cw_eq := rfl
  I₁_eq := rfl
  LmaxLow_eq := rfl
  endpointUp_eq := rfl
  circleUp_le := fun _ _ _ _ _ => min_le_left _ _
  lc18_le := min_le_left _ _
  β₂Up_le := fun _ _ _ => min_le_left _ _
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => min_le_left _ _
  sectionUp_le := fun _ _ _ _ => min_le_left _ _
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => min_le_left _ _
  β₁Up_le := fun _ _ _ _ _ _ => min_le_left _ _
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_max_left _ _
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- Refinement is transitive. -/
theorem ClosedStrategyRefinesV4.trans_RGC {D : ClosedEarlyData} {T U W : ClosedThresholdsV4 D}
    (h₁ : ClosedStrategyRefinesV4 T U) (h₂ : ClosedStrategyRefinesV4 U W) :
    ClosedStrategyRefinesV4 T W where
  Nb_eq := h₁.Nb_eq.trans h₂.Nb_eq
  cw_eq := h₁.cw_eq.trans h₂.cw_eq
  I₁_eq := h₁.I₁_eq.trans h₂.I₁_eq
  LmaxLow_eq := h₁.LmaxLow_eq.trans h₂.LmaxLow_eq
  endpointUp_eq := h₁.endpointUp_eq.trans h₂.endpointUp_eq
  circleUp_le := fun _ _ _ _ _ => (h₁.circleUp_le _ _ _ _ _).trans (h₂.circleUp_le _ _ _ _ _)
  lc18_le := h₁.lc18_le.trans h₂.lc18_le
  β₂Up_le := fun _ _ _ => (h₁.β₂Up_le _ _ _).trans (h₂.β₂Up_le _ _ _)
  ΔLow_ge := fun _ _ _ _ => (h₂.ΔLow_ge _ _ _ _).trans (h₁.ΔLow_ge _ _ _ _)
  errorsUp_le := fun _ _ _ => (h₁.errorsUp_le _ _ _).trans (h₂.errorsUp_le _ _ _)
  sectionUp_le := fun _ _ _ _ => (h₁.sectionUp_le _ _ _ _).trans (h₂.sectionUp_le _ _ _ _)
  lfr29W_le := fun _ _ _ _ _ => (h₁.lfr29W_le _ _ _ _ _).trans (h₂.lfr29W_le _ _ _ _ _)
  σcolUp_le := fun _ _ _ _ _ _ _ =>
    (h₁.σcolUp_le _ _ _ _ _ _ _).trans (h₂.σcolUp_le _ _ _ _ _ _ _)
  scaleUp_le := fun _ _ _ _ => (h₁.scaleUp_le _ _ _ _).trans (h₂.scaleUp_le _ _ _ _)
  wUp_le := fun _ _ _ _ _ => (h₁.wUp_le _ _ _ _ _).trans (h₂.wUp_le _ _ _ _ _)
  splitUp_le := fun _ _ _ _ _ => (h₁.splitUp_le _ _ _ _ _).trans (h₂.splitUp_le _ _ _ _ _)
  β₁Up_le := fun _ _ _ _ _ _ => (h₁.β₁Up_le _ _ _ _ _ _).trans (h₂.β₁Up_le _ _ _ _ _ _)
  T₀Low_ge := fun _ _ _ _ _ _ _ => (h₂.T₀Low_ge _ _ _ _ _ _ _).trans (h₁.T₀Low_ge _ _ _ _ _ _ _)
  tailLow_ge := fun _ _ _ _ _ _ _ =>
    (h₂.tailLow_ge _ _ _ _ _ _ _).trans (h₁.tailLow_ge _ _ _ _ _ _ _)

/-- **The register inequalities below the chain caps**: at a register of a strategy below the caps,
with `ν = β₃/3` and the thresholds positive at the register's arguments: `β₃ < 1`, `3β₂ ≤ σ`,
`β₂ ≤ η₂`, `γ, γc ≤ γ₀`, `γc ≤ 1`, `βc ≤ η_c`, the six coordinate errors below the errors cap, `μ`
below the full-collar cap, `b < min(η₁, η₀)`, `β₁ < min(η₁, η₀, η₀')`, and `σ⁻¹, L_c, L_c' ≤ T₀`. -/
theorem ClosedRegisterV4.chainCaps_RGC {D : ClosedEarlyData} {U T : ClosedThresholdsV4 D}
    {σf η₂f γ₀f ηcf θf : ClosedStage D → ℝ → ℝ}
    {η₁f Lc₁f η₀₁f θsf Lc₂f η₀₂f : ClosedStage D → ℝ → ℝ → ℝ}
    (h : ClosedStrategyBelowV4 T (U.withChainCaps_RGC σf η₂f γ₀f ηcf θf η₁f Lc₁f η₀₁f θsf Lc₂f
      η₀₂f))
    (R : ClosedRegisterV4 D T)
    (hσ : 0 < σf R.stage (R.later.excl.β₃ / 3)) (hη₂ : 0 < η₂f R.stage (R.later.excl.β₃ / 3))
    (hγ₀ : 0 < γ₀f R.stage (R.later.excl.β₃ / 3)) (hηc : 0 < ηcf R.stage (R.later.excl.β₃ / 3))
    (hθ : 0 < θf R.stage (R.later.excl.β₃ / 3))
    (hη₁ : 0 < η₁f R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ)
    (hη₀₁ : 0 < η₀₁f R.stage R.later.excl.Δ R.later.excl.β₂)
    (hθs : 0 < θsf R.stage R.later.excl.Δ R.later.excl.β₂)
    (hη₀₂ : 0 < η₀₂f R.stage R.later.excl.Δ R.later.excl.β₂) :
    R.later.excl.β₃ < 1 ∧ 3 * R.later.excl.β₂ ≤ σf R.stage (R.later.excl.β₃ / 3) ∧
      R.later.excl.β₂ ≤ η₂f R.stage (R.later.excl.β₃ / 3) ∧
      R.later.circle.γ ≤ γ₀f R.stage (R.later.excl.β₃ / 3) ∧
      R.later.circle.γc ≤ γ₀f R.stage (R.later.excl.β₃ / 3) ∧ R.later.circle.γc ≤ 1 ∧
      R.later.circle.βc ≤ ηcf R.stage (R.later.excl.β₃ / 3) ∧
      (∀ x ∈ ({R.later.err.co.qe, R.later.err.co.qs, R.later.err.co.ve, R.later.err.co.ε,
          R.later.err.co.ζ, R.later.err.co.ε₀} : Set ℝ),
        x < chainErrCap_RGC (θf R.stage (R.later.excl.β₃ / 3))
          (θsf R.stage R.later.excl.Δ R.later.excl.β₂) (R.stage.e 1) R.later.excl.Δ) ∧
      R.later.err.bd.μ < chainSectionCap_RGC (θf R.stage (R.later.excl.β₃ / 3)) (R.stage.e 1)
        R.later.excl.Δ ∧
      R.later.split.b < min (η₁f R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ)
        (η₀₁f R.stage R.later.excl.Δ R.later.excl.β₂) ∧
      R.later.split.β₁ < min (η₁f R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ)
        (min (η₀₁f R.stage R.later.excl.Δ R.later.excl.β₂)
          (η₀₂f R.stage R.later.excl.Δ R.later.excl.β₂)) ∧
      (σf R.stage (R.later.excl.β₃ / 3))⁻¹ ≤ R.later.split.T₀ ∧
      Lc₁f R.stage R.later.excl.Δ R.later.excl.β₂ ≤ R.later.split.T₀ ∧
      Lc₂f R.stage R.later.excl.Δ R.later.excl.β₂ ≤ R.later.split.T₀ := by
  have hΔ := R.later.Δ_pos_VAL6
  have he := R.stage.e_pos 1
  -- the circle slot
  have hcu := h.circleUp_le R.stage R.later.excl.β₃ R.later.circle.θs R.later.circle.θe
    R.later.circle.θ₂
  change _ ≤ min _ (min (posOr_VAL3 _) (min (posOr_VAL3 _) 1)) at hcu
  rw [posOr_eq_VAL3 hγ₀, posOr_eq_VAL3 hηc] at hcu
  simp only [le_min_iff] at hcu
  obtain ⟨-, hcuγ, hcuη, hcu1⟩ := hcu
  have hγ : R.later.circle.γ < T.circleUp R.stage R.later.excl.β₃ R.later.circle.θs
      R.later.circle.θe R.later.circle.θ₂ := R.later.γ_lt.trans_le (min_le_right _ _)
  have hγc := R.later.γc_lt
  have hβc := R.later.βc_lt_circleUp_VAL6
  -- the `β₂` slot
  have hbu := h.β₂Up_le R.stage R.later.circle.toPrefixV4 R.later.excl.β₃
  change _ ≤ min _ (min (posOr_VAL3 _) (posOr_VAL3 _)) at hbu
  rw [posOr_eq_VAL3 (by positivity : 0 < σf R.stage (R.later.excl.β₃ / 3) / 3),
    posOr_eq_VAL3 hη₂] at hbu
  simp only [le_min_iff] at hbu
  obtain ⟨-, hbuσ, hbuη⟩ := hbu
  have hβ₂ : R.later.excl.β₂ < T.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃ :=
    R.later.β₂_lt.trans_le (min_le_left _ _)
  -- the errors slot
  have heu := h.errorsUp_le R.stage R.later.circle R.later.excl
  change _ ≤ min _ (posOr_VAL3 _) at heu
  rw [posOr_eq_VAL3 (chainErrCap_pos_RGC hθ hθs he hΔ)] at heu
  have heu' := heu.trans (min_le_right _ _)
  -- the section slot
  have hsu := h.sectionUp_le R.stage R.later.circle R.later.excl R.later.err.co
  change _ ≤ min _ (posOr_VAL3 _) at hsu
  rw [posOr_eq_VAL3 (chainSectionCap_pos_RGC hθ he hΔ)] at hsu
  -- the splitting slots
  have hpu := h.splitUp_le R.stage R.later.circle R.later.excl R.later.err R.later.scale
  change _ ≤ min _ (posOr_VAL3 _) at hpu
  rw [posOr_eq_VAL3 (lt_min hη₁ hη₀₁)] at hpu
  have hqu := h.β₁Up_le R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b
  change _ ≤ min _ (posOr_VAL3 _) at hqu
  rw [posOr_eq_VAL3 (lt_min hη₁ (lt_min hη₀₁ hη₀₂))] at hqu
  -- the lower slot `T₀Low`
  have htu := h.T₀Low_ge R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁
  change max _ (max _ (max _ _)) ≤ _ at htu
  have hT₀ : T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ ≤ R.later.split.T₀ := (le_max_right _ _).trans R.later.T₀_ge
  simp only [max_le_iff] at htu
  obtain ⟨-, htσ, htL₁, htL₂⟩ := htu
  -- `β₃ < 1`
  have hl := h.lc18_le
  change _ ≤ min _ 1 at hl
  refine ⟨R.later.β₃_lt.trans_le (hl.trans (min_le_right _ _)), by linarith [hβ₂.trans_le hbuσ],
    (hβ₂.trans_le hbuη).le, (hγ.trans_le hcuγ).le, (hγc.trans_le hcuγ).le, (hγc.trans_le hcu1).le,
    (hβc.trans_le hcuη).le, ?_, (R.later.μ_lt.trans_le (min_le_right _ _)).trans_le
      (hsu.trans (min_le_right _ _)),
    (R.later.b_lt.trans_le (min_le_left _ _)).trans_le (hpu.trans (min_le_right _ _)),
    (R.later.β₁_lt.trans_le (min_le_left _ _)).trans_le (hqu.trans (min_le_right _ _)),
    htσ.trans hT₀, htL₁.trans hT₀, htL₂.trans hT₀⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (R.later.qe_lt.trans_le (min_le_right _ _)).trans_le heu'
  · exact (R.later.qs_lt.trans_le (min_le_right _ _)).trans_le heu'
  · exact (R.later.ve_lt.trans_le (min_le_right _ _)).trans_le heu'
  · exact R.later.ε_lt.trans_le heu'
  · exact R.later.ζ_lt.trans_le heu'
  · exact (R.later.ε₀_lt.trans_le (min_le_right _ _)).trans_le heu'

end DifferentialGeometry.Geometry.Collapse
