import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusLpa02WitnessFXT
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterFamilyFXR

/-!
# LPA02 on the flat torus, part 4: the register layer (S-LPA02-TOR, G4)

Lane S-LPA02-TOR (suffix `_FXT`). The witness `torLpa02Witness_FXT` needs `4 T D ≤ δ² f V`
(`T = T₀`, `D` a diameter bound, `f` the fibre, `δ` the cone error). The register records only
`T₀ ≤ V` and `V = T.lpa02V …` (`ClosedLaterV4.V_eq`); `lpa02V` is the ONLY slot of the threshold
record that no `ClosedStrategyBelowV4` comparison reads, and it may read the register values
`β₂` (in `excl`), `w` (in `scale`), `ε₀` (in `err`) and `T₀`. So:

* `ClosedThresholdsV4.withTorusV_FXT T`: `T` with `lpa02V` replaced by
  `torLpa02V_FXT β₂ w ε₀ T₀ = T₀ + |4 T₀ D(β₂, w) / (δ(ε₀)² f(β₂, w))|`, where `f = min β₂ (w/4)` is
  the fibre of the corrected register torus `torRegPeriodsR_RHB`, `D = 2 (2 N + f)` its diameter
  bound (`N = ⌈8/β₂⌉`) and `δ(ε₀) = min(radialSmoothingConeError(ε_r/4), 1/2)/2` with
  `ε_r = min(ε₀/2, 1/8)`; it is below every `U` that `T` is below
  (`ClosedThresholdsV4.withTorusV_below_FXT`);
* `torDiam_le_FXT`: `diam T³_Λ ≤ 2 (L₀ + L₁ + L₂)`;
* **`torRegLpa02Witness_FXT`**: at EVERY register `R` of `T.withTorusV_FXT`, for EVERY `K_f`, the
  LPA02 joint witness `Lpa02WitnessV2` of the corrected register torus at the register's own
  `(Λ, w, T₀, V, e₀)` with `ε_r = ε_r(ε₀)`, `δ = δ(ε₀)` (no hypothesis).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric GC.Endpoint
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- The diameter of the flat torus is at most `2 (L₀ + L₁ + L₂)`. -/
theorem torDiam_le_FXT (Λ : TorusPeriods_FXC1) :
    Metric.diam (univ : Set (Tor_FXC1 Λ)) ≤ 2 * (Λ.L 0 + Λ.L 1 + Λ.L 2) := by
  have hL : 0 ≤ Λ.L 0 + Λ.L 1 + Λ.L 2 := by
    have := Λ.pos 0; have := Λ.pos 1; have := Λ.pos 2; linarith
  refine Metric.diam_le_of_forall_dist_le (by linarith) fun x _ y _ => ?_
  obtain ⟨a, ha, rfl⟩ := torPi_surjective_FXC1 Λ x
  obtain ⟨y', rfl⟩ := torPi_surjective_FXC1 Λ y
  obtain ⟨a', ha', ha'e⟩ := exists_mem_closedBall_torPi_eq_FXC1 Λ a
  obtain ⟨b', hb', hb'e⟩ := exists_mem_closedBall_torPi_eq_FXC1 Λ y'
  rw [← ha'e, ← hb'e]
  refine (dist_le_of_edist_le_FXC1 Λ _ _ _ (norm_nonneg _) (edist_torPi_le_FXC1 Λ a' b')).trans ?_
  rw [mem_closedBall, dist_zero_right] at ha' hb'
  calc ‖a' - b'‖ ≤ ‖a'‖ + ‖b'‖ := norm_sub_le _ _
    _ ≤ 2 * (Λ.L 0 + Λ.L 1 + Λ.L 2) := by linarith

/-- The fibre `min β₂ (w/4)` of the corrected register torus. -/
def torFibre_FXT (β₂ w : ℝ) : ℝ := min β₂ (w / 4)

/-- The diameter bound `2 (2 N + f)` of the corrected register torus, `N = ⌈8/β₂⌉`. -/
def torDiam_FXT (β₂ w : ℝ) : ℝ := 2 * (2 * (torRegSide_OFC β₂ : ℝ) + torFibre_FXT β₂ w)

/-- The `ε_r` chosen at `ε₀`. -/
def torErr_FXT (ε₀ : ℝ) : ℝ := min (ε₀ / 2) (1 / 8)

/-- The cone error `δ` chosen at `ε₀`. -/
def torCone_FXT (ε₀ : ℝ) : ℝ :=
  min (radialSmoothingConeError (torErr_FXT ε₀ / 4)) (1 / 2) / 2

/-- The enlarged `V` of the torus threshold record. -/
def torLpa02V_FXT (β₂ w ε₀ T₀ : ℝ) : ℝ :=
  T₀ + |4 * T₀ * torDiam_FXT β₂ w / (torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w)|

theorem torErr_pos_FXT {ε₀ : ℝ} (h : 0 < ε₀) : 0 < torErr_FXT ε₀ :=
  lt_min (by linarith) (by norm_num)

theorem torCone_pos_FXT {ε₀ : ℝ} (h : 0 < ε₀) : 0 < torCone_FXT ε₀ := by
  have h1 := radialSmoothingConeError_pos (θ := torErr_FXT ε₀ / 4)
    (by have := torErr_pos_FXT h; positivity)
  exact div_pos (lt_min h1 (by norm_num)) (by norm_num)

theorem torCone_lt_FXT {ε₀ : ℝ} (h : 0 < ε₀) :
    torCone_FXT ε₀ < radialSmoothingConeError (torErr_FXT ε₀ / 4) := by
  have h1 := radialSmoothingConeError_pos (θ := torErr_FXT ε₀ / 4)
    (by have := torErr_pos_FXT h; positivity)
  have h2 := min_le_left (radialSmoothingConeError (torErr_FXT ε₀ / 4)) (1 / 2)
  unfold torCone_FXT
  linarith

theorem torErr_lt_one_FXT (ε₀ : ℝ) : torErr_FXT ε₀ < 1 :=
  (min_le_right _ _).trans_lt (by norm_num)

theorem torFibre_pos_FXT {β₂ w : ℝ} (hβ : 0 < β₂) (hw : 0 < w) : 0 < torFibre_FXT β₂ w :=
  lt_min hβ (by linarith)

theorem torDiam_nonneg_FXT {β₂ w : ℝ} (hβ : 0 < β₂) (hw : 0 < w) : 0 ≤ torDiam_FXT β₂ w := by
  have := torFibre_pos_FXT hβ hw
  unfold torDiam_FXT
  positivity

/-- The two inequalities of the witness for the enlarged `V`. -/
theorem torLpa02V_spec_FXT {β₂ w ε₀ T₀ : ℝ} (hβ : 0 < β₂) (hw : 0 < w) (hε : 0 < ε₀)
    (hT : 0 < T₀) :
    T₀ ≤ torLpa02V_FXT β₂ w ε₀ T₀ ∧
      4 * T₀ * torDiam_FXT β₂ w ≤
        torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w * torLpa02V_FXT β₂ w ε₀ T₀ := by
  have hf := torFibre_pos_FXT hβ hw
  have hδ := torCone_pos_FXT hε
  have hD := torDiam_nonneg_FXT hβ hw
  have hq : 0 < torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w := by positivity
  have hA : 0 ≤ 4 * T₀ * torDiam_FXT β₂ w / (torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w) := by
    positivity
  refine ⟨le_add_of_nonneg_right (abs_nonneg _), ?_⟩
  unfold torLpa02V_FXT
  rw [abs_of_nonneg hA]
  have : torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w *
      (4 * T₀ * torDiam_FXT β₂ w / (torCone_FXT ε₀ ^ 2 * torFibre_FXT β₂ w)) =
      4 * T₀ * torDiam_FXT β₂ w := mul_div_cancel₀ _ hq.ne'
  nlinarith

/-- **The threshold record with the enlarged `lpa02V`.** -/
def ClosedThresholdsV4.withTorusV_FXT {D : ClosedEarlyData} (T : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { T with
    lpa02V := fun _ _ ex er sc _ _ T₀ => torLpa02V_FXT ex.β₂ sc.w er.co.ε₀ T₀
    T₀_le_lpa02V := fun _ _ _ _ _ _ _ _ => le_add_of_nonneg_right (abs_nonneg _) }

/-- `lpa02V` is the only slot changed, and no comparison reads it. -/
theorem ClosedThresholdsV4.withTorusV_below_FXT {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U) :
    ClosedStrategyBelowV4 T.withTorusV_FXT U := by
  exact ⟨h.lc18_le, h.circleUp_le, h.β₂Up_le, h.ΔLow_ge, h.errorsUp_le, h.sectionUp_le,
    h.lfr29W_le, h.endpointUp_le, h.σcolUp_le, h.scaleUp_le, h.wUp_le, h.splitUp_le,
    h.β₁Up_le, h.T₀Low_ge, h.LmaxLow_ge, h.tailLow_ge⟩

section Register

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
  (R : ClosedRegisterV4 D T.withTorusV_FXT)

theorem ClosedRegisterV4.V_eq_FXT :
    R.later.split.V = torLpa02V_FXT R.later.excl.β₂ R.later.scale.w R.later.err.co.ε₀
      R.later.split.T₀ :=
  R.later.V_eq

/-- All periods of the corrected register torus are at least its fibre. -/
theorem ClosedRegisterV4.torPeriods_lower_FXT :
    ∀ i, torFibre_FXT R.later.excl.β₂ R.later.scale.w ≤ (torRegPeriodsR_RHB R).L i := by
  have hβ := R.later.β₂_pos
  have hβ1 : R.later.excl.β₂ < 1 :=
    R.later.β₂_lt.trans_le ((min_le_right _ _).trans (by norm_num))
  have hN : 8 / R.later.excl.β₂ ≤ (torRegSide_OFC R.later.excl.β₂ : ℝ) := Nat.le_ceil _
  have h8 : 1 ≤ 8 / R.later.excl.β₂ := by rw [le_div_iff₀ hβ]; linarith
  have hf : torFibre_FXT R.later.excl.β₂ R.later.scale.w ≤ 1 :=
    (min_le_left _ _).trans hβ1.le
  intro i
  fin_cases i
  · simpa [torRegPeriodsR_RHB, torRegPeriodsF_RHB] using hf.trans (h8.trans hN)
  · simpa [torRegPeriodsR_RHB, torRegPeriodsF_RHB] using hf.trans (h8.trans hN)
  · simp [torRegPeriodsR_RHB, torRegPeriodsF_RHB, torFibre_FXT]

/-- **LPA02's joint witness on the corrected register torus, at every register of the enlarged
threshold record** (no hypothesis). -/
theorem ClosedRegisterV4.torRegLpa02Witness_FXT (Kf : ℕ) :
    Lpa02WitnessV2 (torRegModelF_FXR R).gX Kf R.later.scale.Λ R.later.scale.w
      (torErr_FXT R.later.err.co.ε₀) R.later.err.co.e₀ R.later.split.T₀ R.later.split.V
      (torCone_FXT R.later.err.co.ε₀) := by
  have hβ := R.later.β₂_pos
  have hw := R.later.w_pos
  have hε := R.later.ε₀_pos
  have hspec := torLpa02V_spec_FXT hβ hw hε R.later.T₀_pos_VAL6
  rw [← ClosedRegisterV4.V_eq_FXT R] at hspec
  refine torLpa02Witness_FXT (torRegPeriodsR_RHB R)
    (D := torDiam_FXT R.later.excl.β₂ R.later.scale.w) (torFibre_pos_FXT hβ hw)
    (ClosedRegisterV4.torPeriods_lower_FXT R) ?_ Kf (torErr_pos_FXT hε) (torErr_lt_one_FXT _)
    R.later.e₀_pos R.later.e₀_lt_VAL6 (torCone_pos_FXT hε) (torCone_lt_FXT hε)
    R.later.T₀_pos_VAL6 R.later.T₀_le_V_VAL6 ?_
  · refine (torDiam_le_FXT _).trans_eq ?_
    simp [torRegPeriodsR_RHB, torRegPeriodsF_RHB, torDiam_FXT, torFibre_FXT]
    ring
  · exact hspec.2

end Register

end DifferentialGeometry.Geometry.Collapse
