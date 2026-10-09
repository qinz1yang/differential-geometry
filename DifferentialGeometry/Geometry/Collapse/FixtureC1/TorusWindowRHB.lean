import DifferentialGeometry.Geometry.Collapse.RhoWindowRHB
import DifferentialGeometry.Geometry.Collapse.RegisterSmallWRHB
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusBallVolumeRHB
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterPacket

/-!
# LPA01's window on the flat torus (lane S-RHOBOUNDS, finding F-REG-1, G2)

The window `ρ_bounds` at `ρ ≡ 1` on the flat torus of periods `(N, N, f)` (fibre `f = L₂`):

* `torWindowOne_of_numbers_RHB`: the window holds when `4 f ≤ w`, `w' < f`, `w' < 729/1000`,
  `L₀, L₁ ≥ 1`  (left half from the slab bound `vol B(p,1) ≤ 4 f`, right half from the box bound
  `vol B(p,r) ≥ 0.729 · min(r,f) · r²`);
* necessary conditions on the fibre at `ρ ≡ 1`: the right half forces `L₂ > w'/8`
  (`torWindow_right_fibre_RHB`), the left half fails when `L₂ ≥ (11/4) w`
  (`torWindow_left_fails_RHB`): the fibre must lie in `(w'/8, (11/4) w)`, and `[w', w/4]` suffices;
* the register's `w'` satisfies `w' < w β₂³/10³⁶` (`ClosedLaterV4.wPrime_lt_w_beta2_cube_RHB`), so
  with the CORRECTED fibre `f = min β₂ (w/4)` the window holds at EVERY register
  (`ClosedLaterV4.torWindowF_RHB`) while `f ≤ β₂` and the plane periods are those of the existing
  fixture (`torRegPeriodsF_L2_RHB`, `torRegPeriodsF_plane_RHB`); the circle packet of the
  existing fixture is rebuilt on it (`torRegPacketsF_RHB`);
* for the EXISTING fixture (fibre `β₂`): the window holds when `w ≥ 4 β₂`
  (`ClosedLaterV4.torWindowOld_holds_RHB`) and FAILS when `w ≤ (3/10) β₂`
  (`ClosedLaterV4.torWindowOld_fails_RHB`); the register imposes only upper bounds on `w`, and
  registers with `w ≤ (3/10) β₂` exist (`exists_register_torWindowOld_fails_RHB`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The numeric window on a torus -/

/-- **The window at `ρ ≡ 1` on a flat torus, from numbers.** -/
theorem torWindowOne_of_numbers_RHB (Λ : TorusPeriods_FXC1) {w w' : ℝ} (hw : 0 < w)
    (hwc : w < 4 * Real.pi / 3) (hw' : 0 < w') (hw'1 : w' < 729 / 1000)
    (hw'f : w' < Λ.L 2) (hN0 : 1 ≤ Λ.L 0) (hN1 : 1 ≤ Λ.L 1) (hvol : 4 * Λ.L 2 ≤ w)
    (p : Tor_FXC1 Λ) :
    firstVolumeScale (torMetric_FXC1 Λ) p w / 2 < 1 ∧
      1 < 2 * firstVolumeScale (torMetric_FXC1 Λ) p w' := by
  have hw'c : w' < 4 * Real.pi / 3 := by
    have := Real.pi_gt_three
    linarith
  obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ p
  have hf := Λ.pos 2
  refine (rhoWindowOne_iff_RHB (g := torMetric_FXC1 Λ) (p := torPi_FXC1 Λ x)
    finrank_euclideanSpace_fin hw hwc hw' hw'c).mpr ⟨⟨1, one_pos, by norm_num, ?_⟩, ?_⟩
  · have h := ballVolume_torMetric_toReal_le_slab_RHB Λ (torPi_FXC1 Λ x) one_pos
    nlinarith
  · intro r hr hr2
    by_cases hrf : r ≤ Λ.L 2
    · have h := ballVolume_torMetric_ge_RHB Λ x hr hr le_rfl (by linarith) (by linarith)
        (by linarith)
      have hr3 : 0 < r ^ 3 := by positivity
      nlinarith
    · have hrf' : Λ.L 2 ≤ r := (not_le.mp hrf).le
      have h := ballVolume_torMetric_ge_RHB Λ x hr hf hrf' (by linarith) (by linarith)
        (by linarith)
      have hr2' : 0 < r ^ 2 := by positivity
      have h1 : w' * r ≤ w' * (1 / 2) := mul_le_mul_of_nonneg_left hr2 hw'.le
      have h2 : w' * r < 729 / 1000 * Λ.L 2 := by linarith
      calc w' * r ^ 3 = (w' * r) * r ^ 2 := by ring
        _ < 729 / 1000 * Λ.L 2 * r ^ 2 := mul_lt_mul_of_pos_right h2 hr2'
        _ ≤ _ := h

/-- **Necessary for the right half**: if `1 < 2 · firstVolumeScale w'` at `p`, the fibre exceeds
`w'/8` (the ball of radius `1/2` has volume at most `4 (1/2)² L₂`). A fibre that is too thin
misses the window as well. -/
theorem torWindow_right_fibre_RHB (Λ : TorusPeriods_FXC1) {w' : ℝ} (hw' : 0 < w')
    (hw'c : w' < 4 * Real.pi / 3) (p : Tor_FXC1 Λ)
    (hwin : 1 < 2 * firstVolumeScale (torMetric_FXC1 Λ) p w') : w' / 8 < Λ.L 2 := by
  have h1 := (lt_firstVolumeScale_iff_RHB (g := torMetric_FXC1 Λ) (p := p) (c := 1 / 2)
    finrank_euclideanSpace_fin hw' hw'c).mp (by linarith) (1 / 2) (by norm_num) le_rfl
  have h2 := ballVolume_torMetric_toReal_le_slab_RHB Λ p (r := 1 / 2) (by norm_num)
  nlinarith

/-- **Sufficient for the failure of the left half**: a fibre `L₂ ≥ (11/4) w` (and `w ≤ 7/10`,
`L₀, L₁ ≥ 2`) gives `firstVolumeScale w ≥ 2` at every point. -/
theorem torWindow_left_fails_RHB (Λ : TorusPeriods_FXC1) {w : ℝ} (hw : 0 < w)
    (hwc : w < 4 * Real.pi / 3) (hw7 : w ≤ 7 / 10) (hN0 : 2 ≤ Λ.L 0) (hN1 : 2 ≤ Λ.L 1)
    (hf : 11 / 4 * w ≤ Λ.L 2) (p : Tor_FXC1 Λ) :
    ¬ (firstVolumeScale (torMetric_FXC1 Λ) p w / 2 < 1) := by
  obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ p
  have hf0 := Λ.pos 2
  have hlt := (lt_firstVolumeScale_iff_RHB (g := torMetric_FXC1 Λ) (p := torPi_FXC1 Λ x)
    (c := 2) finrank_euclideanSpace_fin hw hwc).mpr ?_
  · intro h
    linarith
  · intro r hr hr2
    by_cases hrf : r ≤ Λ.L 2
    · have h := ballVolume_torMetric_ge_RHB Λ x hr hr le_rfl (by linarith) (by linarith)
        (by linarith)
      have hr3 : 0 < r ^ 3 := by positivity
      nlinarith
    · have hrf' : Λ.L 2 ≤ r := (not_le.mp hrf).le
      have h := ballVolume_torMetric_ge_RHB Λ x hr hf0 hrf' (by linarith) (by linarith)
        (by linarith)
      have hr2' : 0 < r ^ 2 := by positivity
      have h1 : w * r ≤ w * 2 := mul_le_mul_of_nonneg_left hr2 hw.le
      have h2 : w * r < 729 / 1000 * Λ.L 2 := by linarith
      calc w * r ^ 3 = (w * r) * r ^ 2 := by ring
        _ < 729 / 1000 * Λ.L 2 * r ^ 2 := mul_lt_mul_of_pos_right h2 hr2'
        _ ≤ _ := h

/-! ### The torus of a register: existing fibre `β₂` and corrected fibre `min β₂ (w/4)` -/

section Register

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} {st : ClosedStage D}
  (L : ClosedLaterV4 D T st)

/-- The corrected flat torus of a register: periods `(N, N, min β₂ (w/4))`. -/
def torRegPeriodsF_RHB (β₂ w : ℝ) (hβ₂ : 0 < β₂) (hw : 0 < w) : TorusPeriods_FXC1 where
  L := ![(torRegSide_OFC β₂ : ℝ), (torRegSide_OFC β₂ : ℝ), min β₂ (w / 4)]
  pos := by
    have hN : (0 : ℝ) < torRegSide_OFC β₂ := Nat.cast_pos.mpr (torRegSide_pos_OFC hβ₂)
    intro i
    fin_cases i
    · exact hN
    · exact hN
    · exact lt_min hβ₂ (by positivity)

section Periods

variable {β₂ w : ℝ} (hβ₂ : 0 < β₂) (hw : 0 < w)

theorem torRegPeriodsF_L0_RHB :
    (torRegPeriodsF_RHB β₂ w hβ₂ hw).L 0 = (torRegSide_OFC β₂ : ℝ) * 1 := by
  simp [torRegPeriodsF_RHB]

theorem torRegPeriodsF_L1_RHB :
    (torRegPeriodsF_RHB β₂ w hβ₂ hw).L 1 = (torRegSide_OFC β₂ : ℝ) * 1 := by
  simp [torRegPeriodsF_RHB]

/-- The corrected fibre is at most `β₂` (the circle stage's `L₂ ≤ R β₂` at `R = 1`). -/
theorem torRegPeriodsF_L2_RHB : (torRegPeriodsF_RHB β₂ w hβ₂ hw).L 2 ≤ 1 * β₂ := by
  simp [torRegPeriodsF_RHB]

theorem torRegPeriodsF_L2_eq_RHB :
    (torRegPeriodsF_RHB β₂ w hβ₂ hw).L 2 = min β₂ (w / 4) := by
  simp [torRegPeriodsF_RHB]

theorem torRegPeriodsF_plane_RHB :
    8 * 1 / β₂ ≤ planePeriod_FXC1 (torRegPeriodsF_RHB β₂ w hβ₂ hw) := by
  simp only [planePeriod_FXC1, torRegPeriodsF_RHB, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, min_self, mul_one]
  exact Nat.le_ceil _

end Periods

/-- **The window holds on the corrected torus at EVERY register**: `w' < w β₂³/10³⁶` is far below
the fibre `min β₂ (w/4)`. -/
theorem ClosedLaterV4.torWindowF_RHB (p : Tor_FXC1 (torRegPeriodsF_RHB L.excl.β₂ L.scale.w
    L.β₂_pos L.w_pos)) :
    firstVolumeScale (torMetric_FXC1 (torRegPeriodsF_RHB L.excl.β₂ L.scale.w L.β₂_pos L.w_pos))
        p L.scale.w / 2 < 1 ∧
      1 < 2 * firstVolumeScale
        (torMetric_FXC1 (torRegPeriodsF_RHB L.excl.β₂ L.scale.w L.β₂_pos L.w_pos)) p
        (closedWPrime L.scale) := by
  have hβ := L.β₂_pos
  have hβ1 : L.excl.β₂ < 1 := L.β₂_lt.trans_le ((min_le_right _ _).trans (by norm_num))
  have hw := L.w_pos
  have hwp := closedWPrime_pos_RHB L.scale L.Λ_pos hw
  have hsharp := L.wPrime_lt_w_beta2_cube_RHB
  have hcube := L.wPrime_lt_beta2_cube_RHB
  have hb3 : L.excl.β₂ ^ 3 < 1 := pow_lt_one₀ hβ.le hβ1 (by norm_num)
  have hf1 : closedWPrime L.scale < L.excl.β₂ := by
    have : L.excl.β₂ ^ 3 ≤ L.excl.β₂ := by nlinarith [sq_nonneg L.excl.β₂, mul_pos hβ hβ]
    have h36 : L.excl.β₂ ^ 3 / 10 ^ 36 ≤ L.excl.β₂ ^ 3 := by
      have : 0 ≤ L.excl.β₂ ^ 3 := by positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hf2 : closedWPrime L.scale < L.scale.w / 4 := by
    have h1 : L.scale.w * L.excl.β₂ ^ 3 / 10 ^ 36 ≤ L.scale.w / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_pos hw (show 0 < L.excl.β₂ ^ 3 by positivity)]
    linarith
  have hN : (1 : ℝ) ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := by
    have h8 : 8 / L.excl.β₂ ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := Nat.le_ceil _
    have : 1 ≤ 8 / L.excl.β₂ := by
      rw [le_div_iff₀ hβ]; linarith
    linarith
  refine torWindowOne_of_numbers_RHB _ hw L.w_lt_unitBall_RHB hwp ?_ ?_ ?_ ?_ ?_ p
  · linarith
  · rw [torRegPeriodsF_L2_eq_RHB]
    exact lt_min hf1 hf2
  · rw [torRegPeriodsF_L0_RHB]; linarith
  · rw [torRegPeriodsF_L1_RHB]; linarith
  · rw [torRegPeriodsF_L2_eq_RHB]
    have := min_le_right L.excl.β₂ (L.scale.w / 4)
    linarith

/-! ### The existing fixture (fibre `β₂`): the window holds iff `w` is not too small -/

/-- **The existing fixture's window HOLDS when `w ≥ 4 β₂`.** -/
theorem ClosedLaterV4.torWindowOld_holds_RHB (hw4 : 4 * L.excl.β₂ ≤ L.scale.w)
    (p : Tor_FXC1 (torRegPeriods_OFC L.excl.β₂ L.β₂_pos)) :
    firstVolumeScale (torMetric_FXC1 (torRegPeriods_OFC L.excl.β₂ L.β₂_pos)) p L.scale.w / 2
        < 1 ∧
      1 < 2 * firstVolumeScale (torMetric_FXC1 (torRegPeriods_OFC L.excl.β₂ L.β₂_pos)) p
        (closedWPrime L.scale) := by
  have hβ := L.β₂_pos
  have hβ1 : L.excl.β₂ < 1 := L.β₂_lt.trans_le ((min_le_right _ _).trans (by norm_num))
  have hw := L.w_pos
  have hwp := closedWPrime_pos_RHB L.scale L.Λ_pos hw
  have hcube := L.wPrime_lt_beta2_cube_RHB
  have hb3 : L.excl.β₂ ^ 3 < 1 := pow_lt_one₀ hβ.le hβ1 (by norm_num)
  have hf1 : closedWPrime L.scale < L.excl.β₂ := by
    have : L.excl.β₂ ^ 3 ≤ L.excl.β₂ := by nlinarith [sq_nonneg L.excl.β₂, mul_pos hβ hβ]
    have h36 : L.excl.β₂ ^ 3 / 10 ^ 36 ≤ L.excl.β₂ ^ 3 := by
      have : 0 ≤ L.excl.β₂ ^ 3 := by positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hN : (1 : ℝ) ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := by
    have h8 : 8 / L.excl.β₂ ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := Nat.le_ceil _
    have : 1 ≤ 8 / L.excl.β₂ := by
      rw [le_div_iff₀ hβ]; linarith
    linarith
  refine torWindowOne_of_numbers_RHB _ hw L.w_lt_unitBall_RHB hwp ?_ ?_ ?_ ?_ ?_ p
  · linarith
  · simpa [torRegPeriods_OFC] using hf1
  · simpa [torRegPeriods_OFC] using hN
  · simpa [torRegPeriods_OFC] using hN
  · simpa [torRegPeriods_OFC] using hw4

/-- **The existing fixture's window FAILS when `w ≤ (3/10) β₂`**: the left half
`firstVolumeScale w / 2 < 1` is false at every point (the register imposes only upper bounds on
`w`: `w_lt`). -/
theorem ClosedLaterV4.torWindowOld_fails_RHB (hw3 : L.scale.w ≤ 3 / 10 * L.excl.β₂)
    (p : Tor_FXC1 (torRegPeriods_OFC L.excl.β₂ L.β₂_pos)) :
    ¬ (firstVolumeScale (torMetric_FXC1 (torRegPeriods_OFC L.excl.β₂ L.β₂_pos)) p L.scale.w / 2
        < 1) := by
  have hβ := L.β₂_pos
  have hβ6 : L.excl.β₂ < 1 / 10 ^ 6 := L.β₂_lt.trans_le (min_le_right _ _)
  have hN : (2 : ℝ) ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := by
    have h8 : 8 / L.excl.β₂ ≤ (torRegSide_OFC L.excl.β₂ : ℝ) := Nat.le_ceil _
    have : 2 ≤ 8 / L.excl.β₂ := by
      rw [le_div_iff₀ hβ]; linarith
    linarith
  refine torWindow_left_fails_RHB _ L.w_pos L.w_lt_unitBall_RHB (by linarith) ?_ ?_ ?_ p
  · simpa [torRegPeriods_OFC] using hN
  · simpa [torRegPeriods_OFC] using hN
  · simp only [torRegPeriods_OFC, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith

end Register

/-! ### The circle packet of the existing fixture, rebuilt on the corrected torus -/

section Packets

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} (R : ClosedRegisterV4 D T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})

/-- The periods of the corrected flat torus of the register. -/
abbrev torRegPeriodsR_RHB : TorusPeriods_FXC1 :=
  torRegPeriodsF_RHB R.later.excl.β₂ R.later.scale.w R.later.β₂_pos R.later.w_pos

/-- The corrected flat torus of the register. -/
abbrev torRegTorusF_RHB : Type :=
  Tor_FXC1 (torRegPeriodsR_RHB R)

/-- **The circle packet at the register on the corrected torus** (scale `ρ ≡ 1`): the same
construction as `torRegPackets_OFC`, with the fibre `min β₂ (w/4)` in place of `β₂`. -/
def torRegPacketsF_RHB (Kf : ℕ) (δ εr Λz : ℝ) :
    LocalChartPacketsC14 (torRegTorusF_RHB R)
      (torMetric_FXC1 (torRegPeriodsR_RHB R))
      (torMS_hmetric_FXC1 (torRegPeriodsR_RHB R))
      (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
      Λz :=
  torPacketsC14_FXC1 (torRegPeriodsR_RHB R) (R := 1) one_pos
    (R.torus_numbers_OFC hT hlc).1 (R.torus_numbers_OFC hT hlc).2.1
    (by rw [R.β_two_VAL6]; exact torRegPeriodsF_L2_RHB R.later.β₂_pos R.later.w_pos)
    (by rw [R.β_two_VAL6]; exact torRegPeriodsF_plane_RHB R.later.β₂_pos R.later.w_pos)
    (torRegSide_OFC R.later.excl.β₂) (torRegPeriodsF_L0_RHB R.later.β₂_pos R.later.w_pos)
    (torRegPeriodsF_L1_RHB R.later.β₂_pos R.later.w_pos) (R.torus_numbers_OFC hT hlc).2.2.1
    (R.torus_numbers_OFC hT hlc).2.2.2.1 (R.torus_numbers_OFC hT hlc).2.2.2.2.1
    (R.torus_numbers_OFC hT hlc).2.2.2.2.2.1 (R.torus_numbers_OFC hT hlc).2.2.2.2.2.2

include hT hlc in
/-- **Consumer: the corrected torus carries the circle packet AND LPA01's window at `ρ ≡ 1`**, at
every register of a strategy below the combined strategy. -/
theorem torRegWindowAndPacketsF_RHB (Kf : ℕ) (δ εr Λz : ℝ) :
    (∀ p : torRegTorusF_RHB R,
      firstVolumeScale (torMetric_FXC1 (torRegPeriodsR_RHB R)) p R.later.scale.w / 2 < 1 ∧
        1 < 2 * firstVolumeScale (torMetric_FXC1 (torRegPeriodsR_RHB R)) p
          (closedWPrime R.later.scale)) ∧
      Nonempty (LocalChartPacketsC14 (torRegTorusF_RHB R)
        (torMetric_FXC1 (torRegPeriodsR_RHB R))
        (torMS_hmetric_FXC1 (torRegPeriodsR_RHB R))
        (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β R.later.excl.Δ
        R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
        R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
        R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
        R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
        Λz) :=
  ⟨fun p => R.later.torWindowF_RHB p, ⟨torRegPacketsF_RHB R hT hlc Kf δ εr Λz⟩⟩

end Packets

/-- **Consumer of the failure: at every producer-threshold record `T` some register has a volume
parameter so small that the existing fixture torus (fibre `β₂`) misses LPA01's window at every
point.** -/
theorem exists_register_torWindowOld_fails_RHB (D : ClosedEarlyData) (T : ClosedThresholdsV4 D) :
    ∃ R : ClosedRegisterV4 D T, ∀ p : Tor_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos),
      ¬ (firstVolumeScale (torMetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos)) p
        R.later.scale.w / 2 < 1) := by
  obtain ⟨st⟩ := exists_closedStage D
  obtain ⟨la, hla⟩ := exists_closedLaterV4_smallW_RHB D T st
  exact ⟨⟨st, la⟩, fun p => la.torWindowOld_fails_RHB hla p⟩

end DifferentialGeometry.Geometry.Collapse
