import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

def linearLiftTimeHorizon (c M : ℝ) : ℝ :=
  min 1 (min ((1 - c) / (2 * (c + 1))) ((1 - c) ^ 2 / (64 * (M + 1) ^ 2)))

theorem linearLiftTimeHorizon_le_one {c M : ℝ} : linearLiftTimeHorizon c M ≤ 1 :=
  min_le_left _ _

theorem linearLiftTimeHorizon_le_secondOrderCoefficient {c M : ℝ} :
    linearLiftTimeHorizon c M ≤ (1 - c) / (2 * (c + 1)) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem linearLiftTimeHorizon_le_firstOrderAction {c M : ℝ} :
    linearLiftTimeHorizon c M ≤ (1 - c) ^ 2 / (64 * (M + 1) ^ 2) :=
  le_trans (min_le_right _ _) (min_le_right _ _)

theorem linearLiftTimeHorizon_pos {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hM : 0 ≤ M) : 0 < linearLiftTimeHorizon c M := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hc : (0 : ℝ) < c + 1 := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

theorem linearLiftTimeHorizon_mono {c c' M M' : ℝ} (hc0 : 0 ≤ c) (hc1' : c' < 1)
    (hM : 0 ≤ M) (hcc : c ≤ c') (hMM : M ≤ M') :
    linearLiftTimeHorizon c' M' ≤ linearLiftTimeHorizon c M := by
  have h1c' : (0 : ℝ) ≤ 1 - c' := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hM1' : (0 : ℝ) < M' + 1 := by linarith
  refine min_le_min le_rfl (min_le_min ?_ ?_)
  · have hden : (0 : ℝ) < 2 * (c + 1) := by linarith
    have hden' : (0 : ℝ) < 2 * (c' + 1) := by linarith
    rw [div_le_div_iff₀ hden' hden]
    nlinarith
  · have hd : (0 : ℝ) < 64 * (M + 1) ^ 2 := by positivity
    have hd' : (0 : ℝ) < 64 * (M' + 1) ^ 2 := by positivity
    rw [div_le_div_iff₀ hd' hd]
    have h1 : (1 - c') ^ 2 ≤ (1 - c) ^ 2 := by nlinarith
    have h2 : 64 * (M + 1) ^ 2 ≤ 64 * (M' + 1) ^ 2 := by nlinarith
    exact mul_le_mul h1 h2 hd.le (sq_nonneg _)

theorem lift_small_arith {c M T C N : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ linearLiftTimeHorizon c M)
    (hCc : C ≤ c)
    (hN0 : 0 ≤ N) (hN : N ≤ M * Real.sqrt T) :
    C * (1 + T) + 2 * Real.sqrt (1 + T) * N < 1 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hT1 : T ≤ 1 := hTle.trans linearLiftTimeHorizon_le_one
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hTa : T ≤ (1 - c) / (2 * (c + 1)) := hTle.trans linearLiftTimeHorizon_le_secondOrderCoefficient
  have hcT : c * T ≤ (1 - c) / 2 := by
    have hden : (0 : ℝ) < 2 * (c + 1) := by linarith
    rw [le_div_iff₀ hden] at hTa
    nlinarith
  have hq : Real.sqrt (1 + T) ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + T ≤ (3 / 2 : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  have hTb : T ≤ (1 - c) ^ 2 / (64 * (M + 1) ^ 2) :=
    hTle.trans linearLiftTimeHorizon_le_firstOrderAction
  have hsq : ((1 - c) / (8 * (M + 1))) ^ 2 = (1 - c) ^ 2 / (64 * (M + 1) ^ 2) := by
    rw [div_pow, mul_pow]
    norm_num
  have hs : Real.sqrt T ≤ (1 - c) / (8 * (M + 1)) := by
    have h := Real.sqrt_le_sqrt (hTb.trans_eq hsq.symm)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs' : Real.sqrt T * (8 * (M + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ (by linarith : (0 : ℝ) < 8 * (M + 1))]
    exact hs
  have hfirst : Real.sqrt (1 + T) * N ≤ 3 / 2 * (M * Real.sqrt T) :=
    mul_le_mul hq hN hN0 (by norm_num)
  have hthird : 3 * (M * Real.sqrt T) ≤ 3 * (1 - c) / 8 := by nlinarith
  have hCT : C * T ≤ c * T := mul_le_mul_of_nonneg_right hCc hT.le
  rw [show C * (1 + T) = C + C * T from by ring]
  linarith

theorem norm_toLp_le_bd {T : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A : ℝ → Z} (hA : MemLp A 2 (timeMeasure T)) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ M) :
    ‖hA.toLp A‖ ≤ M * Real.sqrt T := by
  rw [Lp.norm_toLp]
  have hle := eLpNorm_le_of_ae_bound (μ := timeMeasure T) (p := 2) hbd
  refine le_trans (ENNReal.toReal_mono ?_ hle) ?_
  · exact ENNReal.mul_ne_top
      (by rw [timeMeasure_univ]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness))
      ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_mul, timeMeasure_univ,
      show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
      toReal_ofReal_rpow_half, ENNReal.toReal_ofReal hM]
    exact le_of_eq (mul_comm _ _)

theorem norm_le_of_affine {T L Z₀ K U V : ℝ} (hL : 0 ≤ L)
    (hU : U ≤ Real.sqrt T * K) (hV : V ≤ L * U + Real.sqrt T * Z₀) :
    V ≤ (L * K + Z₀) * Real.sqrt T := by
  nlinarith [mul_le_mul_of_nonneg_left hU hL]

theorem lift_small_toLp {T c M : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A1 : ℝ → Z} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ linearLiftTimeHorizon c M)
    (hnorm : ‖hA1.toLp A1‖ ≤ M * Real.sqrt T) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_small_arith hc0 hc1 hM hT hTle hC2 (norm_nonneg _) hnorm

theorem lift_small_of_bd {T c M : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A1 : ℝ → Z} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ linearLiftTimeHorizon c M)
    (hbd : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ M) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_small_toLp hA1 hC2 hc0 hc1 hM hT hTle (norm_toLp_le_bd hA1 hM hbd)

theorem lift_smallness {T c M : ℝ} {ZHi ZLo : Type*}
    [NormedAddCommGroup ZHi] [NormedAddCommGroup ZLo]
    {A1Hi : ℝ → ZHi} (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    {A1Lo : ℝ → ZLo} (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    {C2Hi C2Lo : ℝ≥0} (hC2Hi : (C2Hi : ℝ) ≤ c) (hC2Lo : (C2Lo : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ linearLiftTimeHorizon c M)
    (hHi : ‖hA1Hi.toLp A1Hi‖ ≤ M * Real.sqrt T)
    (hLo : ‖hA1Lo.toLp A1Lo‖ ≤ M * Real.sqrt T) :
    ((C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1) ∧
      ((C2Lo : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1) :=
  ⟨lift_small_toLp hA1Hi hC2Hi hc0 hc1 hM hT hTle hHi,
    lift_small_toLp hA1Lo hC2Lo hc0 hc1 hM hT hTle hLo⟩

theorem lift_small_two_bd {T c M : ℝ} {ZHi ZLo : Type*}
    [NormedAddCommGroup ZHi] [NormedAddCommGroup ZLo]
    {A1Hi : ℝ → ZHi} (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    {A1Lo : ℝ → ZLo} (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    {C2Hi C2Lo : ℝ≥0} (hC2Hi : (C2Hi : ℝ) ≤ c) (hC2Lo : (C2Lo : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ linearLiftTimeHorizon c M)
    (hHi : ∀ᵐ t ∂timeMeasure T, ‖A1Hi t‖ ≤ M)
    (hLo : ∀ᵐ t ∂timeMeasure T, ‖A1Lo t‖ ≤ M) :
    ((C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1) ∧
      ((C2Lo : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1) :=
  lift_smallness hA1Hi hA1Lo hC2Hi hC2Lo hc0 hc1 hM hT hTle
    (norm_toLp_le_bd hA1Hi hM hHi) (norm_toLp_le_bd hA1Lo hM hLo)

def affineLiftTimeHorizon (c Z : ℝ) : ℝ :=
  min 1 (min ((1 - c) / (4 * (c + 1))) ((1 - c) ^ 2 / (144 * (Z + 1) ^ 2)))

theorem affineLiftTimeHorizon_le_one {c Z : ℝ} : affineLiftTimeHorizon c Z ≤ 1 :=
  min_le_left _ _

theorem affineLiftTimeHorizon_pos {c Z : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hZ : 0 ≤ Z) : 0 < affineLiftTimeHorizon c Z := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hc : (0 : ℝ) < c + 1 := by linarith
  have hZ1 : (0 : ℝ) < Z + 1 := by linarith
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

theorem lift_aff_arith {c A Z T C V : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hZ : 0 ≤ Z)
    (hA : 6 * A < 1 - c)
    (hT : 0 < T) (hTle : T ≤ affineLiftTimeHorizon c Z)
    (hCc : C ≤ c) (hV0 : 0 ≤ V) (hV : V ≤ A + Real.sqrt T * Z) :
    C * (1 + T) + 2 * Real.sqrt (1 + T) * V < 1 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hZ1 : (0 : ℝ) < Z + 1 := by linarith
  have hT1 : T ≤ 1 := hTle.trans affineLiftTimeHorizon_le_one
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hTa : T ≤ (1 - c) / (4 * (c + 1)) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcT : c * T ≤ (1 - c) / 4 := by
    have hden : (0 : ℝ) < 4 * (c + 1) := by linarith
    rw [le_div_iff₀ hden] at hTa
    nlinarith
  have hq : Real.sqrt (1 + T) ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + T ≤ (3 / 2 : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  have hTb : T ≤ (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsq : ((1 - c) / (12 * (Z + 1))) ^ 2 =
      (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) := by
    rw [div_pow, mul_pow]
    norm_num
  have hs : Real.sqrt T ≤ (1 - c) / (12 * (Z + 1)) := by
    have h := Real.sqrt_le_sqrt (hTb.trans_eq hsq.symm)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs' : Real.sqrt T * (12 * (Z + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ (by linarith : (0 : ℝ) < 12 * (Z + 1))]
    exact hs
  have hzT : 3 * (Real.sqrt T * Z) ≤ (1 - c) / 4 := by nlinarith
  have hfirst : Real.sqrt (1 + T) * V ≤ 3 / 2 * V :=
    mul_le_mul_of_nonneg_right hq hV0
  have hCT : C * T ≤ c * T := mul_le_mul_of_nonneg_right hCc hT.le
  rw [show C * (1 + T) = C + C * T from by ring]
  linarith

theorem lift_aff_margin {c A Z T C V : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hZ : 0 ≤ Z)
    (hA : 6 * A ≤ (1 - c) / 2)
    (hT : 0 < T) (hTle : T ≤ affineLiftTimeHorizon c Z)
    (hCc : C ≤ c) (hV0 : 0 ≤ V) (hV : V ≤ A + Real.sqrt T * Z) :
    C * (1 + T) + 2 * Real.sqrt (1 + T) * V ≤ 1 - (1 - c) / 4 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hZ1 : (0 : ℝ) < Z + 1 := by linarith
  have hT1 : T ≤ 1 := hTle.trans affineLiftTimeHorizon_le_one
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hTa : T ≤ (1 - c) / (4 * (c + 1)) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcT : c * T ≤ (1 - c) / 4 := by
    have hden : (0 : ℝ) < 4 * (c + 1) := by linarith
    rw [le_div_iff₀ hden] at hTa
    nlinarith
  have hq : Real.sqrt (1 + T) ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + T ≤ (3 / 2 : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  have hTb : T ≤ (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsq : ((1 - c) / (12 * (Z + 1))) ^ 2 =
      (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) := by
    rw [div_pow, mul_pow]
    norm_num
  have hs : Real.sqrt T ≤ (1 - c) / (12 * (Z + 1)) := by
    have h := Real.sqrt_le_sqrt (hTb.trans_eq hsq.symm)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs' : Real.sqrt T * (12 * (Z + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ (by linarith : (0 : ℝ) < 12 * (Z + 1))]
    exact hs
  have hzT : 3 * (Real.sqrt T * Z) ≤ (1 - c) / 4 := by nlinarith
  have hfirst : Real.sqrt (1 + T) * V ≤ 3 / 2 * V :=
    mul_le_mul_of_nonneg_right hq hV0
  have hCT : C * T ≤ c * T := mul_le_mul_of_nonneg_right hCc hT.le
  rw [show C * (1 + T) = C + C * T from by ring]
  linarith

theorem lift_small_aff {T c A Z : ℝ} {Y : Type*} [NormedAddCommGroup Y]
    {A1 : ℝ → Y} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hZ : 0 ≤ Z)
    (hA : 6 * A < 1 - c)
    (hT : 0 < T) (hTle : T ≤ affineLiftTimeHorizon c Z)
    (hnorm : ‖hA1.toLp A1‖ ≤ A + Real.sqrt T * Z) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_aff_arith hc0 hc1 hZ hA hT hTle hC2 (norm_nonneg _) hnorm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
