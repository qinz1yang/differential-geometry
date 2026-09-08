import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.SteklovEnergy

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem timeL2.integral_mul_bilinear_le_of_forced_timeH1_test_identity
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (htest : ∀ w : timeH1 X T, w.init = 0 → w.toFun T = 0 →
      (∫ t, F t (u t) (w.toFun t) ∂timeMeasure T) =
        (∫ t, B (u t) (w.deriv t) ∂timeMeasure T) +
          ∫ t, ℓ t (w.toFun t) ∂timeMeasure T)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (u t) ∂timeMeasure T := by
  apply u.integral_mul_bilinear_le_of_forced_cutoff_steklov_identity F hF hCF B hB hBpos
    ℓ hζsmooth hζ hζpos hζlip
  intro s hs
  let U : ℝ → X := (Icc (0 : ℝ) T).indicator u
  let W : ℝ → X := fun t => DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s U t
  let Q : ℝ → X := fun t => s⁻¹ • (U (t + s) - U t)
  obtain ⟨w, hwi, hw, hwd, hwT⟩ :=
    exists_timeH1_cutoff_steklovAverage_timeL2 hT u s hζsmooth.contDiffOn hζ0 hζT
  have hW : MemLp W 2 (timeMeasure T) :=
    (memLp_congr_ae (timeL2.coeFn_steklovAverage s u)).mp (Lp.memLp (u.steklovAverage s))
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp u)
  have hQ : MemLp Q 2 (timeMeasure T) :=
    (((hU.comp_measurePreserving (measurePreserving_add_right volume s)).sub hU).const_smul s⁻¹).restrict _
  have hintB (v : ℝ → X) (hv : MemLp v 2 (timeMeasure T)) :
      Integrable (fun t => B (u t) (v t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) (Lp.memLp u) hv
  have hβ : MemLp (_root_.deriv ζ) ∞ (timeMeasure T) :=
    memLp_top_of_bound hζsmooth.continuous_deriv_one.aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hζlip)
  have hI₁ : Integrable (fun t => _root_.deriv ζ t * B (u t) (W t)) (timeMeasure T) :=
    (hintB W hW).mul_of_top_right hβ
  have hI₂ : Integrable (fun t => ζ t * B (u t) (Q t)) (timeMeasure T) :=
    (hintB Q hQ).mul_of_top_right (hζ.restrict (Icc (0 : ℝ) T))
  have hleft : (∫ t, F t (u t) (w.toFun t) ∂timeMeasure T) =
      ∫ t, ζ t * F t (u t) (W t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht, map_smul]
    rfl
  have hmass : (∫ t, B (u t) (w.deriv t) ∂timeMeasure T) =
      (∫ t, _root_.deriv ζ t * B (u t) (W t) ∂timeMeasure T) +
        ∫ t, ζ t * B (u t) (Q t) ∂timeMeasure T := by
    rw [← integral_add hI₁ hI₂]
    apply integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht, map_add, map_smul, map_smul]
    rfl
  have hsource : (∫ t, ℓ t (w.toFun t) ∂timeMeasure T) =
      ∫ t, ζ t * ℓ t (W t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht, map_smul]
    rfl
  have h := htest w hwi hwT
  rw [hleft, hmass, hsource] at h
  exact h

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
