import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Stability
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftDependence

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem quasilinear_fixed_forcing_initial_sub_norm_le
    {Acoef : Type*} [SeminormedAddCommGroup Acoef] [NormedSpace ℝ Acoef]
    {T R ρ H P : ℝ} {S : Set X} {V : Set Z}
    (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (m : Acoef →L[ℝ] Y →L[ℝ] Y) (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z)
    (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (alpha : ℝ → Z → Acoef) (reaction : ℝ → Z → Y) (offset : ℝ → X → Y)
    (f g : X) (N : ℝ → S → Y)
    (hN : ∀ᵐ t ∂(timeMeasure T), ∀ u : S,
      N t u = m (alpha t (J (f + u))) (Q (f + u)) +
        reaction t (J (f + u)) - offset t u)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
        (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
        (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
          ‖J ((u : X) - (v : X))‖)
    (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hL : ∀ F, ‖L F‖ ≤ H * ‖F‖) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (F G : timeL2 Y T)
    (hstateF : ∀ᵐ t ∂(timeMeasure T), L F t ∈ S)
    (hstateG : ∀ᵐ t ∂(timeMeasure T), L G t ∈ S)
    (hF : F =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero (L F) t))
    (hG : G =ᵐ[timeMeasure T] fun t =>
      m (alpha t (J (g + L G t))) (Q (g + L G t)) +
        reaction t (J (g + L G t)) - offset t (L G t))
    (hmeasG : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero (L G) t)) (timeMeasure T))
    {a : ℝ} (ha : 0 ≤ a) {Lalpha Lreaction : ℝ≥0}
    (halpha : ∀ᵐ t ∂(timeMeasure T), LipschitzOnWith Lalpha (alpha t) V)
    (hreaction : ∀ᵐ t ∂(timeMeasure T), LipschitzOnWith Lreaction (reaction t) V)
    (hstatef : ∀ᵐ t ∂(timeMeasure T), J (f + L G t) ∈ V)
    (hstateg : ∀ᵐ t ∂(timeMeasure T), J (g + L G t) ∈ V)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖alpha t (J (f + L G t))‖ ≤ a)
    {κ : ℝ}
    (hκ : (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P +
      2 * (C : ℝ) * ρ * P * H ≤ κ)
    (hρF : ‖F‖ ≤ ρ) (hρG : ‖G‖ ≤ ρ) (hκlt : κ < 1) :
    ‖F - G‖ ≤ (Real.sqrt T * ‖m‖ * a * ‖Q‖ +
      (‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * (H * ρ)) +
        Real.sqrt T * Lreaction) * ‖J‖) / (1 - κ) * ‖f - g‖ := by
  let NG := timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame (L G)
    hstateG hmeasG
  have hNG : NG =ᵐ[timeMeasure T] fun t =>
      m (alpha t (J (f + L G t))) (Q (f + L G t)) +
        reaction t (J (f + L G t)) - offset t (L G t) := by
    filter_upwards [timeNemyTame_ae hzero hR J hstate N A B C D hD hzeroN htame
      (L G) hstateG hmeasG, hN, hstateG] with t ht hn hgt
    rw [ht]
    simpa only [aeSetLift, dif_pos hgt] using hn ⟨L G t, hgt⟩
  have hshift := quasilinear_forcing_shift_sub_norm_le m Q J alpha reaction
    (fun t => offset t (L G t)) f g (L G) NG G ha halpha hreaction
      hstatef hstateg hbound hNG hG
  have hLG : ‖L G‖ ≤ H * ρ :=
    (hL G).trans (mul_le_mul_of_nonneg_left hρG hH)
  have hcoef : 0 ≤ ‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * (H * ρ)) +
        Real.sqrt T * Lreaction := by
    have hρ : 0 ≤ ρ := (norm_nonneg G).trans hρG
    positivity
  have hshift' : ‖NG - G‖ ≤
      (Real.sqrt T * ‖m‖ * a * ‖Q‖ +
        (‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * (H * ρ)) +
          Real.sqrt T * Lreaction) * ‖J‖) * ‖f - g‖ := by
    calc
      ‖NG - G‖ ≤ Real.sqrt T * ‖m‖ * a * ‖Q (f - g)‖ +
          (‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * ‖L G‖) +
            Real.sqrt T * Lreaction) * ‖J (f - g)‖ := hshift
      _ ≤ Real.sqrt T * ‖m‖ * a * (‖Q‖ * ‖f - g‖) +
          (‖m‖ * Lalpha * (Real.sqrt T * ‖Q g‖ + ‖Q‖ * (H * ρ)) +
            Real.sqrt T * Lreaction) * (‖J‖ * ‖f - g‖) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Q.le_opNorm _) (by positivity)
        · apply mul_le_mul _ (J.le_opNorm _) (norm_nonneg _) hcoef
          gcongr
      _ = _ := by ring
  have h := tame_fixed_forcing_sub_norm_le hzero hR J hstate N A B C D hD hzeroN
    htame L hL hH hP hpoint F G hstateF hstateG hF hmeasG hshift' hκ hρF hρG hκlt
  convert h using 1
  · ring
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
