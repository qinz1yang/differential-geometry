import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Bounds
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.TailScale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Piece

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem kochLammFluxTailKernel {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (w x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
        ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPDual V) ≤
      ‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * kochLammLpScaleR (V := V) R)) := by
  let μ := kochLammTailMeasure (V := V) R S
  let p : ℝ := kochLammPDual V
  have hp : 0 < p := (kochLammPDual_holder (V := V)).pos
  have hμ : μ ≤ kochLammTermMeasure (V := V) (R ^ 2) := by
    exact kochLammTailTerm_le (V := V) R S
  have hkint : Integrable
      (fun z : ℝ × V ↦ ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ p) μ := by
    have hmLp :=
      (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).mono_measure hμ
    have hm := hmLp.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [p, ENNReal.toReal_ofReal hp.le] using hm
  have hmint : Integrable
      (fun z : ℝ × V ↦ (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ p) μ := by
    have hmLp0 :=
      (kochLammFluxMajor_memLp (V := V) (t := R ^ 2) x).mono_measure hμ
    have hmLp := hmLp0.const_mul ‖w‖
    have hm := hmLp.integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [p, ENNReal.toReal_ofReal hp.le,
      Real.norm_of_nonneg (norm_nonneg w),
      Real.norm_of_nonneg
        (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _), norm_mul] using hm
  have hpoint : ∀ᵐ z ∂μ,
      ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ p ≤
        (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ p := by
    have hae : ∀ᵐ z ∂μ,
        ‖kochLammFluxKernel (R ^ 2) w x z‖ ≤
          ‖w‖ * kochLammFluxMajor (R ^ 2) x z :=
      ae_mono hμ (kochLammFluxKernel_ae (V := V) w x)
    filter_upwards [hae] with z hz
    exact Real.rpow_le_rpow (norm_nonneg _) hz hp.le
  have hmass :
      (∫ z : ℝ × V, (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ p ∂μ) =
        ‖w‖ ^ p * kochLammFluxTailPow (V := V) R x S := by
    simp_rw [Real.mul_rpow (norm_nonneg w)
      (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _)]
    rw [integral_const_mul]
    unfold kochLammFluxTailPow
    simp_rw [Real.norm_of_nonneg
      (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _)]
    rfl
  have hmono :
      (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ p ∂μ) ≤
        ‖w‖ ^ p * kochLammFluxTailPow (V := V) R x S := by
    rw [← hmass]
    exact integral_mono_ae hkint hmint hpoint
  have hpinv : p * (1 / p) = 1 := by
    field_simp [hp.ne']
  have htailnn : 0 ≤ kochLammFluxTailPow (V := V) R x S :=
    kochLammFluxTailPow_nn (V := V) R x S
  calc
    (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
        ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPDual V) =
        (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ p ∂μ) ^
          (1 / p) := rfl
    _ ≤ (‖w‖ ^ p * kochLammFluxTailPow (V := V) R x S) ^ (1 / p) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hmono (by positivity)
    _ = ‖w‖ * (kochLammFluxTailPow (V := V) R x S) ^ (1 / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg w) p) htailnn]
      rw [← Real.rpow_mul (norm_nonneg w), hpinv, Real.rpow_one]
    _ ≤ ‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (kochLammFluxTailC V * kochLammLpScaleR (V := V) R)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [p] using
          (kochLammFluxTail_integral_rpow_le (V := V) hR hk x hSm hfar))
        (norm_nonneg w)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammFluxPiece_mem {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    MemLp f (kochLammP V) (kochLammTailMeasure (V := V) R S) :=
  (kochLammFluxSource_memLp (V := V) h c hR hRT).mono_measure
    (kochLammTailCylinder_le (V := V) c hS)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammFluxPiece_source {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V
        ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPReal V) ≤
      (kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hp : 0 < kochLammPReal V := (kochLammPDual_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxPiece_mem (V := V) h c hR hRT hS)
  have hfactor := realLpFactor_eq hp hf
  have hnorm : eLpNorm f (kochLammP V) μ ≤
      (kochLammLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) :=
    (eLpNorm_mono_measure f (kochLammTailCylinder_le (V := V) c hS)).trans
      (kochLammFluxSource_norm (V := V) h c hR hRT)
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : kochLammLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (kochLammLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [kochLammPReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [kochLammLpScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

def kochLammFluxPiece1 (R : ℝ) (w : V) (f : ℝ × V → F)
    (x : V) (S : Set V) : F :=
  ∫ z : ℝ × V, kochLammFluxKernel (R ^ 2) w x z • f z
    ∂kochLammTailMeasure (V := V) R S

omit [CompleteSpace F] in
theorem kochLammFluxPiece_holder {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    ‖kochLammFluxPiece1 R w f x S‖ ≤
      (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
          ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPDual V) *
        (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V
          ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPReal V) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hk : MemLp (kochLammFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (kochLammPDual V)) μ :=
    (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).mono_measure
      (kochLammTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxPiece_mem (V := V) h c hR hRT hS)
  simpa only [kochLammFluxPiece1, μ] using
    (integral_holder (kochLammPDual_holder (V := V))
      (kochLammFluxKernel (R ^ 2) w x) f hk hf)

omit [CompleteSpace F] in
theorem kochLammFluxPiece_norm {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖kochLammFluxPiece1 R w f x S‖ ≤
      ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * (Aₚ : ℝ)) := by
  have hkern := kochLammFluxTailKernel (V := V) hR hk w x hSm hfar
  have hsrc := kochLammFluxPiece_source (V := V) h c hR hRT hS
  have hhold := kochLammFluxPiece_holder (V := V) h w x c hR hRT hS
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ kochLammFluxTailC V := by
    unfold kochLammFluxTailC kochLammFluxHalfRoot
    exact Real.rpow_nonneg
      (kochLammFluxHalf_nonneg (V := V) one_pos) _
  calc
    ‖kochLammFluxPiece1 R w f x S‖ ≤
        (∫ z : ℝ × V, ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammPReal V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammPReal V) := hhold
    _ ≤ (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (kochLammFluxTailC V * kochLammLpScaleR (V := V) R))) *
        ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (norm_nonneg w)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc hs.le)))
    _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * (Aₚ : ℝ)) := by
      calc
        (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
              (kochLammFluxTailC V * kochLammLpScaleR (V := V) R))) *
              ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) * kochLammFluxTailC V *
              (kochLammLpScaleR (V := V) R *
                (kochLammLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
            (kochLammFluxTailC V * (Aₚ : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
