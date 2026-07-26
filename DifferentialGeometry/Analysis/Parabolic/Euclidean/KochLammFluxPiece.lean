import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxBound
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxTailScale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLatePiece

/-!
# One far terminal piece of the Koch--Lamm flux potential

The directional first-derivative kernel is restricted to a measurable
terminal spatial piece.  Its split-Gaussian tail factor is paired with the
local `KLSource1.late_lp` estimate on one radius-scale source cylinder.  The
two exact `klLpScaleR` factors cancel after space-time Hölder.
-/

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

/-- The directional first-derivative kernel inherits the selected radial
Gaussian tail factor, including the norm of the chosen direction. -/
theorem klFluxTailKern {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (w x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
        ∂klTailMeasure (V := V) R S) ^ (1 / klPDual V) ≤
      ‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * klLpScaleR (V := V) R)) := by
  let μ := klTailMeasure (V := V) R S
  let p : ℝ := klPDual V
  have hp : 0 < p := (klP_holder (V := V)).pos
  have hμ : μ ≤ klTermMeasure (V := V) (R ^ 2) := by
    exact klTailTerm_le (V := V) R S
  have hkint : Integrable
      (fun z : ℝ × V ↦ ‖klFluxKernel (R ^ 2) w x z‖ ^ p) μ := by
    have hmLp :=
      (klFluxKernel_memLp (V := V) (sq_pos_of_pos hR) w x).mono_measure hμ
    have hm := hmLp.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hmint : Integrable
      (fun z : ℝ × V ↦ (‖w‖ * klFluxMajor (R ^ 2) x z) ^ p) μ := by
    have hmLp0 :=
      (klFluxMajor_memLp (V := V) (sq_pos_of_pos hR) x).mono_measure hμ
    have hmLp := hmLp0.const_mul ‖w‖
    have hm := hmLp.integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le,
      Real.norm_of_nonneg (norm_nonneg w),
      Real.norm_of_nonneg
        (klFluxMajor_nonneg (V := V) (R ^ 2) x _), norm_mul] using hm
  have hpoint : ∀ᵐ z ∂μ,
      ‖klFluxKernel (R ^ 2) w x z‖ ^ p ≤
        (‖w‖ * klFluxMajor (R ^ 2) x z) ^ p := by
    have hae : ∀ᵐ z ∂μ,
        ‖klFluxKernel (R ^ 2) w x z‖ ≤
          ‖w‖ * klFluxMajor (R ^ 2) x z :=
      ae_mono hμ (klFluxKernel_ae (V := V) (sq_pos_of_pos hR) w x)
    filter_upwards [hae] with z hz
    exact Real.rpow_le_rpow (norm_nonneg _) hz hp.le
  have hmass :
      (∫ z : ℝ × V, (‖w‖ * klFluxMajor (R ^ 2) x z) ^ p ∂μ) =
        ‖w‖ ^ p * klFluxTailPow (V := V) R x S := by
    simp_rw [Real.mul_rpow (norm_nonneg w)
      (klFluxMajor_nonneg (V := V) (R ^ 2) x _)]
    rw [integral_const_mul]
    unfold klFluxTailPow
    simp_rw [Real.norm_of_nonneg
      (klFluxMajor_nonneg (V := V) (R ^ 2) x _)]
  have hmono :
      (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ p ∂μ) ≤
        ‖w‖ ^ p * klFluxTailPow (V := V) R x S := by
    rw [← hmass]
    exact integral_mono_ae hkint hmint hpoint
  have hpinv : p * (1 / p) = 1 := by
    field_simp [hp.ne']
  have htailnn : 0 ≤ klFluxTailPow (V := V) R x S :=
    klFluxTailPow_nn (V := V) R x S
  calc
    (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
        ∂klTailMeasure (V := V) R S) ^ (1 / klPDual V) =
        (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ p ∂μ) ^
          (1 / p) := rfl
    _ ≤ (‖w‖ ^ p * klFluxTailPow (V := V) R x S) ^ (1 / p) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hmono (by positivity)
    _ = ‖w‖ * (klFluxTailPow (V := V) R x S) ^ (1 / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg w) p) htailnn]
      rw [← Real.rpow_mul (norm_nonneg w), hpinv, Real.rpow_one]
    _ ≤ ‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (klFluxTailC V * klLpScaleR (V := V) R)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [p] using
          (klFluxTail_fac (V := V) hR hk x hSm hfar))
        (norm_nonneg w)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The local late-flux source hypothesis supplies `MemLp` on each selected
piece contained in its spatial source ball. -/
theorem klFluxPiece_mem {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    MemLp f (klP V) (klTailMeasure (V := V) R S) :=
  (klFluxSrc_memLp (V := V) h c hR hRT).mono_measure
    (klTailCyl_le (V := V) c hS)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Quantitative source Hölder factor on one selected terminal flux piece. -/
theorem klFluxPiece_src {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    (∫ z : ℝ × V, ‖f z‖ ^ klPReal V
        ∂klTailMeasure (V := V) R S) ^ (1 / klPReal V) ≤
      (klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ) := by
  let μ := klTailMeasure (V := V) R S
  have hp : 0 < klPReal V := (klP_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (klPReal V)) μ := by
    simpa only [klPReal_ofReal] using
      (klFluxPiece_mem (V := V) h c hR hRT hS)
  have hfactor := realLpFactor_eq hp hf
  have hnorm : eLpNorm f (klP V) μ ≤
      (klLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) :=
    (eLpNorm_mono_measure f (klTailCyl_le (V := V) c hS)).trans
      (klFluxSrc_norm (V := V) h c hR hRT)
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : klLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (klLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [klPReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [klLpScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

/-- Contribution of one selected terminal spatial flux piece. -/
def klFluxPiece1 (R : ℝ) (w : V) (f : ℝ × V → F)
    (x : V) (S : Set V) : F :=
  ∫ z : ℝ × V, klFluxKernel (R ^ 2) w x z • f z
    ∂klTailMeasure (V := V) R S

omit [CompleteSpace F] in
/-- Joint space-time Hölder on one selected terminal flux piece. -/
theorem klFluxPiece_hold {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    ‖klFluxPiece1 R w f x S‖ ≤
      (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
          ∂klTailMeasure (V := V) R S) ^ (1 / klPDual V) *
        (∫ z : ℝ × V, ‖f z‖ ^ klPReal V
          ∂klTailMeasure (V := V) R S) ^ (1 / klPReal V) := by
  let μ := klTailMeasure (V := V) R S
  have hk : MemLp (klFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (klPDual V)) μ :=
    (klFluxKernel_memLp (V := V) (sq_pos_of_pos hR) w x).mono_measure
      (klTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (klPReal V)) μ := by
    simpa only [klPReal_ofReal] using
      (klFluxPiece_mem (V := V) h c hR hRT hS)
  simpa only [klFluxPiece1, μ] using
    (integral_holder (klP_holder (V := V))
      (klFluxKernel (R ^ 2) w x) f hk hf)

omit [CompleteSpace F] in
/-- Radius-independent bound for one far terminal flux piece. -/
theorem klFluxPiece_norm {T R k : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖klFluxPiece1 R w f x S‖ ≤
      ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * (Aₚ : ℝ)) := by
  have hkern := klFluxTailKern (V := V) hR hk w x hSm hfar
  have hsrc := klFluxPiece_src (V := V) h c hR hRT hS
  have hhold := klFluxPiece_hold (V := V) h w x c hR hRT hS
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ klFluxTailC V := by
    unfold klFluxTailC klFluxHalfRoot
    exact Real.rpow_nonneg
      (klFluxHalf_nonneg (V := V) one_pos) _
  calc
    ‖klFluxPiece1 R w f x S‖ ≤
        (∫ z : ℝ × V, ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂klTailMeasure (V := V) R S) ^ (1 / klPDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klPReal V
            ∂klTailMeasure (V := V) R S) ^ (1 / klPReal V) := hhold
    _ ≤ (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
          (klFluxTailC V * klLpScaleR (V := V) R))) *
        ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (norm_nonneg w)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc hs.le)))
    _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * (Aₚ : ℝ)) := by
      calc
        (‖w‖ * (Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
              (klFluxTailC V * klLpScaleR (V := V) R))) *
              ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) * klFluxTailC V *
              (klLpScaleR (V := V) R *
                (klLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
            (klFluxTailC V * (Aₚ : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
