import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Bounds
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Tail.Scale

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

omit [Nontrivial V] in
theorem kochLammTailCylinder_le {R : ℝ} {S : Set V} (c : V)
    (hS : S ⊆ Metric.ball c R) :
    kochLammTailMeasure (V := V) R S ≤
      (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder c R) := by
  unfold kochLammTailMeasure kochLammVolume kochLammLateCylinder
  rw [Measure.prod_restrict]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) hS) le_rfl

omit [Nontrivial V] in
theorem kochLammTailTerm_le (R : ℝ) (S : Set V) :
    kochLammTailMeasure (V := V) R S ≤ kochLammTermMeasure (V := V) (R ^ 2) := by
  unfold kochLammTailMeasure kochLammTermMeasure
  rw [Measure.prod_restrict, Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammPieceSource_memLp {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    MemLp f (kochLammQ V) (kochLammTailMeasure (V := V) R S) :=
  (kochLammLateSource_memLp (V := V) h c hR hRT).mono_measure
    (kochLammTailCylinder_le (V := V) c hS)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammPieceSource_integral_rpow_le {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V
        ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammQReal V) ≤
      (kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hq : 0 < kochLammQReal V := (kochLammQ_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (kochLammQReal V)) μ := by
    simpa only [kochLammQReal_ofReal] using
      (kochLammPieceSource_memLp (V := V) h c hR hRT hS)
  have hfactor := realLpFactor_eq hq hf
  have hnorm : eLpNorm f (kochLammQ V) μ ≤
      (kochLammLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) :=
    (eLpNorm_mono_measure f (kochLammTailCylinder_le (V := V) c hS)).trans
      (kochLammLateSource_norm (V := V) h c hR hRT)
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : kochLammLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (kochLammLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [kochLammQReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [kochLammLqScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

def kochLammLatePiece0 (R : ℝ) (f : ℝ × V → F) (x : V) (S : Set V) : F :=
  ∫ z : ℝ × V, kochLammTermKernel (R ^ 2) x z • f z
    ∂kochLammTailMeasure (V := V) R S

omit [CompleteSpace F] in
theorem kochLammLatePiece_holder {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    ‖kochLammLatePiece0 R f x S‖ ≤
      (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) *
        (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V
          ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammQReal V) := by
  let μ := kochLammTailMeasure (V := V) R S
  have hk : MemLp (kochLammTermKernel (R ^ 2) x)
      (ENNReal.ofReal (kochLammQDual V)) μ :=
    (kochLammTermKernel_memLp (V := V) (t := R ^ 2) x).mono_measure
      (kochLammTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (kochLammQReal V)) μ := by
    simpa only [kochLammQReal_ofReal] using
      (kochLammPieceSource_memLp (V := V) h c hR hRT hS)
  simpa only [kochLammLatePiece0, kochLammTermTailPow, μ] using
    (integral_holder (kochLammQ_holder (V := V))
      (kochLammTermKernel (R ^ 2) x) f hk hf)

omit [CompleteSpace F] in
theorem kochLammLatePiece_norm {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖kochLammLatePiece0 R f x S‖ ≤
      Real.exp (-(k ^ 2) / 4) * (kochLammLateTailC V * (A_q : ℝ)) := by
  have hkern := kochLammTailKernel_integral_rpow_le (V := V) hR hk x hSm hfar
  have hsrc := kochLammPieceSource_integral_rpow_le (V := V) h c hR hRT hS
  have hhold := kochLammLatePiece_holder (V := V) h x c hR hRT hS
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < kochLammLateTailC V := by
    unfold kochLammLateTailC kochLammTailRoot
    exact Real.rpow_pos_of_pos (kochLammTailCore_pos (V := V) one_pos) _
  calc
    ‖kochLammLatePiece0 R f x S‖ ≤
        (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ kochLammQReal V
            ∂kochLammTailMeasure (V := V) R S) ^ (1 / kochLammQReal V) := hhold
    _ ≤ (Real.exp (-(k ^ 2) / 4) *
          (kochLammLateTailC V * kochLammLqScaleR (V := V) R)) *
        ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.le hs.le))
    _ = Real.exp (-(k ^ 2) / 4) *
        (kochLammLateTailC V * (A_q : ℝ)) := by
      calc
        Real.exp (-(k ^ 2) / 4) *
              (kochLammLateTailC V * kochLammLqScaleR (V := V) R) *
              ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            Real.exp (-(k ^ 2) / 4) * kochLammLateTailC V *
              (kochLammLqScaleR (V := V) R *
                (kochLammLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = Real.exp (-(k ^ 2) / 4) *
            (kochLammLateTailC V * (A_q : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
