import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateBound
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammTailScale

/-!
# One far terminal piece of the Koch--Lamm ordinary-source potential

An arbitrary measurable spatial piece is paired with two independent facts:
it lies in one source cylinder, and it is far from the observation point.
Joint space-time Hölder then combines the local source bound with the
Gaussian tail factor.  No cover or shell decomposition is chosen here.
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

omit [Nontrivial V] in
/-- A selected terminal piece inside a radius-`R` ball has measure bounded by
the corresponding late source cylinder. -/
theorem klTailCyl_le {R : ℝ} {S : Set V} (c : V)
    (hS : S ⊆ Metric.ball c R) :
    klTailMeasure (V := V) R S ≤
      (klVolume : Measure (ℝ × V)).restrict (klLateCyl c R) := by
  unfold klTailMeasure klVolume klLateCyl
  rw [Measure.prod_restrict]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) hS) le_rfl

omit [Nontrivial V] in
/-- Every selected terminal piece is contained in the full terminal slab. -/
theorem klTailTerm_le (R : ℝ) (S : Set V) :
    klTailMeasure (V := V) R S ≤ klTermMeasure (V := V) (R ^ 2) := by
  unfold klTailMeasure klTermMeasure
  rw [Measure.prod_restrict, Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The local late-source hypothesis supplies `MemLp` on every selected
piece contained in its spatial ball. -/
theorem klPieceSrc_mem {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    MemLp f (klQ V) (klTailMeasure (V := V) R S) :=
  (klLateSrc_memLp (V := V) h c hR hRT).mono_measure
    (klTailCyl_le (V := V) c hS)

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Quantitative source Hölder factor on one selected terminal piece. -/
theorem klPieceSrc_fac {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    (∫ z : ℝ × V, ‖f z‖ ^ klQReal V
        ∂klTailMeasure (V := V) R S) ^ (1 / klQReal V) ≤
      (klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ) := by
  let μ := klTailMeasure (V := V) R S
  have hq : 0 < klQReal V := (klQ_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klPieceSrc_mem (V := V) h c hR hRT hS)
  have hfactor := realLpFactor_eq hq hf
  have hnorm : eLpNorm f (klQ V) μ ≤
      (klLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) :=
    (eLpNorm_mono_measure f (klTailCyl_le (V := V) c hS)).trans
      (klLateSrc_norm (V := V) h c hR hRT)
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : klLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (klLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [klQReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [klLqScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

/-- Contribution of one selected terminal spatial piece. -/
def klLatePiece0 (R : ℝ) (f : ℝ × V → F) (x : V) (S : Set V) : F :=
  ∫ z : ℝ × V, klTermKernel (R ^ 2) x z • f z
    ∂klTailMeasure (V := V) R S

omit [CompleteSpace F] in
/-- Joint space-time Hölder on one selected terminal piece. -/
theorem klLatePiece_hold {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    ‖klLatePiece0 R f x S‖ ≤
      (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) *
        (∫ z : ℝ × V, ‖f z‖ ^ klQReal V
          ∂klTailMeasure (V := V) R S) ^ (1 / klQReal V) := by
  let μ := klTailMeasure (V := V) R S
  have hk : MemLp (klTermKernel (R ^ 2) x)
      (ENNReal.ofReal (klQDual V)) μ :=
    (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).mono_measure
      (klTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klPieceSrc_mem (V := V) h c hR hRT hS)
  simpa only [klLatePiece0, klTermTailPow, μ] using
    (integral_holder (klQ_holder (V := V))
      (klTermKernel (R ^ 2) x) f hk hf)

omit [CompleteSpace F] in
/-- Radius-independent bound for one far terminal piece. -/
theorem klLatePiece_norm {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    {S : Set V} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖klLatePiece0 R f x S‖ ≤
      Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ)) := by
  have hkern := klTailKern_fac (V := V) hR hk x hSm hfar
  have hsrc := klPieceSrc_fac (V := V) h c hR hRT hS
  have hhold := klLatePiece_hold (V := V) h x c hR hRT hS
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < klLateTailC V := by
    unfold klLateTailC klTailRoot
    exact Real.rpow_pos_of_pos (klTailCore_pos (V := V) one_pos) _
  calc
    ‖klLatePiece0 R f x S‖ ≤
        (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) *
          (∫ z : ℝ × V, ‖f z‖ ^ klQReal V
            ∂klTailMeasure (V := V) R S) ^ (1 / klQReal V) := hhold
    _ ≤ (Real.exp (-(k ^ 2) / 4) *
          (klLateTailC V * klLqScaleR (V := V) R)) *
        ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hkern hsrc
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.le hs.le))
    _ = Real.exp (-(k ^ 2) / 4) *
        (klLateTailC V * (A_q : ℝ)) := by
      calc
        Real.exp (-(k ^ 2) / 4) *
              (klLateTailC V * klLqScaleR (V := V) R) *
              ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            Real.exp (-(k ^ 2) / 4) * klLateTailC V *
              (klLqScaleR (V := V) R *
                (klLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = Real.exp (-(k ^ 2) / 4) *
            (klLateTailC V * (A_q : ℝ)) := by
          rw [mul_inv_cancel₀ hs.ne']
          ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
