import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.H3Energy
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.GalerkinForcingArms
import DifferentialGeometry.Analysis.Estimates.ProductBounds

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic (zero_mem_lowerState)
open DifferentialGeometry.Analysis.Elliptic (riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (cc_partial_le_norm ccTensorBilin_symmS_symm eigenIdxFinset galerkinEnergy hs_le_jet
   iteratedCovGrad_add smoothCcToTensorHs)
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


theorem lowerScaleActions_covariantJetNorm_two_tame_bound_background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop Kr2 Kr1 Kmid : ℝ, 0 ≤ Ctop ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kmid ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
        {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient.toSection x) ≤
            Cδ ^ 2)
        {X Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
        (h5 : Real.sqrt (∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ X)
        (h4 : Real.sqrt (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Y)
        (h3 : Real.sqrt (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Z),
        ∑ q ∈ Finset.range 3,
            (‖iteratedCovGrad (I := I) g 0 2 q
                ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                    (I := I) (M := M) T)‖ +
              ‖iteratedCovGrad (I := I) g 0 2 q
                ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                    (I := I) (M := M) T)‖) ≤
          (Ctop * Cδ + Kr2 * Z + Kr1 * Z) * X +
            Kmid * (1 + Cδ) * ((1 + Y) ^ 2 * (1 + Z) ^ 2) := by
  classical
  obtain ⟨Cqa, Ka, hCqa, hKa, ha2⟩ :=
    secondOrderAction_perIndex_linear_bound (I := I) (M := M) hDim g g_bg
  obtain ⟨Cqb, Kb0, Kb1, hCqb, hKb0, hKb1, ha1⟩ :=
    firstOrderAction_perIndex_linear_bound_background (I := I) (M := M) hDim g g_bg
  have hRest : (0 : ℝ) ≤ Cqa 1 * Ka 1 + Cqa 2 * Ka 1 + Cqa 2 * Ka 2 +
      Cqb 0 * (2 * Kb0 0 + Kb1 0) +
      Cqb 1 * (Kb0 0 + Kb0 1 + Kb1 0 + Kb1 1) +
      Cqb 2 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb1 0 + Kb1 1 + Kb1 2) := by
    have t1 := mul_nonneg (hCqa 1) (hKa 1)
    have t2 := mul_nonneg (hCqa 2) (hKa 1)
    have t3 := mul_nonneg (hCqa 2) (hKa 2)
    have t4 := mul_nonneg (hCqb 0)
      (by linarith [hKb0 0, hKb1 0] : (0 : ℝ) ≤ 2 * Kb0 0 + Kb1 0)
    have t5 := mul_nonneg (hCqb 1)
      (by linarith [hKb0 0, hKb0 1, hKb1 0, hKb1 1] :
        (0 : ℝ) ≤ Kb0 0 + Kb0 1 + Kb1 0 + Kb1 1)
    have t6 := mul_nonneg (hCqb 2)
      (by linarith [hKb0 0, hKb0 1, hKb0 2, hKb1 0, hKb1 1, hKb1 2] :
        (0 : ℝ) ≤ Kb0 0 + Kb0 1 + Kb0 2 + Kb1 0 + Kb1 1 + Kb1 2)
    linarith
  refine ⟨Cqa 2, Cqa 2 * Ka 2, Cqb 2 * Kb1 1,
    Cqa 0 + Cqa 1 + (Cqa 1 * Ka 1 + Cqa 2 * Ka 1 + Cqa 2 * Ka 2 +
      Cqb 0 * (2 * Kb0 0 + Kb1 0) +
      Cqb 1 * (Kb0 0 + Kb0 1 + Kb1 0 + Kb1 1) +
      Cqb 2 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb1 0 + Kb1 1 + Kb1 2)),
    hCqa 2, mul_nonneg (hCqa 2) (hKa 2), mul_nonneg (hCqb 2) (hKb1 1),
    by linarith [hCqa 0, hCqa 1], ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ Cδ hCδ hfib X Y Z hY hZ h5 h4 h3
  have H20 := ha2 T hT hδ0 hδ_le hδg hδZ hCδ hfib 0
  have H21 := ha2 T hT hδ0 hδ_le hδg hδZ hCδ hfib 1
  have H22 := ha2 T hT hδ0 hδ_le hδg hδZ hCδ hfib 2
  have H10 := ha1 T hT hδ0 hδ_le hδg hδZ 0
  have H11 := ha1 T hT hδ0 hδ_le hδg hδZ 1
  have H12 := ha1 T hT hδ0 hδ_le hδg hδZ 2
  simp only [show (Finset.Icc 1 0 : Finset ℕ) = ∅ from rfl, Finset.sum_empty,
    add_zero] at H20
  simp only [show (Finset.Icc 1 1 : Finset ℕ) = {1} from rfl,
    Finset.sum_singleton] at H21
  simp only [show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} from rfl,
    Finset.sum_pair (show (1 : ℕ) ≠ 2 by norm_num)] at H22
  simp only [show (Finset.range 0 : Finset ℕ) = ∅ from rfl, Finset.sum_empty,
    zero_add] at H10 H11
  simp only [show (Finset.range 1 : Finset ℕ) = {0} from rfl,
    Finset.sum_singleton] at H11 H12
  simp only [show (Finset.range 2 : Finset ℕ) = {0, 1} from rfl,
    Finset.sum_pair (show (0 : ℕ) ≠ 1 by norm_num)] at H12
  simp only [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 3 = 3 from rfl,
    show (0 : ℕ) + 4 = 4 from rfl, show (1 : ℕ) + 4 = 5 from rfl,
    show (0 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) - 0 = 1 from rfl,
    show (2 : ℕ) - 0 = 2 from rfl] at H20 H21 H22 H10 H11 H12
  set J2 : ℝ := Real.sqrt (∑ j ∈ Finset.range 2,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ2def
  set J3 : ℝ := Real.sqrt (∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ3def
  set J4 : ℝ := Real.sqrt (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ4def
  set J5 : ℝ := Real.sqrt (∑ j ∈ Finset.range 5,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ5def
  have hJ2nn : (0 : ℝ) ≤ J2 := by rw [hJ2def]; positivity
  have hJ3nn : (0 : ℝ) ≤ J3 := by rw [hJ3def]; positivity
  have hJ4nn : (0 : ℝ) ≤ J4 := by rw [hJ4def]; positivity
  have hJ5nn : (0 : ℝ) ≤ J5 := by rw [hJ5def]; positivity
  have hJ23 : J2 ≤ J3 := by
    rw [hJ2def, hJ3def]; exact iteratedCovGrad_l2_window_mono (I := I) (M := M) g (by norm_num) T
  have hJ34 : J3 ≤ J4 := by
    rw [hJ3def, hJ4def]; exact iteratedCovGrad_l2_window_mono (I := I) (M := M) g (by norm_num) T
  have hJ2Z : J2 ≤ Z := le_trans hJ23 h3
  have hJ3Y : J3 ≤ Y := le_trans hJ34 h4
  have hXnn : (0 : ℝ) ≤ X := le_trans hJ5nn h5
  set P : ℝ := (1 + Y) ^ 2 * (1 + Z) ^ 2 with hPdef
  have hPnn : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ :=
    quadratic_product_bounds Y Z P hY hZ hPdef
  clear_value J2 J3 J4 J5 P
  clear hJ2def hJ3def hJ4def hJ5def hPdef
  have eZ : J3 ≤ P := le_trans h3 p1
  have eY : J4 ≤ P := le_trans h4 p2
  have e1 : (1 + J4) * J3 ≤ P :=
    le_trans (mul_le_mul (by linarith) h3 hJ3nn (by linarith)) p3
  have e2 : (1 + J4) * J4 ≤ P :=
    le_trans (mul_le_mul (by linarith) h4 hJ4nn (by linarith)) p4
  have e3 : (1 + J2) * J4 ≤ P :=
    le_trans (mul_le_mul (by linarith) h4 hJ4nn (by linarith)) p5
  have e4 : (1 + J3) * J4 ≤ P :=
    le_trans (mul_le_mul (by linarith) h4 hJ4nn (by linarith)) p5
  have e5 : (1 + J4) * (1 + J2) * J4 ≤ P :=
    le_trans (mul_three_le_mul_three (by linarith) hJ4nn (by linarith) (by linarith)
      (by linarith) (by linarith) h4) p7
  have e6 : (1 + J4) * (1 + J2) * J3 ≤ P :=
    le_trans (mul_three_le_mul_three (by linarith) hJ3nn (by linarith) (by linarith)
      (by linarith) (by linarith) h3) p8
  have e7 : (1 + J4) * (1 + J3) * J3 ≤ P :=
    le_trans (mul_three_le_mul_three (by linarith) hJ3nn (by linarith) (by linarith)
      (by linarith) (by linarith) h3) p8
  have e8 : (1 + J4) * (1 + J3) * J4 ≤ P :=
    le_trans (mul_three_le_mul_three (by linarith) hJ4nn (by linarith) (by linarith)
      (by linarith) (by linarith) h4) p7
  have e9 : (1 + J4) * (1 + J4) * J3 ≤ P :=
    le_trans (mul_three_le_mul_three (by linarith) hJ3nn (by linarith) (by linarith)
      (by linarith) (by linarith) h3) p6
  have e10 : (1 + J5) * J3 ≤ Z * X + P := by
    have hstep : (1 + J5) * J3 ≤ (1 + X) * Z :=
      mul_le_mul (by linarith) h3 hJ3nn (by linarith)
    linarith [hstep, p1]
  have b20 : ‖iteratedCovGrad (I := I) g 0 2 0
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction (I := I) (M := M) T)‖ ≤
      Cqa 0 * Cδ * P := by
    refine le_trans H20 ?_
    calc Cqa 0 * (Cδ * J3) ≤ Cqa 0 * (Cδ * P) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left eZ hCδ) (hCqa 0)
      _ = Cqa 0 * Cδ * P := by ring
  have b21 : ‖iteratedCovGrad (I := I) g 0 2 1
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction (I := I) (M := M) T)‖ ≤
      (Cqa 1 * Cδ + Cqa 1 * Ka 1) * P := by
    refine le_trans H21 ?_
    have hin : Cδ * J4 + Ka 1 * (1 + J4) * J3 ≤ Cδ * P + Ka 1 * P := by
      have t1 : Cδ * J4 ≤ Cδ * P := mul_le_mul_of_nonneg_left eY hCδ
      have t2 : Ka 1 * ((1 + J4) * J3) ≤ Ka 1 * P :=
        mul_le_mul_of_nonneg_left e1 (hKa 1)
      linarith [t1, t2]
    calc Cqa 1 * (Cδ * J4 + Ka 1 * (1 + J4) * J3)
        ≤ Cqa 1 * (Cδ * P + Ka 1 * P) := mul_le_mul_of_nonneg_left hin (hCqa 1)
      _ = (Cqa 1 * Cδ + Cqa 1 * Ka 1) * P := by ring
  have b22 : ‖iteratedCovGrad (I := I) g 0 2 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction (I := I) (M := M) T)‖ ≤
      Cqa 2 * Cδ * X + Cqa 2 * Ka 2 * Z * X +
        (Cqa 2 * Ka 1 + Cqa 2 * Ka 2) * P := by
    refine le_trans H22 ?_
    have hin : Cδ * J5 + (Ka 1 * (1 + J4) * J4 + Ka 2 * (1 + J5) * J3) ≤
        Cδ * X + (Ka 1 * P + Ka 2 * (Z * X + P)) := by
      have t1 : Cδ * J5 ≤ Cδ * X := mul_le_mul_of_nonneg_left h5 hCδ
      have t2 : Ka 1 * ((1 + J4) * J4) ≤ Ka 1 * P :=
        mul_le_mul_of_nonneg_left e2 (hKa 1)
      have t3 : Ka 2 * ((1 + J5) * J3) ≤ Ka 2 * (Z * X + P) :=
        mul_le_mul_of_nonneg_left e10 (hKa 2)
      linarith [t1, t2, t3]
    calc Cqa 2 * (Cδ * J5 + (Ka 1 * (1 + J4) * J4 + Ka 2 * (1 + J5) * J3))
        ≤ Cqa 2 * (Cδ * X + (Ka 1 * P + Ka 2 * (Z * X + P))) :=
          mul_le_mul_of_nonneg_left hin (hCqa 2)
      _ = Cqa 2 * Cδ * X + Cqa 2 * Ka 2 * Z * X +
            (Cqa 2 * Ka 1 + Cqa 2 * Ka 2) * P := by ring
  have b10 : ‖iteratedCovGrad (I := I) g 0 2 0
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction (I := I) (M := M) T)‖ ≤
      Cqb 0 * (2 * Kb0 0 + Kb1 0) * P := by
    refine le_trans H10 ?_
    have hin : Kb0 0 * (1 + J4) * (1 + J2) * J4 +
        Kb0 0 * (1 + J4) * (1 + J2) * J3 + Kb1 0 * (1 + J2) * J4 ≤
        Kb0 0 * P + Kb0 0 * P + Kb1 0 * P := by
      have t1 : Kb0 0 * ((1 + J4) * (1 + J2) * J4) ≤ Kb0 0 * P :=
        mul_le_mul_of_nonneg_left e5 (hKb0 0)
      have t2 : Kb0 0 * ((1 + J4) * (1 + J2) * J3) ≤ Kb0 0 * P :=
        mul_le_mul_of_nonneg_left e6 (hKb0 0)
      have t3 : Kb1 0 * ((1 + J2) * J4) ≤ Kb1 0 * P :=
        mul_le_mul_of_nonneg_left e3 (hKb1 0)
      linarith [t1, t2, t3]
    calc Cqb 0 * (Kb0 0 * (1 + J4) * (1 + J2) * J4 +
            Kb0 0 * (1 + J4) * (1 + J2) * J3 + Kb1 0 * (1 + J2) * J4)
        ≤ Cqb 0 * (Kb0 0 * P + Kb0 0 * P + Kb1 0 * P) :=
          mul_le_mul_of_nonneg_left hin (hCqb 0)
      _ = Cqb 0 * (2 * Kb0 0 + Kb1 0) * P := by ring
  have b11 : ‖iteratedCovGrad (I := I) g 0 2 1
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction (I := I) (M := M) T)‖ ≤
      Cqb 1 * (Kb0 0 + Kb0 1 + Kb1 0 + Kb1 1) * P := by
    refine le_trans H11 ?_
    have hin : Kb0 0 * (1 + J4) * (1 + J2) * J4 +
        Kb0 1 * (1 + J4) * (1 + J3) * J3 +
        (Kb1 0 * (1 + J4) * J3 + Kb1 1 * (1 + J3) * J4) ≤
        Kb0 0 * P + Kb0 1 * P + (Kb1 0 * P + Kb1 1 * P) := by
      have t1 : Kb0 0 * ((1 + J4) * (1 + J2) * J4) ≤ Kb0 0 * P :=
        mul_le_mul_of_nonneg_left e5 (hKb0 0)
      have t2 : Kb0 1 * ((1 + J4) * (1 + J3) * J3) ≤ Kb0 1 * P :=
        mul_le_mul_of_nonneg_left e7 (hKb0 1)
      have t3 : Kb1 0 * ((1 + J4) * J3) ≤ Kb1 0 * P :=
        mul_le_mul_of_nonneg_left e1 (hKb1 0)
      have t4 : Kb1 1 * ((1 + J3) * J4) ≤ Kb1 1 * P :=
        mul_le_mul_of_nonneg_left e4 (hKb1 1)
      linarith [t1, t2, t3, t4]
    calc Cqb 1 * (Kb0 0 * (1 + J4) * (1 + J2) * J4 +
            Kb0 1 * (1 + J4) * (1 + J3) * J3 +
            (Kb1 0 * (1 + J4) * J3 + Kb1 1 * (1 + J3) * J4))
        ≤ Cqb 1 * (Kb0 0 * P + Kb0 1 * P + (Kb1 0 * P + Kb1 1 * P)) :=
          mul_le_mul_of_nonneg_left hin (hCqb 1)
      _ = Cqb 1 * (Kb0 0 + Kb0 1 + Kb1 0 + Kb1 1) * P := by ring
  have b12 : ‖iteratedCovGrad (I := I) g 0 2 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction (I := I) (M := M) T)‖ ≤
      Cqb 2 * Kb1 1 * Z * X +
        Cqb 2 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb1 0 + Kb1 1 + Kb1 2) * P := by
    refine le_trans H12 ?_
    have hin : Kb0 0 * (1 + J4) * (1 + J4) * J3 +
        Kb0 1 * (1 + J4) * (1 + J3) * J4 +
        Kb0 2 * (1 + J4) * (1 + J4) * J3 +
        (Kb1 0 * (1 + J4) * J4 + Kb1 1 * (1 + J5) * J3 +
          Kb1 2 * (1 + J4) * J4) ≤
        Kb0 0 * P + Kb0 1 * P + Kb0 2 * P +
          (Kb1 0 * P + Kb1 1 * (Z * X + P) + Kb1 2 * P) := by
      have t1 : Kb0 0 * ((1 + J4) * (1 + J4) * J3) ≤ Kb0 0 * P :=
        mul_le_mul_of_nonneg_left e9 (hKb0 0)
      have t2 : Kb0 1 * ((1 + J4) * (1 + J3) * J4) ≤ Kb0 1 * P :=
        mul_le_mul_of_nonneg_left e8 (hKb0 1)
      have t3 : Kb0 2 * ((1 + J4) * (1 + J4) * J3) ≤ Kb0 2 * P :=
        mul_le_mul_of_nonneg_left e9 (hKb0 2)
      have t4 : Kb1 0 * ((1 + J4) * J4) ≤ Kb1 0 * P :=
        mul_le_mul_of_nonneg_left e2 (hKb1 0)
      have t5 : Kb1 1 * ((1 + J5) * J3) ≤ Kb1 1 * (Z * X + P) :=
        mul_le_mul_of_nonneg_left e10 (hKb1 1)
      have t6 : Kb1 2 * ((1 + J4) * J4) ≤ Kb1 2 * P :=
        mul_le_mul_of_nonneg_left e2 (hKb1 2)
      linarith [t1, t2, t3, t4, t5, t6]
    calc Cqb 2 * (Kb0 0 * (1 + J4) * (1 + J4) * J3 +
            Kb0 1 * (1 + J4) * (1 + J3) * J4 +
            Kb0 2 * (1 + J4) * (1 + J4) * J3 +
            (Kb1 0 * (1 + J4) * J4 + Kb1 1 * (1 + J5) * J3 +
              Kb1 2 * (1 + J4) * J4))
        ≤ Cqb 2 * (Kb0 0 * P + Kb0 1 * P + Kb0 2 * P +
            (Kb1 0 * P + Kb1 1 * (Z * X + P) + Kb1 2 * P)) :=
          mul_le_mul_of_nonneg_left hin (hCqb 2)
      _ = Cqb 2 * Kb1 1 * Z * X +
            Cqb 2 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb1 0 + Kb1 1 + Kb1 2) * P := by
          ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [b20, b21, b22, b10, b11, b12,
    mul_nonneg (add_nonneg (hCqa 0) (hCqa 1)) hPnn,
    mul_nonneg hRest hPnn, mul_nonneg (mul_nonneg hRest hCδ) hPnn]

theorem exists_galerkin_action_h2_tame_bound_constants_background (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop Kr2 Kr1 Kcap : ℝ,
      0 ≤ Ctop ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
      ∀ {R δ : ℝ} (hR : 0 ≤ R)
        (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
        (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ T) δ),
        ∃ Kmid : ℝ, 0 ≤ Kmid ∧
          ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
            (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
            Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
                  ((galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hR hδ hreal F c).coeff i) ^ 2) ≤
              (Ctop * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R) *
                  Real.sqrt (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                Kmid * (1 + Real.sqrt (∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2)) ^ 2 := by
  classical
  obtain ⟨Ctop, Kr2, Kr1, Kmid, hCtop, hKr2, hKr1, hKmid, hlad⟩ :=
    lowerScaleActions_covariantJetNorm_two_tame_bound_background (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Kcap, hKcap, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  obtain ⟨Chs, hChs, hhs⟩ := hs_le_jet (I := I) (M := M) g₀ 2 2
  obtain ⟨C4, hC4, hjet4⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 4
  obtain ⟨C3, hC3, hjet3⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 3
  obtain ⟨CR, hCR, hjetR⟩ := galerkinRepresentation_lowOrder_iteratedCovGrad_sum_le (I := I) (M := M) g₀
  simp only [Nat.cast_ofNat] at hjet4 hjet3 hhs
  refine ⟨Chs * C4 * Ctop, Chs * C4 * Kr2 * CR, Chs * C4 * Kr1 * CR,
    Kcap,
    mul_nonneg (mul_nonneg hChs hC4) hCtop,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC4) hKr2) hCR,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC4) hKr1) hCR,
    hKcap, ?_⟩
  intro R δ hR hδ hδ0 hδ3 hreal
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  have hCδ : 0 ≤ Cδ := mul_nonneg hKcap (div_nonneg hδ0 (sq_nonneg _))
  have hcap : ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
          ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
            (galRepFib (I := I) (M := M) g₀ hR hreal S c)
            (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderCoefficient.toSection x) ≤
        Cδ ^ 2 := by
    intro S c x
    exact (hsplit _
      (ccTensorBilin_symmS_symm (I := I) (M := M)
        g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
      hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR hreal S c)
      (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).2 x
  refine ⟨Chs * Kmid * (1 + Cδ) * (1 + C3) ^ 2 * (1 + CR * R) ^ 2,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hChs hKmid) (by linarith))
      (sq_nonneg _)) (sq_nonneg _), ?_⟩
  intro F c
  rw [show Kcap * (δ / (1 - δ) ^ 2) = Cδ by rfl]
  set s4 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) with hs4def
  set s3 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) with hs3def
  have hs4nn : (0 : ℝ) ≤ s4 := by rw [hs4def]; positivity
  have hs3nn : (0 : ℝ) ≤ s3 := by rw [hs3def]; positivity
  have hsym := ccTensorBilin_symmS_symm
    (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c)
  have h5 : Real.sqrt (∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C4 * s4 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 5 _) (hjet4 hR F c)
  have h4 : Real.sqrt (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C3 * s3 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 4 _) (hjet3 hR F c)
  have h3 : Real.sqrt (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ CR * R :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 3 _) (hjetR hR F c)
  have hladb := hlad (symmS (I := I) (M := M) g₀
      (galCoreRep (I := I) (M := M) g₀ R F c)) hsym hδ0 hδ3
    (galRepFib (I := I) (M := M) g₀ hR hreal F c)
    (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal) hCδ (hcap F c)
    (mul_nonneg hC3 hs3nn) (mul_nonneg hCR hR) h5 h4 h3
  have hmass := cc_partial_le_norm (I := I) (M := M) g₀ 2 (2 : ℝ)
    ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
          (symmS (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderAction
        (I := I) (M := M)
        (symmS (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c)) +
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
          (symmS (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).firstOrderAction
        (I := I) (M := M)
        (symmS (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c))) F
  refine le_trans (le_trans (Real.sqrt_le_sqrt hmass)
    (le_of_eq (Real.sqrt_sq (norm_nonneg _)))) ?_
  refine le_trans (hhs _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (le_trans (Finset.sum_le_sum (fun j _ => by
      rw [iteratedCovGrad_add]; exact norm_add_le _ _)) hladb) hChs) ?_
  have h1 : (1 : ℝ) + C3 * s3 ≤ (1 + C3) * (1 + s3) := by
    nlinarith [hC3, hs3nn]
  have hsq : (1 + C3 * s3) ^ 2 ≤ (1 + C3) ^ 2 * (1 + s3) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + C3 * s3 := by nlinarith [mul_nonneg hC3 hs3nn]
    have := pow_le_pow_left₀ h0 h1 2
    calc (1 + C3 * s3) ^ 2 ≤ ((1 + C3) * (1 + s3)) ^ 2 := this
      _ = (1 + C3) ^ 2 * (1 + s3) ^ 2 := by ring
  have hcoef : (0 : ℝ) ≤ Chs * Kmid * (1 + Cδ) * (1 + CR * R) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hChs hKmid) (by linarith)) (sq_nonneg _)
  have hB : Chs * (Kmid * (1 + Cδ) *
        ((1 + C3 * s3) ^ 2 * (1 + CR * R) ^ 2)) ≤
      Chs * Kmid * (1 + Cδ) * (1 + C3) ^ 2 * (1 + CR * R) ^ 2 * (1 + s3) ^ 2 := by
    calc Chs * (Kmid * (1 + Cδ) * ((1 + C3 * s3) ^ 2 * (1 + CR * R) ^ 2))
        = Chs * Kmid * (1 + Cδ) * (1 + CR * R) ^ 2 * (1 + C3 * s3) ^ 2 := by ring
      _ ≤ Chs * Kmid * (1 + Cδ) * (1 + CR * R) ^ 2 *
            ((1 + C3) ^ 2 * (1 + s3) ^ 2) := mul_le_mul_of_nonneg_left hsq hcoef
      _ = Chs * Kmid * (1 + Cδ) * (1 + C3) ^ 2 * (1 + CR * R) ^ 2 *
            (1 + s3) ^ 2 := by ring
  nlinarith [hB]

private theorem exists_galerkin_energy_three_bound_parameters_raw_background (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop₂ Kr2 Kr1 Kcap : ℝ,
      0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
      ∀ {δ Ctop B1 ρ P T B : ℝ}
    (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
    (_hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (_hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun u => U N u i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
        (Set.Ici t) t)
    (_hUinit : ∀ N i, U N 0 i = 0)
    {Pr : ℕ → ℝ → ℝ}
    (_hPr0 : ∀ N, Pr N 0 = 0)
    (_hPrnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Pr N t)
    (_hPrcont : ∀ N, ContinuousOn (Pr N) (Set.Icc (0 : ℝ) T))
    (_hPrderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (Pr N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) (Set.Ici t) t)
    (_hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ B)
    {ε : ℝ}, 0 < ε →
        Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
            Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t ≤ Φ := by
  classical
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hCtop₂, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_action_h2_tame_bound_constants_background (I := I) (M := M) hDim g₀ g_bg
  refine ⟨Ctop₂, Kr2, Kr1, Kcap, hCtop₂, hKr2, hKr1, hKcap, ?_⟩
  intro δ Ctop B1 ρ P T B hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore U
    hUcont hUderiv hUinit Pr hPr0 hPrnn hPrcont hPrderiv hPrbd ε hε hH
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  obtain ⟨Kmid, hKmid, hmass⟩ := hord hRpos.le hδ hδ0 hδ3
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  obtain ⟨Cseed, hCseed, hseed⟩ := exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g₀ g_bg
    hRpos hδ (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
      (ρ := ρ) hP.le hreal) hcore
  change Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 at hH
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i 3 *
            (U N t i * galTameForce (I := I) (M := M) g₀ 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i) ≤
        (2 * (Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) (3 + 1) t +
          (0 + 6 * Kmid ^ 2 / ε * (1 + galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t)) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t +
          2 * Cseed 3 * Real.sqrt (galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) +
          Kmid ^ 2 / ε := by
    intro N t _
    have hsplit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        galTameForce (I := I) (M := M) g₀ 1 hRpos.le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i =
          (galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i +
          (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i := by
      intro i hi
      rw [galForceArmBackground (I := I) (M := M) g₀ g_bg hδ hδ0 hδ3 hCtop hB1 hρ hP hreal
        hcore (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i, if_pos hi]
      simp only [galerkinActionVectorBackground]
      module
    have hstat : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i 3 *
          ((boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i) ^ 2
          ≤ Cseed 3 ^ 2 := by
      have h := hseed 3 (eigenIdxFinset (I := I) (M := M) g₀ N)
      simpa only [boundedDeTurckRemainderOnLowerState, Nat.cast_ofNat] using h
    have hladder :
        Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i (3 - 1) *
              ((galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
                (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                  (ρ := ρ) hP.le hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N)
                (U N t)).coeff i) ^ 2) ≤
          (Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) *
              Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i (3 + 1) *
                  (U N t i) ^ 2) +
            (Kmid * (2 + Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i 3 * (U N t i) ^ 2))) *
              Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i 3 * (U N t i) ^ 2) +
            Kmid := by
      rw [show (3 - 1 : ℝ) = 2 by norm_num, show (3 + 1 : ℝ) = 4 by norm_num]
      have hm := hmass (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)
      nlinarith [hm]
    have hres := two_sum_ladder_add_le (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (3 : ℝ) (U N t)
      (fun i => (galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal) (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i)
      (fun i => (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i)
      (galTameForce (I := I) (M := M) g₀ 1 hRpos.le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
      (hCseed 3) hε hsplit hladder hstat
    unfold galerkinEnergy
    refine le_trans hres ?_
    set Eng : ℝ := ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      tensorSobolevWeight (I := I) (M := M) i 3 * (U N t i) ^ 2 with hEngDef
    have hEngnn : (0 : ℝ) ≤ Eng := by
      rw [hEngDef]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i 3) (sq_nonneg _))
    have hssq : Real.sqrt Eng ^ 2 = Eng := Real.sq_sqrt hEngnn
    have hsnn : (0 : ℝ) ≤ Real.sqrt Eng := Real.sqrt_nonneg _
    clear_value Eng
    clear hEngDef
    have hbsq : (Kmid * (2 + Real.sqrt Eng)) ^ 2 ≤ 6 * Kmid ^ 2 * (1 + Eng) := by
      nlinarith [hssq, hsnn, sq_nonneg (Kmid * (Real.sqrt Eng - 1)),
        sq_nonneg (Kmid * Real.sqrt Eng)]
    have hmid : (Kmid * (2 + Real.sqrt Eng)) ^ 2 / ε * Eng ≤
        6 * Kmid ^ 2 / ε * (1 + Eng) * Eng := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have h2 := mul_le_mul_of_nonneg_right hbsq hEngnn
      have h3 := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hε.le)
      linarith [h3]
    linarith [hmid]
  refine galRiderBound (I := I) (M := M) (g := g₀) (r := 0) (s₀ := 2)
    (U := U) (T := T) (σ := 3)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g₀ 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g₀ N)
    (Cδ := 2 * (Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε)
    (Cmid := 0) (seed := 2 * Cseed 3) (B0 := 0)
    (c₀ := Kmid ^ 2 / ε) (Crid := 6 * Kmid ^ 2 / ε) (B := B) (P := Pr)
    (by linarith) le_rfl (by linarith [hCseed 3])
    (div_nonneg (sq_nonneg _) hε.le)
    (div_nonneg (by positivity) hε.le)
    hPr0 hPrnn hPrcont hPrderiv hPrbd hUcont hUderiv hclosure ?_
  intro N
  have hz : galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 0 = 0 := by
    unfold galerkinEnergy
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hUinit N i]; ring
  rw [hz]

def HasGalerkinEnergyThreeBoundBackground (g₀ g_bg : SmoothRiemannianMetric I M)
    (Ctop₂ Kr2 Kr1 Kcap : ℝ) : Prop :=
  0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
    ∀ {δ Ctop B1 ρ P T B : ℝ}
      (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)))
      {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
      (_hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
      (_hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun u => U N u i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            galTameForce (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
          (Set.Ici t) t)
      (_hUinit : ∀ N i, U N 0 i = 0)
      {Pr : ℕ → ℝ → ℝ}
      (_hPr0 : ∀ N, Pr N 0 = 0)
      (_hPrnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Pr N t)
      (_hPrcont : ∀ N, ContinuousOn (Pr N) (Set.Icc (0 : ℝ) T))
      (_hPrderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Pr N)
          (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) (Set.Ici t) t)
      (_hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ B)
      {ε : ℝ}, 0 < ε →
        Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
            Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t ≤ Φ

theorem exists_galerkin_energy_three_bound_parameters_background (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop₂ Kr2 Kr1 Kcap : ℝ, HasGalerkinEnergyThreeBoundBackground (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hCtop₂, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_energy_three_bound_parameters_raw_background (I := I) (M := M) hDim g₀ g_bg
  exact ⟨Ctop₂, Kr2, Kr1, Kcap, hCtop₂, hKr2, hKr1, hKcap, hord⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
