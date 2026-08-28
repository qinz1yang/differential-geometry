import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.H3Energy

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic (riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (cc_partial_le_norm ccTensorBilin_symmS_symm eigenIdxFinset galerkinEnergy hs_le_jet
    iteratedCovGrad_add smoothCcToTensorHs)
open DifferentialGeometry.Analysis.Parabolic (zero_mem_lowerState)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private theorem mul4Le {a b c d A B C D : ℝ}
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    a * b * c * d ≤ A * B * C * D :=
  mul_le_mul
    (mul_le_mul (mul_le_mul ha hb hb0 hA0) hc hc0 (mul_nonneg hA0 hB0))
    hd hd0 (mul_nonneg (mul_nonneg hA0 hB0) hC0)


theorem lowerScaleActions_covariantDerivative_three_tame_bound_background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Atop Ar2 Ar1 Krem : ℝ,
      0 ≤ Atop ∧ 0 ≤ Ar2 ∧ 0 ≤ Ar1 ∧ 0 ≤ Krem ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
        {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderCoefficient.toSection x) ≤
            Cδ ^ 2)
        {X W Y Z : ℝ} (hW : 0 ≤ W) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
        (h6 : Real.sqrt (∑ j ∈ Finset.range 6,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ X)
        (h5 : Real.sqrt (∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ W)
        (h4 : Real.sqrt (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Y)
        (h3 : Real.sqrt (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Z),
        ‖iteratedCovGrad (I := I) g 0 2 3
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
                (I := I) (M := M) T)‖ +
          ‖iteratedCovGrad (I := I) g 0 2 3
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ≤
          (Atop * Cδ + Ar2 * Z + Ar1 * Z) * X +
            Krem * (1 + Cδ) * ((1 + Y) ^ 3 * (1 + Z) ^ 2) * (1 + W) := by
  classical
  obtain ⟨Cqa, Ka, hCqa, hKa, ha2⟩ :=
    secondOrderAction_perIndex_linear_bound (I := I) (M := M) hDim g g_bg
  obtain ⟨Cqb, Kb0, Kb1, hCqb, hKb0, hKb1, ha1⟩ :=
    firstOrderAction_perIndex_linear_bound_background (I := I) (M := M) hDim g g_bg
  let Krem : ℝ := Cqa 3 * (Ka 1 + Ka 2 + Ka 3) +
    Cqb 3 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
      Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3)
  have hKas : 0 ≤ Ka 1 + Ka 2 + Ka 3 := by
    linarith only [hKa 1, hKa 2, hKa 3]
  have hKbs : 0 ≤ Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
      Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 := by
    linarith only [hKb0 0, hKb0 1, hKb0 2, hKb0 3,
      hKb1 0, hKb1 1, hKb1 2, hKb1 3]
  have hKrem : 0 ≤ Krem := by
    dsimp only [Krem]
    exact add_nonneg (mul_nonneg (hCqa 3) hKas) (mul_nonneg (hCqb 3) hKbs)
  refine ⟨Cqa 3, Cqa 3 * Ka 3, Cqb 3 * Kb1 2, Krem,
    hCqa 3, mul_nonneg (hCqa 3) (hKa 3),
    mul_nonneg (hCqb 3) (hKb1 2), hKrem, ?_⟩
  intro T hT δ hδ0 hδ3 hδg hδZ Cδ hCδ hfib X W Y Z hW hY hZ h6 h5 h4 h3
  have H23 := ha2 T hT hδ0 hδ3 hδg hδZ hCδ hfib 3
  have H13 := ha1 T hT hδ0 hδ3 hδg hδZ 3
  set J3 : ℝ := Real.sqrt (∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ3def
  set J4 : ℝ := Real.sqrt (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ4def
  set J5 : ℝ := Real.sqrt (∑ j ∈ Finset.range 5,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ5def
  set J6 : ℝ := Real.sqrt (∑ j ∈ Finset.range 6,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ6def
  simp only [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} from rfl,
    Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by norm_num),
    Finset.sum_pair (show (2 : ℕ) ≠ 3 by norm_num), Nat.reduceAdd,
    Nat.reduceSub] at H23
  rw [← hJ3def, ← hJ4def, ← hJ5def, ← hJ6def] at H23
  simp only [show (Finset.range 2 : Finset ℕ) = {0, 1} from rfl,
    Finset.sum_pair (show (0 : ℕ) ≠ 1 by norm_num),
    show (Finset.range 3 : Finset ℕ) = {0, 1, 2} from rfl,
    Finset.sum_insert (show (0 : ℕ) ∉ ({1, 2} : Finset ℕ) by norm_num),
    Finset.sum_pair (show (1 : ℕ) ≠ 2 by norm_num), Nat.reduceAdd,
    Nat.reduceSub] at H13 hJ3def
  rw [← hJ3def, ← hJ4def, ← hJ5def, ← hJ6def] at H13
  have H23' :
      ‖iteratedCovGrad (I := I) g 0 2 3
          ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqa 3 * (Cδ * J6 + Ka 1 * (1 + J4) * J5 +
          Ka 2 * (1 + J5) * J4 + Ka 3 * (1 + J6) * J3) := by
    calc
      _ ≤ _ := H23
      _ = _ := by ring
  have H13' :
      ‖iteratedCovGrad (I := I) g 0 2 3
          ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqb 3 * ((Kb0 0 + Kb0 2) * (1 + J4) ^ 2 * J4 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J3 +
          Kb1 0 * (1 + J4) * J5 +
          (Kb1 1 + Kb1 3) * (1 + J5) * J4 +
          Kb1 2 * (1 + J6) * J3) := by
    calc
      _ ≤ _ := H13
      _ = _ := by ring
  have hJ3nn : 0 ≤ J3 := by rw [hJ3def]; positivity
  have hJ4nn : 0 ≤ J4 := by rw [hJ4def]; positivity
  have hJ5nn : 0 ≤ J5 := by rw [hJ5def]; positivity
  have hJ6nn : 0 ≤ J6 := by rw [hJ6def]; positivity
  have hJ3Z : J3 ≤ Z := by simpa only [hJ3def] using h3
  have hJ4Y : J4 ≤ Y := by simpa only [hJ4def] using h4
  have hJ5W : J5 ≤ W := by simpa only [hJ5def] using h5
  have hJ6X : J6 ≤ X := by simpa only [hJ6def] using h6
  let A : ℝ := 1 + Cδ
  let B : ℝ := (1 + Y) ^ 3
  let C : ℝ := (1 + Z) ^ 2
  let D : ℝ := 1 + W
  let Q : ℝ := A * B * C * D
  have hAnn : 0 ≤ A := by dsimp only [A]; linarith only [hCδ]
  have hBnn : 0 ≤ B := by dsimp only [B]; positivity
  have hCnn : 0 ≤ C := by dsimp only [C]; positivity
  have hDnn : 0 ≤ D := by dsimp only [D]; linarith only [hW]
  have hA1 : 1 ≤ A := by dsimp only [A]; linarith only [hCδ]
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    nlinarith only [hZ, sq_nonneg Z]
  have hZC : Z ≤ C := by
    dsimp only [C]
    nlinarith only [hZ, sq_nonneg Z]
  have hsqY : 1 ≤ (1 + Y) ^ 2 := by
    nlinarith only [hY, sq_nonneg Y]
  have hYB0 : 1 + Y ≤ B := by
    dsimp only [B]
    calc
      1 + Y = (1 + Y) * 1 := by ring
      _ ≤ (1 + Y) * (1 + Y) ^ 2 :=
        mul_le_mul_of_nonneg_left hsqY (by linarith only [hY])
      _ = (1 + Y) ^ 3 := by ring
  have hB1 : 1 ≤ B := by linarith only [hY, hYB0]
  have hJ4B : J4 ≤ B := by linarith only [hJ4Y, hY, hYB0]
  have h1J4B : 1 + J4 ≤ B := by linarith only [hJ4Y, hYB0]
  have hJ4cube : (1 + J4) ^ 2 * J4 ≤ B := by
    have hcube : (1 + J4) ^ 3 ≤ (1 + Y) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hJ4nn]) (by linarith only [hJ4Y]) 3
    dsimp only [B]
    calc
      (1 + J4) ^ 2 * J4 ≤ (1 + J4) ^ 2 * (1 + J4) :=
        mul_le_mul_of_nonneg_left (by linarith only [hJ4nn]) (sq_nonneg _)
      _ = (1 + J4) ^ 3 := by ring
      _ ≤ (1 + Y) ^ 3 := hcube
  have hJ5D : J5 ≤ D := by dsimp only [D]; linarith only [hJ5W, hW]
  have h1J5D : 1 + J5 ≤ D := by dsimp only [D]; linarith only [hJ5W]
  have hQnn : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg (mul_nonneg (mul_nonneg hAnn hBnn) hCnn) hDnn
  have eJ45 : (1 + J4) * J5 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) * J5 = 1 * (1 + J4) * 1 * J5 := by ring
      _ ≤ A * B * C * D := mul4Le (by linarith only [hJ4nn]) zero_le_one hJ5nn
        hAnn hBnn hCnn hA1 h1J4B hC1 hJ5D
  have eJ54 : (1 + J5) * J4 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J5) * J4 = 1 * J4 * 1 * (1 + J5) := by ring
      _ ≤ A * B * C * D := mul4Le hJ4nn zero_le_one
        (by linarith only [hJ5nn])
        hAnn hBnn hCnn hA1 hJ4B hC1 h1J5D
  have eJ3 : J3 ≤ Q := by
    dsimp only [Q]
    calc
      J3 = 1 * 1 * J3 * 1 := by ring
      _ ≤ A * B * C * D := mul4Le zero_le_one hJ3nn zero_le_one
        hAnn hBnn hCnn hA1 hB1 (le_trans hJ3Z hZC)
          (by dsimp only [D]; linarith only [hW])
  have eJ444 : (1 + J4) ^ 2 * J4 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) ^ 2 * J4 = 1 * ((1 + J4) ^ 2 * J4) * 1 * 1 := by ring
      _ ≤ A * B * C * D := mul4Le
        (mul_nonneg (sq_nonneg _) hJ4nn) zero_le_one zero_le_one
        hAnn hBnn hCnn hA1 hJ4cube hC1
          (by dsimp only [D]; linarith only [hW])
  have eJ453 : (1 + J4) * (1 + J5) * J3 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) * (1 + J5) * J3 = 1 * (1 + J4) * J3 * (1 + J5) := by ring
      _ ≤ A * B * C * D := mul4Le (by linarith only [hJ4nn]) hJ3nn
        (by linarith only [hJ5nn])
        hAnn hBnn hCnn hA1 h1J4B (le_trans hJ3Z hZC) h1J5D
  have eTop : (1 + J6) * J3 ≤ Z * X + Q := by
    have hprod : J3 * J6 ≤ Z * X :=
      mul_le_mul hJ3Z hJ6X hJ6nn hZ
    calc
      (1 + J6) * J3 = J3 * J6 + J3 := by ring
      _ ≤ Z * X + Q := add_le_add hprod eJ3
  clear_value J3 J4 J5 J6
  clear hJ3def hJ4def hJ5def hJ6def
  have b23 :
      ‖iteratedCovGrad (I := I) g 0 2 3
          ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqa 3 * Cδ * X + Cqa 3 * Ka 3 * Z * X +
          Cqa 3 * (Ka 1 + Ka 2 + Ka 3) * Q := by
    refine le_trans H23' ?_
    have t0 : Cδ * J6 ≤ Cδ * X := mul_le_mul_of_nonneg_left hJ6X hCδ
    have t1 : Ka 1 * ((1 + J4) * J5) ≤ Ka 1 * Q :=
      mul_le_mul_of_nonneg_left eJ45 (hKa 1)
    have t2 : Ka 2 * ((1 + J5) * J4) ≤ Ka 2 * Q :=
      mul_le_mul_of_nonneg_left eJ54 (hKa 2)
    have t3 : Ka 3 * ((1 + J6) * J3) ≤ Ka 3 * (Z * X + Q) :=
      mul_le_mul_of_nonneg_left eTop (hKa 3)
    have hin : Cδ * J6 + Ka 1 * (1 + J4) * J5 +
        Ka 2 * (1 + J5) * J4 + Ka 3 * (1 + J6) * J3 ≤
        Cδ * X + Ka 1 * Q + Ka 2 * Q + Ka 3 * (Z * X + Q) := by
      linarith only [t0, t1, t2, t3]
    calc
      Cqa 3 * (Cδ * J6 + Ka 1 * (1 + J4) * J5 +
          Ka 2 * (1 + J5) * J4 + Ka 3 * (1 + J6) * J3) ≤
          Cqa 3 * (Cδ * X + Ka 1 * Q + Ka 2 * Q + Ka 3 * (Z * X + Q)) :=
        mul_le_mul_of_nonneg_left hin (hCqa 3)
      _ = Cqa 3 * Cδ * X + Cqa 3 * Ka 3 * Z * X +
          Cqa 3 * (Ka 1 + Ka 2 + Ka 3) * Q := by ring
  have b13 :
      ‖iteratedCovGrad (I := I) g 0 2 3
          ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqb 3 * Kb1 2 * Z * X +
          Cqb 3 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3) * Q := by
    refine le_trans H13' ?_
    have t0 : (Kb0 0 + Kb0 2) * ((1 + J4) ^ 2 * J4) ≤
        (Kb0 0 + Kb0 2) * Q :=
      mul_le_mul_of_nonneg_left eJ444 (add_nonneg (hKb0 0) (hKb0 2))
    have t1 : (Kb0 1 + Kb0 3) * ((1 + J4) * (1 + J5) * J3) ≤
        (Kb0 1 + Kb0 3) * Q :=
      mul_le_mul_of_nonneg_left eJ453 (add_nonneg (hKb0 1) (hKb0 3))
    have t2 : Kb1 0 * ((1 + J4) * J5) ≤ Kb1 0 * Q :=
      mul_le_mul_of_nonneg_left eJ45 (hKb1 0)
    have t3 : (Kb1 1 + Kb1 3) * ((1 + J5) * J4) ≤
        (Kb1 1 + Kb1 3) * Q :=
      mul_le_mul_of_nonneg_left eJ54 (add_nonneg (hKb1 1) (hKb1 3))
    have t4 : Kb1 2 * ((1 + J6) * J3) ≤ Kb1 2 * (Z * X + Q) :=
      mul_le_mul_of_nonneg_left eTop (hKb1 2)
    have hin :
        (Kb0 0 + Kb0 2) * (1 + J4) ^ 2 * J4 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J3 +
          Kb1 0 * (1 + J4) * J5 +
          (Kb1 1 + Kb1 3) * (1 + J5) * J4 +
          Kb1 2 * (1 + J6) * J3 ≤
        (Kb0 0 + Kb0 2) * Q + (Kb0 1 + Kb0 3) * Q +
          Kb1 0 * Q + (Kb1 1 + Kb1 3) * Q + Kb1 2 * (Z * X + Q) := by
      linarith only [t0, t1, t2, t3, t4]
    calc
      Cqb 3 * ((Kb0 0 + Kb0 2) * (1 + J4) ^ 2 * J4 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J3 +
          Kb1 0 * (1 + J4) * J5 +
          (Kb1 1 + Kb1 3) * (1 + J5) * J4 +
          Kb1 2 * (1 + J6) * J3) ≤
        Cqb 3 * ((Kb0 0 + Kb0 2) * Q + (Kb0 1 + Kb0 3) * Q +
          Kb1 0 * Q + (Kb1 1 + Kb1 3) * Q + Kb1 2 * (Z * X + Q)) :=
        mul_le_mul_of_nonneg_left hin (hCqb 3)
      _ = Cqb 3 * Kb1 2 * Z * X +
          Cqb 3 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3) * Q := by ring
  dsimp only [Krem]
  calc
    _ ≤ (Cqa 3 * Cδ * X + Cqa 3 * Ka 3 * Z * X +
          Cqa 3 * (Ka 1 + Ka 2 + Ka 3) * Q) +
        (Cqb 3 * Kb1 2 * Z * X +
          Cqb 3 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3) * Q) := add_le_add b23 b13
    _ = ((Cqa 3) * Cδ + (Cqa 3 * Ka 3) * Z +
          (Cqb 3 * Kb1 2) * Z) * X +
        (Cqa 3 * (Ka 1 + Ka 2 + Ka 3) +
          Cqb 3 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3)) *
          (1 + Cδ) * ((1 + Y) ^ 3 * (1 + Z) ^ 2) * (1 + W) := by
      dsimp only [Q, A, B, C, D]
      ring

theorem exists_galerkin_action_h3_tame_bound_constants_background (hDim : Module.finrank ℝ E = 3)
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
        ∀ {R3 : ℝ}, 0 ≤ R3 →
          ∃ Kmid Kadd : ℝ, 0 ≤ Kmid ∧ 0 ≤ Kadd ∧
            ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
              (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) ≤
                  R3 →
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                  ((galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg
                    hR hδ hreal F c).coeff i) ^ 2) ≤
                (Ctop * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R) *
                    Real.sqrt (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) *
                        (c i) ^ 2) +
                  Kmid * Real.sqrt (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i) ^ 2) + Kadd := by
  classical
  obtain ⟨Atop, Ar2, Ar1, Krem, hAtop, hAr2, hAr1, hKrem, hq3⟩ :=
    lowerScaleActions_covariantDerivative_three_tame_bound_background (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Ltop, Lr2, Lr1, Lrem, hLtop, hLr2, hLr1, hLrem, hlow⟩ :=
    lowerScaleActions_covariantJetNorm_two_tame_bound_background (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Kcap, hKcap, hsplit⟩ :=
    lowData_split (I := I) (M := M) g₀ g_bg
  obtain ⟨Chs, hChs, hhs⟩ := hs_le_jet (I := I) (M := M) g₀ 2 3
  obtain ⟨C5, hC5, hjet5⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 5
  obtain ⟨C4, hC4, hjet4⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 4
  obtain ⟨C3, hC3, hjet3⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 3
  obtain ⟨CR, hCR, hjetR⟩ := galerkinRepresentation_lowOrder_iteratedCovGrad_sum_le (I := I) (M := M) g₀
  simp only [Nat.cast_ofNat] at hjet5 hjet4 hjet3 hhs
  refine ⟨Chs * C5 * Atop, Chs * C5 * Ar2 * CR,
    Chs * C5 * Ar1 * CR, Kcap,
    mul_nonneg (mul_nonneg hChs hC5) hAtop,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC5) hAr2) hCR,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC5) hAr1) hCR,
    hKcap, ?_⟩
  intro R δ hR hδ hδ0 hδ3 hreal R3 hR3
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  let Y : ℝ := C3 * R3
  let Z : ℝ := CR * R
  have hCδ : 0 ≤ Cδ := by
    dsimp only [Cδ]
    exact mul_nonneg hKcap (div_nonneg hδ0 (sq_nonneg _))
  have hY : 0 ≤ Y := by dsimp only [Y]; exact mul_nonneg hC3 hR3
  have hZ : 0 ≤ Z := by dsimp only [Z]; exact mul_nonneg hCR hR
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
  let βlow : ℝ := (Ltop * Cδ + Lr2 * Z + Lr1 * Z) * C4
  let γlow : ℝ := Lrem * (1 + Cδ) * ((1 + Y) ^ 2 * (1 + Z) ^ 2)
  let β3 : ℝ := Krem * (1 + Cδ) * ((1 + Y) ^ 3 * (1 + Z) ^ 2) * C4
  let γ3 : ℝ := Krem * (1 + Cδ) * ((1 + Y) ^ 3 * (1 + Z) ^ 2)
  let Kmid : ℝ := Chs * (βlow + β3)
  let Kadd : ℝ := Chs * (γlow + γ3)
  have hβlow : 0 ≤ βlow := by
    dsimp only [βlow]
    exact mul_nonneg
      (add_nonneg (add_nonneg (mul_nonneg hLtop hCδ) (mul_nonneg hLr2 hZ))
        (mul_nonneg hLr1 hZ)) hC4
  have hγlow : 0 ≤ γlow := by
    dsimp only [γlow]
    exact mul_nonneg (mul_nonneg hLrem (by linarith only [hCδ]))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hβ3 : 0 ≤ β3 := by
    dsimp only [β3]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hKrem (by linarith only [hCδ]))
        (mul_nonneg (by positivity) (sq_nonneg _))) hC4
  have hγ3 : 0 ≤ γ3 := by
    dsimp only [γ3]
    exact mul_nonneg (mul_nonneg hKrem (by linarith only [hCδ]))
      (mul_nonneg (by positivity) (sq_nonneg _))
  refine ⟨Kmid, Kadd,
    by dsimp only [Kmid]; exact mul_nonneg hChs (add_nonneg hβlow hβ3),
    by dsimp only [Kadd]; exact mul_nonneg hChs (add_nonneg hγlow hγ3), ?_⟩
  intro F c hE3
  rw [show Kcap * (δ / (1 - δ) ^ 2) = Cδ by rfl]
  set s5 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) with hs5def
  set s4 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) with hs4def
  set s3 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) with hs3def
  have hs5nn : 0 ≤ s5 := by rw [hs5def]; positivity
  have hs4nn : 0 ≤ s4 := by rw [hs4def]; positivity
  have hs3nn : 0 ≤ s3 := by rw [hs3def]; positivity
  have hsym := ccTensorBilin_symmS_symm
    (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c)
  have h6 : Real.sqrt (∑ j ∈ Finset.range 6,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C5 * s5 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 6 _) (hjet5 hR F c)
  have h5 : Real.sqrt (∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C4 * s4 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 5 _) (hjet4 hR F c)
  have h4raw : Real.sqrt (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C3 * s3 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 4 _) (hjet3 hR F c)
  have h4 : Real.sqrt (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ Y := by
    refine le_trans h4raw ?_
    dsimp only [Y]
    exact mul_le_mul_of_nonneg_left (by simpa only [hs3def] using hE3) hC3
  have h3 : Real.sqrt (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ Z := by
    refine le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 3 _) (hjetR hR F c)
  have hlowb := hlow
    (symmS (I := I) (M := M) g₀
      (galCoreRep (I := I) (M := M) g₀ R F c)) hsym hδ0 hδ3
    (galRepFib (I := I) (M := M) g₀ hR hreal F c)
    (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal) hCδ (hcap F c)
    hY hZ h5 h4 h3
  have hq3b := hq3
    (symmS (I := I) (M := M) g₀
      (galCoreRep (I := I) (M := M) g₀ R F c)) hsym hδ0 hδ3
    (galRepFib (I := I) (M := M) g₀ hR hreal F c)
    (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal) hCδ (hcap F c)
    (mul_nonneg hC4 hs4nn) hY hZ h6 h5 h4 h3
  have hsum :
      ∑ q ∈ Finset.range 4,
          (‖iteratedCovGrad (I := I) g₀ 0 2 q
              ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
                (galRepFib (I := I) (M := M) g₀ hR hreal F c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderAction
                  (I := I) (M := M)
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀ R F c)))‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
                (galRepFib (I := I) (M := M) g₀ hR hreal F c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).firstOrderAction
                  (I := I) (M := M)
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀ R F c)))‖) ≤
        (Atop * Cδ + Ar2 * Z + Ar1 * Z) * (C5 * s5) +
          (βlow + β3) * s4 + (γlow + γ3) := by
    rw [Finset.sum_range_succ]
    refine le_trans (add_le_add hlowb hq3b) ?_
    dsimp only [βlow, γlow, β3, γ3]
    ring_nf
    linarith only [hC4, hs4nn]
  have hmass := cc_partial_le_norm (I := I) (M := M) g₀ 2 (3 : ℝ)
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
    (le_trans (Finset.sum_le_sum (fun q _ => by
      rw [iteratedCovGrad_add]; exact norm_add_le _ _)) hsum) hChs) ?_
  clear_value s5 s4 s3
  clear hs5def hs4def hs3def
  dsimp only [Kmid, Kadd, βlow, γlow, β3, γ3, Y, Z]
  ring_nf
  exact le_rfl

private theorem exists_galerkin_energy_four_bound_of_three_bound_parameters_raw_background (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop₃ Kr2 Kr1 Kcap : ℝ,
      0 ≤ Ctop₃ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
      ∀ {δ Ctop B1 ρ P T R3 : ℝ}
        (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
        (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
        (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ S) δ)
        (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ
          (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
            (ρ := ρ) hP.le hreal)))
        {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
        (_hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
        (_hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
          ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          HasDerivWithinAt (fun u => U N u i)
            (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
              galTameForce (I := I) (M := M) g₀ 1
                (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                  hδ hCtop hB1 hρ hP hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
            (Set.Ici t) t)
        (_hUinit : ∀ N i, U N 0 i = 0)
        (_hR3 : 0 ≤ R3)
        (_hE3 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) ≤ R3)
        {ε : ℝ}, 0 < ε →
          Ctop₃ * (Kcap * (δ / (1 - δ) ^ 2)) +
              Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
          ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t ≤ Φ := by
  classical
  obtain ⟨Ctop₃, Kr2, Kr1, Kcap, hCtop₃, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_action_h3_tame_bound_constants_background (I := I) (M := M) hDim g₀ g_bg
  refine ⟨Ctop₃, Kr2, Kr1, Kcap, hCtop₃, hKr2, hKr1, hKcap, ?_⟩
  intro δ Ctop B1 ρ P T R3 hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore U
    hUcont hUderiv hUinit hR3 hE3 ε hε hH
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  obtain ⟨Kmid, Kadd, hKmid, hKadd, hmass⟩ :=
    hord hRpos.le hδ hδ0 hδ3
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal) hR3
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  change Ctop₃ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 at hH
  obtain ⟨Cseed, hCseed, hseed⟩ :=
    exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g₀ g_bg hRpos hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
        (ρ := ρ) hP.le hreal) hcore
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i 4 *
            (U N t i * galTameForce (I := I) (M := M) g₀ 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i) ≤
        (2 * (Ctop₃ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) (4 + 1) t +
          (Kmid ^ 2 / ε + 0) * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t +
          2 * Cseed 4 * Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t) +
          Kadd ^ 2 / ε := by
    intro N t ht
    have hsplit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        galTameForce (I := I) (M := M) g₀ 1 hRpos.le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
              hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i =
          (galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i +
          (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
            hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i := by
      intro i hi
      rw [galForceArmBackground (I := I) (M := M) g₀ g_bg hδ hδ0 hδ3
        hCtop hB1 hρ hP hreal hcore
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i, if_pos hi]
      simp only [galerkinActionVectorBackground]
      module
    have hstat : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i 4 *
          ((boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
            hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i) ^ 2
          ≤ Cseed 4 ^ 2 := by
      have h := hseed 4 (eigenIdxFinset (I := I) (M := M) g₀ N)
      simpa only [boundedDeTurckRemainderOnLowerState, Nat.cast_ofNat] using h
    have hladder :
        Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i (4 - 1) *
              ((galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
                (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                  (ρ := ρ) hP.le hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N)
                (U N t)).coeff i) ^ 2) ≤
          (Ctop₃ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) *
              Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i (4 + 1) *
                  (U N t i) ^ 2) +
            Kmid * Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
              tensorSobolevWeight (I := I) (M := M) i 4 * (U N t i) ^ 2) +
            Kadd := by
      rw [show (4 - 1 : ℝ) = 3 by norm_num, show (4 + 1 : ℝ) = 5 by norm_num]
      exact hmass (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)
        (by simpa only [galerkinEnergy] using hE3 N t (Set.Ico_subset_Icc_self ht))
    have hres := two_sum_ladder_add_le (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (4 : ℝ) (U N t)
      (fun i => (galerkinActionVectorBackground (I := I) (M := M) g₀ g_bg hRpos.le hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal) (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i)
      (fun i => (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
        hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i)
      (galTameForce (I := I) (M := M) g₀ 1 hRpos.le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
          hδ hCtop hB1 hρ hP hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
      (hCseed 4) hε hsplit hladder hstat
    unfold galerkinEnergy
    simpa only [add_zero] using hres
  refine galerkin_l1_single (I := I) (M := M) (g := g₀) (r := 0) (s₀ := 2)
    (U := U) (T := T) (σ := 4)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g₀ 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g₀ N)
    (Cδ := 2 * (Ctop₃ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε)
    (Cmid := Kmid ^ 2 / ε) (seed := 2 * Cseed 4) (B0 := 0)
    (c₀ := Kadd ^ 2 / ε) (Sbd := 0)
    (A := fun _ _ => 0) (S := fun _ _ => 0)
    (by linarith) (div_nonneg (sq_nonneg _) hε.le) (by linarith [hCseed 4])
    (div_nonneg (sq_nonneg _) hε.le)
    (fun _ => rfl) (fun _ _ _ => le_rfl) (fun _ => continuousOn_const)
    (fun _ t _ => hasDerivWithinAt_const (x := t) (s := Set.Ici t) (c := (0 : ℝ)))
    (fun _ _ _ => le_rfl) hUcont hUderiv hclosure ?_
  intro N
  have hz : galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 0 = 0 := by
    unfold galerkinEnergy
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hUinit N i]
    ring
  rw [hz]

def HasGalerkinEnergyFourBoundBackground (g₀ g_bg : SmoothRiemannianMetric I M)
    (Ctop₃ Kr2 Kr1 Kcap : ℝ) : Prop :=
  0 ≤ Ctop₃ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
    ∀ {δ Ctop B1 ρ P T R3 : ℝ}
      (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
          (ρ := ρ) hP.le hreal)))
      {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
      (_hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
      (_hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun u => U N u i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            galTameForce (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
          (Set.Ici t) t)
      (_hUinit : ∀ N i, U N 0 i = 0)
      (_hR3 : 0 ≤ R3)
      (_hE3 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) ≤ R3)
      {ε : ℝ}, 0 < ε →
        Ctop₃ * (Kcap * (δ / (1 - δ) ^ 2)) +
            Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t ≤ Φ

theorem exists_galerkin_energy_four_bound_parameters_background (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop₃ Kr2 Kr1 Kcap : ℝ,
      HasGalerkinEnergyFourBoundBackground (I := I) (M := M) g₀ g_bg Ctop₃ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₃, Kr2, Kr1, Kcap, hCtop₃, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_energy_four_bound_of_three_bound_parameters_raw_background (I := I) (M := M) hDim g₀ g_bg
  exact ⟨Ctop₃, Kr2, Kr1, Kcap, hCtop₃, hKr2, hKr1, hKcap, hord⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
