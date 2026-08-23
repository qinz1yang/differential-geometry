import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.H4Energy
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

theorem lowerScaleActions_covariantDerivative_four_tame_bound (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
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
            ((lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderCoefficient.toSection x) ≤
            Cδ ^ 2)
        {X W V Z : ℝ} (hW : 0 ≤ W) (hV : 0 ≤ V) (hZ : 0 ≤ Z)
        (h7 : Real.sqrt (∑ j ∈ Finset.range 7,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ X)
        (h6 : Real.sqrt (∑ j ∈ Finset.range 6,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ W)
        (h5 : Real.sqrt (∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ V)
        (h3 : Real.sqrt (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Z),
        ‖iteratedCovGrad (I := I) g 0 2 4
            ((lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
                (I := I) (M := M) T)‖ +
          ‖iteratedCovGrad (I := I) g 0 2 4
            ((lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ≤
          (Atop * Cδ + Ar2 * Z + Ar1 * Z) * X +
            Krem * (1 + V) ^ 3 * (1 + Z) * (1 + W) := by
  classical
  obtain ⟨Cqa, Ka, hCqa, hKa, ha2⟩ := secondOrderAction_perIndex_linear_bound (I := I) (M := M) hDim g g
  obtain ⟨Cqb, Kb0, Kb1, hCqb, hKb0, hKb1, ha1⟩ :=
    firstOrderAction_perIndex_linear_bound (I := I) (M := M) hDim g
  let Krem : ℝ := Cqa 4 * (Ka 1 + Ka 2 + Ka 3 + Ka 4) +
    Cqb 4 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
      Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4)
  have hKas : 0 ≤ Ka 1 + Ka 2 + Ka 3 + Ka 4 := by
    linarith only [hKa 1, hKa 2, hKa 3, hKa 4]
  have hKbs : 0 ≤ Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
      Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4 := by
    linarith only [hKb0 0, hKb0 1, hKb0 2, hKb0 3, hKb0 4,
      hKb1 0, hKb1 1, hKb1 2, hKb1 3, hKb1 4]
  have hKrem : 0 ≤ Krem := by
    dsimp only [Krem]
    exact add_nonneg (mul_nonneg (hCqa 4) hKas) (mul_nonneg (hCqb 4) hKbs)
  refine ⟨Cqa 4, Cqa 4 * Ka 4, Cqb 4 * Kb1 3, Krem,
    hCqa 4, mul_nonneg (hCqa 4) (hKa 4),
    mul_nonneg (hCqb 4) (hKb1 3), hKrem, ?_⟩
  intro T hT δ hδ0 hδ3 hδg hδZ Cδ hCδ hfib X W V Z hW hV hZ h7 h6 h5 h3
  have H24 := ha2 T hT hδ0 hδ3 hδg hδZ hCδ hfib 4
  have H14 := ha1 T hT hδ0 hδ3 hδg hδZ 4
  set J3 : ℝ := Real.sqrt (∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ3def
  set J4 : ℝ := Real.sqrt (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ4def
  set J5 : ℝ := Real.sqrt (∑ j ∈ Finset.range 5,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ5def
  set J6 : ℝ := Real.sqrt (∑ j ∈ Finset.range 6,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ6def
  set J7 : ℝ := Real.sqrt (∑ j ∈ Finset.range 7,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hJ7def
  simp only [show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} from rfl,
    Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ) by norm_num),
    Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by norm_num),
    Finset.sum_pair (show (3 : ℕ) ≠ 4 by norm_num), Nat.reduceAdd,
    Nat.reduceSub] at H24
  rw [← hJ3def, ← hJ4def, ← hJ5def, ← hJ6def, ← hJ7def] at H24
  simp only [show (Finset.range 3 : Finset ℕ) = {0, 1, 2} from rfl,
    Finset.sum_insert (show (0 : ℕ) ∉ ({1, 2} : Finset ℕ) by norm_num),
    Finset.sum_pair (show (1 : ℕ) ≠ 2 by norm_num),
    show (Finset.range 4 : Finset ℕ) = {0, 1, 2, 3} from rfl,
    Finset.sum_insert (show (0 : ℕ) ∉ ({1, 2, 3} : Finset ℕ) by norm_num),
    Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by norm_num),
    Finset.sum_pair (show (2 : ℕ) ≠ 3 by norm_num), Nat.reduceAdd,
    Nat.reduceSub] at H14 hJ3def hJ4def
  rw [← hJ3def, ← hJ4def, ← hJ5def, ← hJ6def, ← hJ7def] at H14
  have H24' :
      ‖iteratedCovGrad (I := I) g 0 2 4
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqa 4 * (Cδ * J7 + Ka 1 * (1 + J4) * J6 +
          Ka 2 * (1 + J5) * J5 + Ka 3 * (1 + J6) * J4 +
          Ka 4 * (1 + J7) * J3) := by
    calc
      _ ≤ _ := H24
      _ = _ := by ring
  have H14' :
      ‖iteratedCovGrad (I := I) g 0 2 4
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqb 4 * (Kb0 0 * (1 + J4) ^ 2 * J5 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J4 +
          (Kb0 2 + Kb0 4) * (1 + J4) * (1 + J6) * J3 +
          Kb1 0 * (1 + J4) * J6 + Kb1 1 * (1 + J5) * J5 +
          (Kb1 2 + Kb1 4) * (1 + J6) * J4 +
          Kb1 3 * (1 + J7) * J3) := by
    calc
      _ ≤ _ := H14
      _ = _ := by ring
  have hJ3nn : 0 ≤ J3 := by rw [hJ3def]; positivity
  have hJ4nn : 0 ≤ J4 := by rw [hJ4def]; positivity
  have hJ5nn : 0 ≤ J5 := by rw [hJ5def]; positivity
  have hJ6nn : 0 ≤ J6 := by rw [hJ6def]; positivity
  have hJ7nn : 0 ≤ J7 := by rw [hJ7def]; positivity
  have hJ3Z : J3 ≤ Z := by simpa only [hJ3def] using h3
  have hJ5V : J5 ≤ V := by simpa only [hJ5def] using h5
  have hJ6W : J6 ≤ W := by simpa only [hJ6def] using h6
  have hJ7X : J7 ≤ X := by simpa only [hJ7def] using h7
  have hJ45 : J4 ≤ J5 := by
    rw [hJ4def, hJ5def]
    simpa only [show (Finset.range 4 : Finset ℕ) = {0, 1, 2, 3} from rfl,
      Finset.sum_insert (show (0 : ℕ) ∉ ({1, 2, 3} : Finset ℕ) by norm_num),
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by norm_num),
      Finset.sum_pair (show (2 : ℕ) ≠ 3 by norm_num)] using
        (iteratedCovGrad_l2_window_mono (I := I) (M := M) (m := 4) (n := 5) g (by norm_num) T)
  have hJ4V : J4 ≤ V := le_trans hJ45 hJ5V
  let A : ℝ := (1 + V) ^ 3
  let B : ℝ := 1 + Z
  let D : ℝ := 1 + W
  let Q : ℝ := A * B * D
  have h1V : 0 ≤ 1 + V := by linarith only [hV]
  have hAnn : 0 ≤ A := by dsimp only [A]; positivity
  have hBnn : 0 ≤ B := by dsimp only [B]; linarith only [hZ]
  have hDnn : 0 ≤ D := by dsimp only [D]; linarith only [hW]
  have cubeLe : ∀ {a b c : ℝ}, 0 ≤ b → 0 ≤ c →
      a ≤ 1 + V → b ≤ 1 + V → c ≤ 1 + V → a * b * c ≤ A := by
    intro a b c hb hc ha hble hcle
    dsimp only [A]
    calc
      a * b * c ≤ (1 + V) * (1 + V) * (1 + V) :=
        mul_three_le_mul_three hb hc h1V h1V ha hble hcle
      _ = (1 + V) ^ 3 := by ring
  have hA1 : 1 ≤ A := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ A := cubeLe zero_le_one zero_le_one (by linarith only [hV])
        (by linarith only [hV]) (by linarith only [hV])
  have hJ4A : J4 ≤ A := by
    calc
      J4 = J4 * 1 * 1 := by ring
      _ ≤ A := cubeLe zero_le_one zero_le_one (by linarith only [hJ4V])
        (by linarith only [hV]) (by linarith only [hV])
  have h1J4A : 1 + J4 ≤ A := by
    calc
      1 + J4 = (1 + J4) * 1 * 1 := by ring
      _ ≤ A := cubeLe zero_le_one zero_le_one (by linarith only [hJ4V])
        (by linarith only [hV]) (by linarith only [hV])
  have hJ55A : (1 + J5) * J5 ≤ A := by
    calc
      (1 + J5) * J5 = 1 * (1 + J5) * J5 := by ring
      _ ≤ A := cubeLe (by linarith only [hJ5nn]) hJ5nn (by linarith only [hV])
        (by linarith only [hJ5V]) (by linarith only [hJ5V, hV])
  have hJ445A : (1 + J4) ^ 2 * J5 ≤ A := by
    calc
      (1 + J4) ^ 2 * J5 = (1 + J4) * (1 + J4) * J5 := by ring
      _ ≤ A := cubeLe (by linarith only [hJ4nn]) hJ5nn (by linarith only [hJ4V])
        (by linarith only [hJ4V]) (by linarith only [hJ5V, hV])
  have hJ454A : (1 + J4) * (1 + J5) * J4 ≤ A := by
    exact cubeLe (by linarith only [hJ5nn]) hJ4nn
      (by linarith only [hJ4V]) (by linarith only [hJ5V])
      (by linarith only [hJ4V, hV])
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith only [hZ]
  have hJ3B : J3 ≤ B := by dsimp only [B]; linarith only [hJ3Z, hZ]
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith only [hW]
  have hJ6D : J6 ≤ D := by dsimp only [D]; linarith only [hJ6W, hW]
  have h1J6D : 1 + J6 ≤ D := by dsimp only [D]; linarith only [hJ6W]
  have hQnn : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg (mul_nonneg hAnn hBnn) hDnn
  have e46 : (1 + J4) * J6 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) * J6 = (1 + J4) * 1 * J6 := by ring
      _ ≤ A * B * D := mul_three_le_mul_three zero_le_one hJ6nn hAnn hBnn h1J4A hB1 hJ6D
  have e55 : (1 + J5) * J5 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J5) * J5 = ((1 + J5) * J5) * 1 * 1 := by ring
      _ ≤ A * B * D := mul_three_le_mul_three zero_le_one zero_le_one hAnn hBnn hJ55A hB1 hD1
  have e64 : (1 + J6) * J4 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J6) * J4 = J4 * 1 * (1 + J6) := by ring
      _ ≤ A * B * D := mul_three_le_mul_three zero_le_one (by linarith only [hJ6nn])
        hAnn hBnn hJ4A hB1 h1J6D
  have e445 : (1 + J4) ^ 2 * J5 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) ^ 2 * J5 = ((1 + J4) ^ 2 * J5) * 1 * 1 := by ring
      _ ≤ A * B * D := mul_three_le_mul_three zero_le_one zero_le_one hAnn hBnn hJ445A hB1 hD1
  have e454 : (1 + J4) * (1 + J5) * J4 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) * (1 + J5) * J4 =
          ((1 + J4) * (1 + J5) * J4) * 1 * 1 := by ring
      _ ≤ A * B * D := mul_three_le_mul_three zero_le_one zero_le_one hAnn hBnn hJ454A hB1 hD1
  have e463 : (1 + J4) * (1 + J6) * J3 ≤ Q := by
    dsimp only [Q]
    calc
      (1 + J4) * (1 + J6) * J3 = (1 + J4) * J3 * (1 + J6) := by ring
      _ ≤ A * B * D := mul_three_le_mul_three hJ3nn (by linarith only [hJ6nn])
        hAnn hBnn h1J4A hJ3B h1J6D
  have eJ3 : J3 ≤ Q := by
    dsimp only [Q]
    calc
      J3 = 1 * J3 * 1 := by ring
      _ ≤ A * B * D := mul_three_le_mul_three hJ3nn zero_le_one hAnn hBnn hA1 hJ3B hD1
  have eTop : (1 + J7) * J3 ≤ Z * X + Q := by
    have hprod : J3 * J7 ≤ Z * X := mul_le_mul hJ3Z hJ7X hJ7nn hZ
    calc
      (1 + J7) * J3 = J3 * J7 + J3 := by ring
      _ ≤ Z * X + Q := add_le_add hprod eJ3
  clear_value J3 J4 J5 J6 J7
  clear hJ3def hJ4def hJ5def hJ6def hJ7def
  have b24 :
      ‖iteratedCovGrad (I := I) g 0 2 4
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).secondOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqa 4 * Cδ * X + Cqa 4 * Ka 4 * Z * X +
          Cqa 4 * (Ka 1 + Ka 2 + Ka 3 + Ka 4) * Q := by
    refine le_trans H24' ?_
    have t0 : Cδ * J7 ≤ Cδ * X := mul_le_mul_of_nonneg_left hJ7X hCδ
    have t1 : Ka 1 * ((1 + J4) * J6) ≤ Ka 1 * Q :=
      mul_le_mul_of_nonneg_left e46 (hKa 1)
    have t2 : Ka 2 * ((1 + J5) * J5) ≤ Ka 2 * Q :=
      mul_le_mul_of_nonneg_left e55 (hKa 2)
    have t3 : Ka 3 * ((1 + J6) * J4) ≤ Ka 3 * Q :=
      mul_le_mul_of_nonneg_left e64 (hKa 3)
    have t4 : Ka 4 * ((1 + J7) * J3) ≤ Ka 4 * (Z * X + Q) :=
      mul_le_mul_of_nonneg_left eTop (hKa 4)
    have hin : Cδ * J7 + Ka 1 * (1 + J4) * J6 + Ka 2 * (1 + J5) * J5 +
        Ka 3 * (1 + J6) * J4 + Ka 4 * (1 + J7) * J3 ≤
        Cδ * X + Ka 1 * Q + Ka 2 * Q + Ka 3 * Q + Ka 4 * (Z * X + Q) := by
      linarith only [t0, t1, t2, t3, t4]
    calc
      Cqa 4 * (Cδ * J7 + Ka 1 * (1 + J4) * J6 + Ka 2 * (1 + J5) * J5 +
          Ka 3 * (1 + J6) * J4 + Ka 4 * (1 + J7) * J3) ≤
        Cqa 4 * (Cδ * X + Ka 1 * Q + Ka 2 * Q + Ka 3 * Q +
          Ka 4 * (Z * X + Q)) := mul_le_mul_of_nonneg_left hin (hCqa 4)
      _ = Cqa 4 * Cδ * X + Cqa 4 * Ka 4 * Z * X +
          Cqa 4 * (Ka 1 + Ka 2 + Ka 3 + Ka 4) * Q := by ring
  have b14 :
      ‖iteratedCovGrad (I := I) g 0 2 4
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ3 (by norm_num)) hδg hδZ).firstOrderAction
              (I := I) (M := M) T)‖ ≤
        Cqb 4 * Kb1 3 * Z * X +
          Cqb 4 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4) * Q := by
    refine le_trans H14' ?_
    have t0 : Kb0 0 * ((1 + J4) ^ 2 * J5) ≤ Kb0 0 * Q :=
      mul_le_mul_of_nonneg_left e445 (hKb0 0)
    have t1 : (Kb0 1 + Kb0 3) * ((1 + J4) * (1 + J5) * J4) ≤
        (Kb0 1 + Kb0 3) * Q :=
      mul_le_mul_of_nonneg_left e454 (add_nonneg (hKb0 1) (hKb0 3))
    have t2 : (Kb0 2 + Kb0 4) * ((1 + J4) * (1 + J6) * J3) ≤
        (Kb0 2 + Kb0 4) * Q :=
      mul_le_mul_of_nonneg_left e463 (add_nonneg (hKb0 2) (hKb0 4))
    have t3 : Kb1 0 * ((1 + J4) * J6) ≤ Kb1 0 * Q :=
      mul_le_mul_of_nonneg_left e46 (hKb1 0)
    have t4 : Kb1 1 * ((1 + J5) * J5) ≤ Kb1 1 * Q :=
      mul_le_mul_of_nonneg_left e55 (hKb1 1)
    have t5 : (Kb1 2 + Kb1 4) * ((1 + J6) * J4) ≤
        (Kb1 2 + Kb1 4) * Q :=
      mul_le_mul_of_nonneg_left e64 (add_nonneg (hKb1 2) (hKb1 4))
    have t6 : Kb1 3 * ((1 + J7) * J3) ≤ Kb1 3 * (Z * X + Q) :=
      mul_le_mul_of_nonneg_left eTop (hKb1 3)
    have hin :
        Kb0 0 * (1 + J4) ^ 2 * J5 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J4 +
          (Kb0 2 + Kb0 4) * (1 + J4) * (1 + J6) * J3 +
          Kb1 0 * (1 + J4) * J6 + Kb1 1 * (1 + J5) * J5 +
          (Kb1 2 + Kb1 4) * (1 + J6) * J4 + Kb1 3 * (1 + J7) * J3 ≤
        Kb0 0 * Q + (Kb0 1 + Kb0 3) * Q + (Kb0 2 + Kb0 4) * Q +
          Kb1 0 * Q + Kb1 1 * Q + (Kb1 2 + Kb1 4) * Q +
          Kb1 3 * (Z * X + Q) := by
      linarith only [t0, t1, t2, t3, t4, t5, t6]
    calc
      Cqb 4 * (Kb0 0 * (1 + J4) ^ 2 * J5 +
          (Kb0 1 + Kb0 3) * (1 + J4) * (1 + J5) * J4 +
          (Kb0 2 + Kb0 4) * (1 + J4) * (1 + J6) * J3 +
          Kb1 0 * (1 + J4) * J6 + Kb1 1 * (1 + J5) * J5 +
          (Kb1 2 + Kb1 4) * (1 + J6) * J4 + Kb1 3 * (1 + J7) * J3) ≤
        Cqb 4 * (Kb0 0 * Q + (Kb0 1 + Kb0 3) * Q +
          (Kb0 2 + Kb0 4) * Q + Kb1 0 * Q + Kb1 1 * Q +
          (Kb1 2 + Kb1 4) * Q + Kb1 3 * (Z * X + Q)) :=
        mul_le_mul_of_nonneg_left hin (hCqb 4)
      _ = Cqb 4 * Kb1 3 * Z * X +
          Cqb 4 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4) * Q := by ring
  dsimp only [Krem]
  calc
    _ ≤ (Cqa 4 * Cδ * X + Cqa 4 * Ka 4 * Z * X +
          Cqa 4 * (Ka 1 + Ka 2 + Ka 3 + Ka 4) * Q) +
        (Cqb 4 * Kb1 3 * Z * X +
          Cqb 4 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4) * Q) := add_le_add b24 b14
    _ = (Cqa 4 * Cδ + (Cqa 4 * Ka 4) * Z + (Cqb 4 * Kb1 3) * Z) * X +
        (Cqa 4 * (Ka 1 + Ka 2 + Ka 3 + Ka 4) +
          Cqb 4 * (Kb0 0 + Kb0 1 + Kb0 2 + Kb0 3 + Kb0 4 +
            Kb1 0 + Kb1 1 + Kb1 2 + Kb1 3 + Kb1 4)) *
          (1 + V) ^ 3 * (1 + Z) * (1 + W) := by
      dsimp only [Q, A, B, D]
      ring

theorem exists_galerkin_action_h4_tame_bound_constants (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Ctop Kr2 Kr1 Kcap : ℝ,
      0 ≤ Ctop ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
      ∀ {R δ : ℝ} (hR : 0 ≤ R)
        (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
        (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ T) δ),
        ∀ {R3 R4 : ℝ}, 0 ≤ R3 → 0 ≤ R4 →
          ∃ Kmid Kadd : ℝ, 0 ≤ Kmid ∧ 0 ≤ Kadd ∧
            ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
              (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) ≤
                  R3 →
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) ≤
                  R4 →
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                  ((galerkinActionVector (I := I) (M := M) g₀ hR hδ hreal F c).coeff i) ^ 2) ≤
                (Ctop * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R) *
                    Real.sqrt (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (6 : ℝ) *
                        (c i) ^ 2) +
                  Kmid * Real.sqrt (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) *
                      (c i) ^ 2) + Kadd := by
  classical
  obtain ⟨A4top, A4r2, A4r1, A4rem, hA4top, hA4r2, hA4r1, hA4rem, hq4⟩ :=
    lowerScaleActions_covariantDerivative_four_tame_bound (I := I) (M := M) hDim g₀
  obtain ⟨A3top, A3r2, A3r1, A3rem, hA3top, hA3r2, hA3r1, hA3rem, hq3⟩ :=
    lowerScaleActions_covariantDerivative_three_tame_bound (I := I) (M := M) hDim g₀
  obtain ⟨Ltop, Lr2, Lr1, Lrem, hLtop, hLr2, hLr1, hLrem, hlow⟩ :=
    lowerScaleActions_covariantJetNorm_two_tame_bound (I := I) (M := M) hDim g₀
  obtain ⟨Kcap, hKcap, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  obtain ⟨Chs, hChs, hhs⟩ := hs_le_jet (I := I) (M := M) g₀ 2 4
  obtain ⟨C6, hC6, hjet6⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 6
  obtain ⟨C5, hC5, hjet5⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 5
  obtain ⟨C4, hC4, hjet4⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 4
  obtain ⟨C3, hC3, hjet3⟩ := galerkinRepresentation_iteratedCovGrad_sum_le (I := I) (M := M) g₀ 3
  obtain ⟨CR, hCR, hjetR⟩ := galerkinRepresentation_lowOrder_iteratedCovGrad_sum_le (I := I) (M := M) g₀
  simp only [Nat.cast_ofNat] at hjet6 hjet5 hjet4 hjet3 hhs
  refine ⟨Chs * C6 * A4top, Chs * C6 * A4r2 * CR,
    Chs * C6 * A4r1 * CR, Kcap,
    mul_nonneg (mul_nonneg hChs hC6) hA4top,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC6) hA4r2) hCR,
    mul_nonneg (mul_nonneg (mul_nonneg hChs hC6) hA4r1) hCR,
    hKcap, ?_⟩
  intro R δ hR hδ hδ0 hδ3 hreal R3 R4 hR3 hR4
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  let Y : ℝ := C3 * R3
  let V : ℝ := C4 * R4
  let Z : ℝ := CR * R
  have hCδ : 0 ≤ Cδ := by
    dsimp only [Cδ]
    exact mul_nonneg hKcap (div_nonneg hδ0 (sq_nonneg _))
  have hY : 0 ≤ Y := by dsimp only [Y]; exact mul_nonneg hC3 hR3
  have hV : 0 ≤ V := by dsimp only [V]; exact mul_nonneg hC4 hR4
  have hZ : 0 ≤ Z := by dsimp only [Z]; exact mul_nonneg hCR hR
  have hcap : ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
          ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
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
  let γlow : ℝ := (Ltop * Cδ + Lr2 * Z + Lr1 * Z) * V +
    Lrem * (1 + Cδ) * ((1 + Y) ^ 2 * (1 + Z) ^ 2)
  let β3 : ℝ := (A3top * Cδ + A3r2 * Z + A3r1 * Z) * C5
  let γ3 : ℝ := A3rem * (1 + Cδ) * ((1 + Y) ^ 3 * (1 + Z) ^ 2) * (1 + V)
  let β4 : ℝ := A4rem * (1 + V) ^ 3 * (1 + Z) * C5
  let γ4 : ℝ := A4rem * (1 + V) ^ 3 * (1 + Z)
  let Kmid : ℝ := Chs * (β3 + β4)
  let Kadd : ℝ := Chs * (γlow + γ3 + γ4)
  have hγlow : 0 ≤ γlow := by
    dsimp only [γlow]
    exact add_nonneg
      (mul_nonneg
        (add_nonneg (add_nonneg (mul_nonneg hLtop hCδ) (mul_nonneg hLr2 hZ))
          (mul_nonneg hLr1 hZ)) hV)
      (mul_nonneg (mul_nonneg hLrem (by linarith only [hCδ]))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hβ3 : 0 ≤ β3 := by
    dsimp only [β3]
    exact mul_nonneg
      (add_nonneg (add_nonneg (mul_nonneg hA3top hCδ) (mul_nonneg hA3r2 hZ))
        (mul_nonneg hA3r1 hZ)) hC5
  have hγ3 : 0 ≤ γ3 := by
    dsimp only [γ3]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA3rem (by linarith only [hCδ]))
        (mul_nonneg (by positivity) (sq_nonneg _))) (by linarith only [hV])
  have hβ4 : 0 ≤ β4 := by
    dsimp only [β4]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA4rem (by positivity)) (by linarith only [hZ])) hC5
  have hγ4 : 0 ≤ γ4 := by
    dsimp only [γ4]
    exact mul_nonneg (mul_nonneg hA4rem (by positivity)) (by linarith only [hZ])
  refine ⟨Kmid, Kadd,
    by dsimp only [Kmid]; exact mul_nonneg hChs (add_nonneg hβ3 hβ4),
    by dsimp only [Kadd]; exact mul_nonneg hChs (add_nonneg (add_nonneg hγlow hγ3) hγ4), ?_⟩
  intro F c hE3 hE4
  rw [show Kcap * (δ / (1 - δ) ^ 2) = Cδ by rfl]
  set s6 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (6 : ℝ) * (c i) ^ 2) with hs6def
  set s5 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) with hs5def
  set s4 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) with hs4def
  set s3 : ℝ := Real.sqrt (∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) with hs3def
  have hs6nn : 0 ≤ s6 := by rw [hs6def]; positivity
  have hs5nn : 0 ≤ s5 := by rw [hs5def]; positivity
  have hs4nn : 0 ≤ s4 := by rw [hs4def]; positivity
  have hs3nn : 0 ≤ s3 := by rw [hs3def]; positivity
  have hsym := ccTensorBilin_symmS_symm
    (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c)
  have h7 : Real.sqrt (∑ j ∈ Finset.range 7,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C6 * s6 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 7 _) (hjet6 hR F c)
  have h6 : Real.sqrt (∑ j ∈ Finset.range 6,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C5 * s5 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 6 _) (hjet5 hR F c)
  have h5raw : Real.sqrt (∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ C4 * s4 :=
    le_trans (iteratedCovGrad_l2_window_le_l1_window (I := I) (M := M) g₀ 5 _) (hjet4 hR F c)
  have h5 : Real.sqrt (∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ^ 2) ≤ V := by
    refine le_trans h5raw ?_
    dsimp only [V]
    exact mul_le_mul_of_nonneg_left (by simpa only [hs4def] using hE4) hC4
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
    hV hY hZ h6 h5 h4 h3
  have hq4b := hq4
    (symmS (I := I) (M := M) g₀
      (galCoreRep (I := I) (M := M) g₀ R F c)) hsym hδ0 hδ3
    (galRepFib (I := I) (M := M) g₀ hR hreal F c)
    (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal) hCδ (hcap F c)
    (mul_nonneg hC5 hs5nn) hV hZ h7 h6 h5 h3
  have hsum :
      ∑ q ∈ Finset.range 5,
          (‖iteratedCovGrad (I := I) g₀ 0 2 q
              ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
                (galRepFib (I := I) (M := M) g₀ hR hreal F c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderAction
                  (I := I) (M := M)
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀ R F c)))‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
                (galRepFib (I := I) (M := M) g₀ hR hreal F c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).firstOrderAction
                  (I := I) (M := M)
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀ R F c)))‖) ≤
        (A4top * Cδ + A4r2 * Z + A4r1 * Z) * (C6 * s6) +
          (β3 + β4) * s5 + (γlow + γ3 + γ4) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    refine le_trans (add_le_add (add_le_add hlowb hq3b) hq4b) ?_
    dsimp only [γlow, β3, γ3, β4, γ4]
    ring_nf
    exact le_rfl
  have hmass := cc_partial_le_norm (I := I) (M := M) g₀ 2 (4 : ℝ)
    ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
          (symmS (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderAction
        (I := I) (M := M)
        (symmS (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R F c)) +
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
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
  clear_value s6 s5 s4 s3
  clear hs6def hs5def hs4def hs3def
  dsimp only [Kmid, Kadd, γlow, β3, γ3, β4, γ4, Y, V, Z]
  ring_nf
  exact le_rfl

private theorem exists_galerkin_energy_five_bound_of_three_four_bounds_parameters_raw (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Ctop₄ Kr2 Kr1 Kcap : ℝ,
      0 ≤ Ctop₄ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
      ∀ {δ Ctop B1 ρ P T R3 R4 : ℝ}
        (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
        (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
        (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ S) δ)
        (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
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
                (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
              (Set.Ici t) t)
        (_hUinit : ∀ N i, U N 0 i = 0)
        (_hR3 : 0 ≤ R3)
        (_hE3 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) ≤ R3)
        (_hR4 : 0 ≤ R4)
        (_hE4 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t) ≤ R4)
        {ε : ℝ}, 0 < ε →
          Ctop₄ * (Kcap * (δ / (1 - δ) ^ 2)) +
              Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
          ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 5 t ≤ Φ := by
  classical
  obtain ⟨Ctop₄, Kr2, Kr1, Kcap, hCtop₄, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_action_h4_tame_bound_constants (I := I) (M := M) hDim g₀
  refine ⟨Ctop₄, Kr2, Kr1, Kcap, hCtop₄, hKr2, hKr1, hKcap, ?_⟩
  intro δ Ctop B1 ρ P T R3 R4 hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore U
    hUcont hUderiv hUinit hR3 hE3 hR4 hE4 ε hε hH
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  obtain ⟨Kmid, Kadd, hKmid, hKadd, hmass⟩ :=
    hord hRpos.le hδ hδ0 hδ3
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal) hR3 hR4
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  change Ctop₄ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 at hH
  obtain ⟨Cseed, hCseed, hseed⟩ := exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g₀ g₀
    hRpos hδ (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
      (ρ := ρ) hP.le hreal) hcore
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i 5 *
            (U N t i * galTameForce (I := I) (M := M) g₀ 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i) ≤
        (2 * (Ctop₄ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) (5 + 1) t +
          (Kmid ^ 2 / ε + 0) * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 5 t +
          2 * Cseed 5 * Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 5 t) +
          Kadd ^ 2 / ε := by
    intro N t ht
    have hsplit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        galTameForce (I := I) (M := M) g₀ 1 hRpos.le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i =
          (galerkinActionVector (I := I) (M := M) g₀ hRpos.le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i +
          (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i := by
      intro i hi
      rw [galForceArm (I := I) (M := M) g₀ hδ hδ0 hδ3 hCtop hB1 hρ hP hreal
        hcore (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i, if_pos hi]
      exact add_comm _ _
    have hstat : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i 5 *
          ((boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i) ^ 2
          ≤ Cseed 5 ^ 2 := by
      have h := hseed 5 (eigenIdxFinset (I := I) (M := M) g₀ N)
      simpa only [Nat.cast_ofNat] using h
    have hladder :
        Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i (5 - 1) *
              ((galerkinActionVector (I := I) (M := M) g₀ hRpos.le hδ
                (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                  (ρ := ρ) hP.le hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i) ^ 2) ≤
          (Ctop₄ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P) *
              Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i (5 + 1) *
                  (U N t i) ^ 2) +
            Kmid * Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
              tensorSobolevWeight (I := I) (M := M) i 5 * (U N t i) ^ 2) +
            Kadd := by
      rw [show (5 - 1 : ℝ) = 4 by norm_num, show (5 + 1 : ℝ) = 6 by norm_num]
      exact hmass (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)
        (by simpa only [galerkinEnergy] using hE3 N t (Set.Ico_subset_Icc_self ht))
        (by simpa only [galerkinEnergy] using hE4 N t (Set.Ico_subset_Icc_self ht))
    have hres := two_sum_ladder_add_le (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (5 : ℝ) (U N t)
      (fun i => (galerkinActionVector (I := I) (M := M) g₀ hRpos.le hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal) (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)).coeff i)
      (fun i => (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i)
      (galTameForce (I := I) (M := M) g₀ 1 hRpos.le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
      (hCseed 5) hε hsplit hladder hstat
    unfold galerkinEnergy
    simpa only [add_zero] using hres
  refine galerkin_l1_single (I := I) (M := M) (g := g₀) (r := 0) (s₀ := 2)
    (U := U) (T := T) (σ := 5)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g₀ 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g₀ N)
    (Cδ := 2 * (Ctop₄ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P) + 2 * ε)
    (Cmid := Kmid ^ 2 / ε) (seed := 2 * Cseed 5) (B0 := 0)
    (c₀ := Kadd ^ 2 / ε) (Sbd := 0)
    (A := fun _ _ => 0) (S := fun _ _ => 0)
    (by linarith) (div_nonneg (sq_nonneg _) hε.le) (by linarith [hCseed 5])
    (div_nonneg (sq_nonneg _) hε.le)
    (fun _ => rfl) (fun _ _ _ => le_rfl) (fun _ => continuousOn_const)
    (fun _ t _ => hasDerivWithinAt_const (x := t) (s := Set.Ici t) (c := (0 : ℝ)))
    (fun _ _ _ => le_rfl) hUcont hUderiv hclosure ?_
  intro N
  have hz : galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 5 0 = 0 := by
    unfold galerkinEnergy
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hUinit N i]
    ring
  rw [hz]

def HasGalerkinEnergyFiveBound (g₀ : SmoothRiemannianMetric I M)
    (Ctop₄ Kr2 Kr1 Kcap : ℝ) : Prop :=
  0 ≤ Ctop₄ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Kcap ∧
    ∀ {δ Ctop B1 ρ P T R3 R4 : ℝ}
      (hδ : δ < 1) (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
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
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
          (Set.Ici t) t)
      (_hUinit : ∀ N i, U N 0 i = 0)
      (_hR3 : 0 ≤ R3)
      (_hE3 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) ≤ R3)
      (_hR4 : 0 ≤ R4)
      (_hE4 : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 4 t) ≤ R4)
      {ε : ℝ}, 0 < ε →
        Ctop₄ * (Kcap * (δ / (1 - δ) ^ 2)) +
            Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 5 t ≤ Φ

theorem exists_galerkin_energy_five_bound_parameters (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Ctop₄ Kr2 Kr1 Kcap : ℝ,
      HasGalerkinEnergyFiveBound (I := I) (M := M) g₀ Ctop₄ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₄, Kr2, Kr1, Kcap, hCtop₄, hKr2, hKr1, hKcap, hord⟩ :=
    exists_galerkin_energy_five_bound_of_three_four_bounds_parameters_raw (I := I) (M := M) hDim g₀
  exact ⟨Ctop₄, Kr2, Kr1, Kcap, hCtop₄, hKr2, hKr1, hKcap, hord⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
