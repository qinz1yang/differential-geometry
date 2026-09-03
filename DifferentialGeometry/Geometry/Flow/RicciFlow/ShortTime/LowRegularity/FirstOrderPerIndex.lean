import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderPerIndex

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem sumPairLe (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (a b : ℕ) :
    ∑ i ∈ ({a, b} : Finset ℕ), f i ≤ f a + f b := by
  classical
  rcases eq_or_ne a b with rfl | hab
  · have hset : ({a, a} : Finset ℕ) = {a} := by simp
    rw [hset, Finset.sum_singleton]
    linarith only [hf a]
  · exact le_of_eq (Finset.sum_pair hab)

private theorem a1Term0Background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ C K : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            (operatorFieldApply (I := I) (M := M) g 2 2
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).zeroOrderCoefficient T)‖ ^ 2 ≤
          C q * (∑ i ∈ Finset.range (q - 1), K i *
                (1 + ∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (1 + ∑ j ∈ Finset.range (i + 4),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (∑ j ∈ Finset.range (q - i + 1),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
              K (q - 1) *
                (1 + ∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (1 + ∑ j ∈ Finset.range (q - 1 + 2),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
              K q *
                (1 + ∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (1 + ∑ j ∈ Finset.range (q + 2),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (∑ j ∈ Finset.range 3,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨K0t, K2t, hK0_nn, hK2_nn, htow⟩ :=
    zeroOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) hDim g g_bg
  choose Cs hCs_nn hCs using fun i : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 2 (2 + i)
  obtain ⟨Cd0, hCd0_nn, hCd0⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 2
  obtain ⟨Cd1, hCd1_nn, hCd1⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 3
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by rw [hDim]
  have hSp_nn : ∀ i : ℕ, (0 : ℝ) ≤
      ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p)) := fun i =>
    Finset.sum_nonneg (fun p _ => add_nonneg (hK0_nn _) (hK2_nn _))
  refine ⟨fun q => operatorFieldApplicationGdiag (E := E) q * (1 + (Cd0 ^ 2 + Cd1 ^ 2)),
    fun i => Cs i ^ 2 * (∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) +
      (K0t i + K2t i),
    fun q => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q) (by positivity),
    fun i => by
      have h1 : (0 : ℝ) ≤ Cs i ^ 2 *
          ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p)) :=
        mul_nonneg (sq_nonneg _) (hSp_nn i)
      have h2 := hK0_nn i
      have h3 := hK2_nn i
      linarith only [h1, h2, h3], ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ q
  set A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ with hA
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hJ_mono : ∀ {a b : ℕ}, a ≤ b → J a ≤ J b := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  set K : ℕ → ℝ := fun i => Cs i ^ 2 *
    (∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) +
      (K0t i + K2t i) with hK
  have hKb_le : ∀ i, Cs i ^ 2 *
      (∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) ≤ K i := by
    intro i
    have h := add_nonneg (hK0_nn i) (hK2_nn i)
    rw [hK]
    linarith only [h]
  have hKt_le : ∀ i, K0t i + K2t i ≤ K i := by
    intro i
    have h1 : (0 : ℝ) ≤ Cs i ^ 2 *
        ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p)) :=
      mul_nonneg (sq_nonneg _) (hSp_nn i)
    rw [hK]
    linarith only [h1]
  have hK_nn : ∀ i, 0 ≤ K i := fun i =>
    le_trans (add_nonneg (hK0_nn i) (hK2_nn i)) (hKt_le i)
  have hH3 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) ≤ J 4 := by
    refine le_trans (le_of_eq ?_) (iteratedCovGradWinShift (I := I) (M := M) g 0 2 1 2 T)
    exact Finset.sum_congr rfl (fun l _ => by
      rw [DifferentialGeometry.Integral.Connection.iteratedCovGrad_norm_comp
        (I := I) (M := M) g 0 2 1 l T])
  have hcoeff : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient‖ ^ 2 ≤
        (K0t i + K2t i) * (1 + J 4) * (1 + J (i + 2)) := by
    intro i
    refine (htow T hT hδ0 hδ_le hδg hδZ i).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by linarith only [hJ_nn (i + 2)])
    have h1 : K2t i * (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) ≤ K2t i * J 4 :=
      mul_le_mul_of_nonneg_left hH3 (hK2_nn i)
    have h2 : (0 : ℝ) ≤ K0t i * J 4 := mul_nonneg (hK0_nn i) (hJ_nn 4)
    have h3 : (K0t i + K2t i) * (1 + J 4) =
        K0t i + K0t i * J 4 + (K2t i + K2t i * J 4) := by ring
    have h4 : (0 : ℝ) ≤ K2t i := hK2_nn i
    linarith only [h1, h2, h3, h4]
  have hsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
          ((iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient).toSection x) ≤
        (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
          ((1 + J 4) * (1 + J (i + 4))) := by
    intro i x
    have hemb := hCs i (iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient) x
    rw [hwin] at hemb
    refine hemb.trans ?_
    have hstep : ∀ p ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 (2 + i) p
            (iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient)‖ ^ 2 ≤
          (K0t (i + p) + K2t (i + p)) * ((1 + J 4) * (1 + J (i + 4))) := by
      intro p hp
      rw [Finset.mem_range] at hp
      rw [DifferentialGeometry.Integral.Connection.iteratedCovGrad_norm_comp
        (I := I) (M := M) g 2 2 i p A.zeroOrderCoefficient]
      refine (hcoeff (i + p)).trans ?_
      have hmono : 1 + J (i + p + 2) ≤ 1 + J (i + 4) := by
        have h := hJ_mono (a := i + p + 2) (b := i + 4) (by omega)
        linarith only [h]
      have hnn : (0 : ℝ) ≤ (K0t (i + p) + K2t (i + p)) * (1 + J 4) :=
        mul_nonneg (add_nonneg (hK0_nn _) (hK2_nn _))
          (by linarith only [hJ_nn 4])
      calc (K0t (i + p) + K2t (i + p)) * (1 + J 4) * (1 + J (i + p + 2))
          ≤ (K0t (i + p) + K2t (i + p)) * (1 + J 4) * (1 + J (i + 4)) :=
            mul_le_mul_of_nonneg_left hmono hnn
        _ = (K0t (i + p) + K2t (i + p)) * ((1 + J 4) * (1 + J (i + 4))) := by
            ring
    calc Cs i ^ 2 * ∑ p ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 (2 + i) p
            (iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient)‖ ^ 2
        ≤ Cs i ^ 2 * ∑ p ∈ Finset.range 3,
            (K0t (i + p) + K2t (i + p)) * ((1 + J 4) * (1 + J (i + 4))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (sq_nonneg _)
      _ = (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
            ((1 + J 4) * (1 + J (i + 4))) := by
          rw [← Finset.sum_mul]; ring
  have hCd2_nn : (0 : ℝ) ≤ Cd0 ^ 2 + Cd1 ^ 2 := by positivity
  have hdata0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
        Cd0 ^ 2 * J 3 := by
    intro x
    have h := hCd0 T x
    rw [hwin] at h
    exact h
  have hdata1 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) ≤
        Cd1 ^ 2 * J 4 := by
    intro x
    have h := hCd1 (iteratedCovGrad (I := I) g 0 2 1 T) x
    rw [hwin] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left
      (iteratedCovGradWinShift (I := I) (M := M) g 0 2 1 2 T) (sq_nonneg _)
  have hsub : Finset.range (q - 1) ⊆ Finset.range (q + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hEng := app_jet_sq_split (I := I) (M := M) g 2 2 q A.zeroOrderCoefficient T
    (Finset.range (q - 1)) hsub
    (fun i => (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
      ((1 + J 4) * (1 + J (i + 4))))
    (fun i => (Cd0 ^ 2 + Cd1 ^ 2) * J (q + 3 - i))
    (fun i _ x => hsup i x)
    (fun i hi x => by
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
      have h0 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g 0 2 0 T).toSection x) ≤
            Cd0 ^ 2 * J 3 := by
        simpa only [Nat.add_zero, iteratedCovGrad_zero] using hdata0 x
      by_cases hlt : i < q
      · rw [show q + 1 - i = 2 from by omega, show q + 3 - i = 4 from by omega,
          Finset.sum_range_succ, Finset.sum_range_one]
        have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) ≤
              Cd1 ^ 2 * J 4 := hdata1 x
        have h34 : J 3 ≤ J 4 := hJ_mono (by omega)
        nlinarith only [h0, h1, h34, sq_nonneg Cd0]
      · rw [show q + 1 - i = 1 from by omega, show q + 3 - i = 3 from by omega,
          Finset.sum_range_one]
        have hc1 : (0 : ℝ) ≤ Cd1 ^ 2 * J 3 :=
          mul_nonneg (sq_nonneg _) (hJ_nn 3)
        nlinarith only [h0, hc1])
  refine hEng.trans ?_
  have hsdiff : Finset.range (q + 1) \ Finset.range (q - 1) = {q - 1, q} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [hsdiff]
  have hPair := sumPairLe
    (fun i => (Cd0 ^ 2 + Cd1 ^ 2) * J (q + 3 - i) *
      ‖iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient‖ ^ 2)
    (fun i => mul_nonneg (mul_nonneg hCd2_nn (hJ_nn _)) (sq_nonneg _)) (q - 1) q
  have hSum : (∑ i ∈ Finset.range (q - 1),
      (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
        ((1 + J 4) * (1 + J (i + 4))) *
        ∑ l ∈ Finset.range (q + 1 - i),
          ‖iteratedCovGrad (I := I) g 0 2 l T‖ ^ 2) ≤
      (1 + (Cd0 ^ 2 + Cd1 ^ 2)) * ∑ i ∈ Finset.range (q - 1),
        K i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show q + 1 - i = q - i + 1 from by omega]
    have hP : (0 : ℝ) ≤ (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1) :=
      mul_nonneg (mul_nonneg (by linarith only [hJ_nn 4])
        (by linarith only [hJ_nn (i + 4)])) (hJ_nn _)
    have hnn : (0 : ℝ) ≤ K i * ((1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) :=
      mul_nonneg (hK_nn i) hP
    calc (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
          ((1 + J 4) * (1 + J (i + 4))) * J (q - i + 1)
        = (Cs i ^ 2 * ∑ p ∈ Finset.range 3, (K0t (i + p) + K2t (i + p))) *
            ((1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) := by ring
      _ ≤ K i * ((1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) :=
          mul_le_mul_of_nonneg_right (hKb_le i) hP
      _ ≤ (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K i * ((1 + J 4) * (1 + J (i + 4)) * J (q - i + 1))) :=
          le_mul_of_one_le_left hnn (by linarith only [hCd2_nn])
      _ = (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) := by ring
  have hMid : (Cd0 ^ 2 + Cd1 ^ 2) * J (q + 3 - (q - 1)) *
        ‖iteratedCovGrad (I := I) g 2 2 (q - 1) A.zeroOrderCoefficient‖ ^ 2 ≤
      (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
        (K (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4) := by
    have hfac : (0 : ℝ) ≤ (1 + J 4) * (1 + J (q - 1 + 2)) :=
      mul_nonneg (by linarith only [hJ_nn 4])
        (by linarith only [hJ_nn (q - 1 + 2)])
    have hcq : ‖iteratedCovGrad (I := I) g 2 2 (q - 1) A.zeroOrderCoefficient‖ ^ 2 ≤
        K (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) := by
      refine (hcoeff (q - 1)).trans ?_
      calc (K0t (q - 1) + K2t (q - 1)) * (1 + J 4) * (1 + J (q - 1 + 2))
          = (K0t (q - 1) + K2t (q - 1)) * ((1 + J 4) * (1 + J (q - 1 + 2))) := by
            ring
        _ ≤ K (q - 1) * ((1 + J 4) * (1 + J (q - 1 + 2))) :=
            mul_le_mul_of_nonneg_right (hKt_le (q - 1)) hfac
        _ = K (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) := by ring
    have hnn : (0 : ℝ) ≤
        K (q - 1) * ((1 + J 4) * (1 + J (q - 1 + 2)) * J 4) :=
      mul_nonneg (hK_nn (q - 1)) (mul_nonneg hfac (hJ_nn 4))
    calc (Cd0 ^ 2 + Cd1 ^ 2) * J (q + 3 - (q - 1)) *
          ‖iteratedCovGrad (I := I) g 2 2 (q - 1) A.zeroOrderCoefficient‖ ^ 2
        ≤ (Cd0 ^ 2 + Cd1 ^ 2) * J 4 *
            ‖iteratedCovGrad (I := I) g 2 2 (q - 1) A.zeroOrderCoefficient‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hJ_mono (by omega)) hCd2_nn)
            (sq_nonneg _)
      _ ≤ (Cd0 ^ 2 + Cd1 ^ 2) * J 4 *
            (K (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2))) :=
          mul_le_mul_of_nonneg_left hcq (mul_nonneg hCd2_nn (hJ_nn 4))
      _ = (Cd0 ^ 2 + Cd1 ^ 2) *
            (K (q - 1) * ((1 + J 4) * (1 + J (q - 1 + 2)) * J 4)) := by ring
      _ ≤ (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K (q - 1) * ((1 + J 4) * (1 + J (q - 1 + 2)) * J 4)) :=
          mul_le_mul_of_nonneg_right (by linarith only []) hnn
      _ = (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4) := by ring
  have hTop : (Cd0 ^ 2 + Cd1 ^ 2) * J (q + 3 - q) *
        ‖iteratedCovGrad (I := I) g 2 2 q A.zeroOrderCoefficient‖ ^ 2 ≤
      (1 + (Cd0 ^ 2 + Cd1 ^ 2)) * (K q * (1 + J 4) * (1 + J (q + 2)) * J 3) := by
    rw [show q + 3 - q = 3 from by omega]
    have hfac : (0 : ℝ) ≤ (1 + J 4) * (1 + J (q + 2)) :=
      mul_nonneg (by linarith only [hJ_nn 4]) (by linarith only [hJ_nn (q + 2)])
    have hcq : ‖iteratedCovGrad (I := I) g 2 2 q A.zeroOrderCoefficient‖ ^ 2 ≤
        K q * (1 + J 4) * (1 + J (q + 2)) := by
      refine (hcoeff q).trans ?_
      calc (K0t q + K2t q) * (1 + J 4) * (1 + J (q + 2))
          = (K0t q + K2t q) * ((1 + J 4) * (1 + J (q + 2))) := by ring
        _ ≤ K q * ((1 + J 4) * (1 + J (q + 2))) :=
            mul_le_mul_of_nonneg_right (hKt_le q) hfac
        _ = K q * (1 + J 4) * (1 + J (q + 2)) := by ring
    have hnn : (0 : ℝ) ≤ K q * ((1 + J 4) * (1 + J (q + 2)) * J 3) :=
      mul_nonneg (hK_nn q) (mul_nonneg hfac (hJ_nn 3))
    calc (Cd0 ^ 2 + Cd1 ^ 2) * J 3 *
          ‖iteratedCovGrad (I := I) g 2 2 q A.zeroOrderCoefficient‖ ^ 2
        ≤ (Cd0 ^ 2 + Cd1 ^ 2) * J 3 * (K q * (1 + J 4) * (1 + J (q + 2))) :=
          mul_le_mul_of_nonneg_left hcq (mul_nonneg hCd2_nn (hJ_nn 3))
      _ = (Cd0 ^ 2 + Cd1 ^ 2) * (K q * ((1 + J 4) * (1 + J (q + 2)) * J 3)) := by
          ring
      _ ≤ (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K q * ((1 + J 4) * (1 + J (q + 2)) * J 3)) :=
          mul_le_mul_of_nonneg_right (by linarith only []) hnn
      _ = (1 + (Cd0 ^ 2 + Cd1 ^ 2)) *
            (K q * (1 + J 4) * (1 + J (q + 2)) * J 3) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (add_le_add hSum (hPair.trans (add_le_add hMid hTop)))
    (operatorFieldApplicationGdiag_nonneg (E := E) q)) (le_of_eq ?_)
  ring

private theorem a1Term1Background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ C K : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            (operatorFieldApply (I := I) (M := M) g 3 2
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 1 T))‖ ^ 2 ≤
          C q * (∑ i ∈ Finset.range q, K i *
                (1 + ∑ j ∈ Finset.range (i + 4),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (∑ j ∈ Finset.range (q - i + 2),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
              K q *
                (1 + ∑ j ∈ Finset.range (q + 2),
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                (∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Kc, hKc_nn, htow⟩ := firstOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) g g_bg
  choose Cs hCs_nn hCs using fun i : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 3 (2 + i)
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 3
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by rw [hDim]
  have hSp_nn : ∀ i : ℕ, (0 : ℝ) ≤ ∑ p ∈ Finset.range 3, Kc (i + p) := fun i =>
    Finset.sum_nonneg (fun p _ => hKc_nn _)
  refine ⟨fun q => operatorFieldApplicationGdiag (E := E) q * (1 + Cd ^ 2),
    fun i => Cs i ^ 2 * (∑ p ∈ Finset.range 3, Kc (i + p)) + Kc i,
    fun q => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q) (by positivity),
    fun i => by
      have h1 : (0 : ℝ) ≤ Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p) :=
        mul_nonneg (sq_nonneg _) (hSp_nn i)
      linarith only [h1, hKc_nn i], ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ q
  set A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ with hA
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hJ_mono : ∀ {a b : ℕ}, a ≤ b → J a ≤ J b := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  set K : ℕ → ℝ := fun i =>
    Cs i ^ 2 * (∑ p ∈ Finset.range 3, Kc (i + p)) + Kc i with hK
  have hKb_le : ∀ i, Cs i ^ 2 * (∑ p ∈ Finset.range 3, Kc (i + p)) ≤ K i := by
    intro i
    rw [hK]
    linarith only [hKc_nn i]
  have hKt_le : ∀ i, Kc i ≤ K i := by
    intro i
    have h1 : (0 : ℝ) ≤ Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p) :=
      mul_nonneg (sq_nonneg _) (hSp_nn i)
    rw [hK]
    linarith only [h1]
  have hK_nn : ∀ i, 0 ≤ K i := fun i => le_trans (hKc_nn i) (hKt_le i)
  have hcoeff : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient‖ ^ 2 ≤ Kc i * (1 + J (i + 2)) :=
    fun i => htow T hT hδ0 hδ_le hδg hδZ i
  have hshift : ∀ n : ℕ,
      (∑ p ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 3 p
          (iteratedCovGrad (I := I) g 0 2 1 T)‖ ^ 2) ≤ J (n + 2) :=
    fun n => iteratedCovGradWinShift (I := I) (M := M) g 0 2 1 n T
  have hsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 3 (2 + i) x
          ((iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient).toSection x) ≤
        (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) := by
    intro i x
    have hemb := hCs i (iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient) x
    rw [hwin] at hemb
    refine hemb.trans ?_
    have hstep : ∀ p ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 (2 + i) p
            (iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient)‖ ^ 2 ≤
          Kc (i + p) * (1 + J (i + 4)) := by
      intro p hp
      rw [Finset.mem_range] at hp
      rw [DifferentialGeometry.Integral.Connection.iteratedCovGrad_norm_comp
        (I := I) (M := M) g 3 2 i p A.firstOrderCoefficient]
      refine (hcoeff (i + p)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
      have h := hJ_mono (a := i + p + 2) (b := i + 4) (by omega)
      linarith only [h]
    calc Cs i ^ 2 * ∑ p ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 3 (2 + i) p
            (iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient)‖ ^ 2
        ≤ Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p) * (1 + J (i + 4)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (sq_nonneg _)
      _ = (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) := by
          rw [← Finset.sum_mul]; ring
  have hdata : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) ≤
        Cd ^ 2 * J 4 := by
    intro x
    have h := hCd (iteratedCovGrad (I := I) g 0 2 1 T) x
    rw [hwin] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (hshift 2) (sq_nonneg _)
  have hsub : Finset.range q ⊆ Finset.range (q + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hEng := app_jet_sq_split (I := I) (M := M) g 3 2 q A.firstOrderCoefficient
    (iteratedCovGrad (I := I) g 0 2 1 T) (Finset.range q) hsub
    (fun i => (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)))
    (fun _ => Cd ^ 2 * J 4)
    (fun i _ x => hsup i x)
    (fun i hi x => by
      have hiq : q + 1 - i = 1 := by
        rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
        omega
      rw [hiq, Finset.sum_range_one]
      simpa only [Nat.add_zero, iteratedCovGrad_zero] using hdata x)
  refine hEng.trans ?_
  have hsdiff : Finset.range (q + 1) \ Finset.range q = {q} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [hsdiff, Finset.sum_singleton]
  have hSum : (∑ i ∈ Finset.range q,
      (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) *
        ∑ l ∈ Finset.range (q + 1 - i),
          ‖iteratedCovGrad (I := I) g 0 3 l
            (iteratedCovGrad (I := I) g 0 2 1 T)‖ ^ 2) ≤
      (1 + Cd ^ 2) * ∑ i ∈ Finset.range q,
        K i * (1 + J (i + 4)) * J (q - i + 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hwindow : (∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 3 l
          (iteratedCovGrad (I := I) g 0 2 1 T)‖ ^ 2) ≤ J (q - i + 2) := by
      have h := hshift (q - i)
      rw [show q - i + 1 = q + 1 - i from by omega] at h
      exact h
    have hBnn : (0 : ℝ) ≤
        (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (hSp_nn i))
        (by linarith only [hJ_nn (i + 4)])
    have hP : (0 : ℝ) ≤ (1 + J (i + 4)) * J (q - i + 2) :=
      mul_nonneg (by linarith only [hJ_nn (i + 4)]) (hJ_nn _)
    have hnn : (0 : ℝ) ≤ K i * ((1 + J (i + 4)) * J (q - i + 2)) :=
      mul_nonneg (hK_nn i) hP
    calc (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) *
          ∑ l ∈ Finset.range (q + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 3 l
              (iteratedCovGrad (I := I) g 0 2 1 T)‖ ^ 2
        ≤ (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) * (1 + J (i + 4)) *
            J (q - i + 2) := mul_le_mul_of_nonneg_left hwindow hBnn
      _ = (Cs i ^ 2 * ∑ p ∈ Finset.range 3, Kc (i + p)) *
            ((1 + J (i + 4)) * J (q - i + 2)) := by ring
      _ ≤ K i * ((1 + J (i + 4)) * J (q - i + 2)) :=
          mul_le_mul_of_nonneg_right (hKb_le i) hP
      _ ≤ (1 + Cd ^ 2) * (K i * ((1 + J (i + 4)) * J (q - i + 2))) := by
          nlinarith only [hnn, sq_nonneg Cd]
      _ = (1 + Cd ^ 2) * (K i * (1 + J (i + 4)) * J (q - i + 2)) := by ring
  have hTop : Cd ^ 2 * J 4 * ‖iteratedCovGrad (I := I) g 3 2 q A.firstOrderCoefficient‖ ^ 2 ≤
      (1 + Cd ^ 2) * (K q * (1 + J (q + 2)) * J 4) := by
    have hfac : (0 : ℝ) ≤ 1 + J (q + 2) := by linarith only [hJ_nn (q + 2)]
    have hcq : ‖iteratedCovGrad (I := I) g 3 2 q A.firstOrderCoefficient‖ ^ 2 ≤
        K q * (1 + J (q + 2)) :=
      (hcoeff q).trans (mul_le_mul_of_nonneg_right (hKt_le q) hfac)
    have hnn : (0 : ℝ) ≤ K q * ((1 + J (q + 2)) * J 4) :=
      mul_nonneg (hK_nn q) (mul_nonneg hfac (hJ_nn 4))
    calc Cd ^ 2 * J 4 * ‖iteratedCovGrad (I := I) g 3 2 q A.firstOrderCoefficient‖ ^ 2
        ≤ Cd ^ 2 * J 4 * (K q * (1 + J (q + 2))) :=
          mul_le_mul_of_nonneg_left hcq (mul_nonneg (sq_nonneg _) (hJ_nn 4))
      _ = Cd ^ 2 * (K q * ((1 + J (q + 2)) * J 4)) := by ring
      _ ≤ (1 + Cd ^ 2) * (K q * ((1 + J (q + 2)) * J 4)) := by
          nlinarith only [hnn, sq_nonneg Cd]
      _ = (1 + Cd ^ 2) * (K q * (1 + J (q + 2)) * J 4) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hSum hTop)
    (operatorFieldApplicationGdiag_nonneg (E := E) q)) (le_of_eq ?_)
  ring

private theorem sqAddLe {a b s : ℝ} (h0 : 0 ≤ s) (h : s ≤ a + b) :
    s ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [mul_self_le_mul_self h0 h, sq_nonneg (a - b)]

private theorem combine2 {a b c d u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : a ≤ c * u) (h2 : b ≤ d * v) :
    2 * a + 2 * b ≤ 2 * (c + d) * (u + v) := by
  nlinarith [mul_nonneg hc hv, mul_nonneg hd hu]

theorem firstOrderAction_perIndex_jet_bound_background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K0 K1 : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K1 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ^ 2 ≤
          Cq q * ((∑ i ∈ Finset.range (q - 1), K0 i *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range (q - i + 1),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 (q - 1) *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (q - 1 + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 q *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
            (∑ i ∈ Finset.range q, K1 i *
                  (1 + ∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range (q - i + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K1 q *
                  (1 + ∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2))) := by
  classical
  obtain ⟨C0, K0, hC0_nn, hK0_nn, harm0⟩ :=
    a1Term0Background (I := I) (M := M) hDim g g_bg
  obtain ⟨C1, K1, hC1_nn, hK1_nn, harm1⟩ :=
    a1Term1Background (I := I) (M := M) hDim g g_bg
  refine ⟨fun q => 2 * (C0 q + C1 q), K0, K1,
    fun q => by linarith only [hC0_nn q, hC1_nn q], hK0_nn, hK1_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ q
  set A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ with hA
  have hJ_nn : ∀ n : ℕ, (0 : ℝ) ≤ ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hshape : A.firstOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient T +
        operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
          (iteratedCovGrad (I := I) g 0 2 1 T) := rfl
  rw [hshape, iteratedCovGrad_add]
  refine le_trans (sqAddLe (norm_nonneg _) (norm_add_le _ _)) ?_
  refine combine2 ?_ ?_ (hC0_nn q) (hC1_nn q)
    (harm0 T hT hδ0 hδ_le hδg hδZ q) (harm1 T hT hδ0 hδ_le hδg hδZ q)
  · refine add_nonneg (add_nonneg (Finset.sum_nonneg (fun i _ => ?_)) ?_) ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn i)
        (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (i + 4)]))
        (hJ_nn _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn (q - 1))
        (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (q - 1 + 2)]))
        (hJ_nn _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn q)
        (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (q + 2)]))
        (hJ_nn _)
  · refine add_nonneg (Finset.sum_nonneg (fun i _ => ?_)) ?_
    · exact mul_nonneg (mul_nonneg (hK1_nn i)
        (by linarith only [hJ_nn (i + 4)])) (hJ_nn _)
    · exact mul_nonneg (mul_nonneg (hK1_nn q)
        (by linarith only [hJ_nn (q + 2)])) (hJ_nn _)

theorem firstOrderAction_perIndex_jet_bound (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Cq K0 K1 : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K1 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ^ 2 ≤
          Cq q * ((∑ i ∈ Finset.range (q - 1), K0 i *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range (q - i + 1),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 (q - 1) *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (q - 1 + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 q *
                  (1 + ∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (1 + ∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
            (∑ i ∈ Finset.range q, K1 i *
                  (1 + ∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range (q - i + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K1 q *
                  (1 + ∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
                  (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2))) :=
  firstOrderAction_perIndex_jet_bound_background (I := I) (M := M) hDim g g

private theorem sqrtOnePlus (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  have hle : (1 : ℝ) + x ≤ (1 + Real.sqrt x) ^ 2 := by
    have := Real.sq_sqrt hx
    nlinarith [Real.sqrt_nonneg x]
  calc Real.sqrt (1 + x) ≤ Real.sqrt ((1 + Real.sqrt x) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = 1 + Real.sqrt x := Real.sqrt_sq (by positivity)

theorem firstOrderAction_perIndex_linear_bound_background (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K0 K1 : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K1 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ≤
          Cq q * ((∑ i ∈ Finset.range (q - 1), K0 i *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range (q - i + 1),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 (q - 1) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q - 1 + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 q *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
            (∑ i ∈ Finset.range q, K1 i *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range (q - i + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K1 q *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2))) := by
  classical
  obtain ⟨Cq, K0, K1, hCq_nn, hK0_nn, hK1_nn, hsq⟩ :=
    firstOrderAction_perIndex_jet_bound_background (I := I) (M := M) hDim g g_bg
  refine ⟨fun q => Real.sqrt (Cq q), fun i => Real.sqrt (K0 i),
    fun i => Real.sqrt (K1 i), fun q => Real.sqrt_nonneg _,
    fun i => Real.sqrt_nonneg _, fun i => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ q
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hterm0 : ∀ i : ℕ,
      0 ≤ K0 i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1) := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn i)
      (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (i + 4)]))
      (hJ_nn _)
  have hmid0 : (0 : ℝ) ≤ K0 (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn (q - 1))
      (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (q - 1 + 2)]))
      (hJ_nn _)
  have htop0 : (0 : ℝ) ≤ K0 q * (1 + J 4) * (1 + J (q + 2)) * J 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hK0_nn q)
      (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (q + 2)]))
      (hJ_nn _)
  have hterm1 : ∀ i : ℕ,
      0 ≤ K1 i * (1 + J (i + 4)) * J (q - i + 2) := fun i =>
    mul_nonneg (mul_nonneg (hK1_nn i) (by linarith only [hJ_nn (i + 4)]))
      (hJ_nn _)
  have htop1 : (0 : ℝ) ≤ K1 q * (1 + J (q + 2)) * J 4 :=
    mul_nonneg (mul_nonneg (hK1_nn q) (by linarith only [hJ_nn (q + 2)]))
      (hJ_nn _)
  have hS0_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (q - 1),
      K0 i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1) :=
    Finset.sum_nonneg (fun i _ => hterm0 i)
  have hS1_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range q,
      K1 i * (1 + J (i + 4)) * J (q - i + 2) :=
    Finset.sum_nonneg (fun i _ => hterm1 i)
  have hSM0_nn : (0 : ℝ) ≤ (∑ i ∈ Finset.range (q - 1),
      K0 i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) +
      K0 (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4 :=
    add_nonneg hS0_nn hmid0
  have hA0_nn : (0 : ℝ) ≤ ((∑ i ∈ Finset.range (q - 1),
      K0 i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) +
      K0 (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4) +
      K0 q * (1 + J 4) * (1 + J (q + 2)) * J 3 := add_nonneg hSM0_nn htop0
  have hA1_nn : (0 : ℝ) ≤ (∑ i ∈ Finset.range q,
      K1 i * (1 + J (i + 4)) * J (q - i + 2)) +
      K1 q * (1 + J (q + 2)) * J 4 := add_nonneg hS1_nn htop1
  have h := hsq T hT hδ0 hδ_le hδg hδZ q
  have hroot : ‖iteratedCovGrad (I := I) g 0 2 q
      ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
          (I := I) (M := M) T)‖ ≤
      Real.sqrt (Cq q) * Real.sqrt
        ((((∑ i ∈ Finset.range (q - 1),
              K0 i * (1 + J 4) * (1 + J (i + 4)) * J (q - i + 1)) +
              K0 (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) * J 4) +
            K0 q * (1 + J 4) * (1 + J (q + 2)) * J 3) +
          ((∑ i ∈ Finset.range q,
              K1 i * (1 + J (i + 4)) * J (q - i + 2)) +
            K1 q * (1 + J (q + 2)) * J 4)) := by
    have hs := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (hCq_nn q)] at hs
    exact hs
  refine hroot.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine le_trans (sqrtAdd2 _ _ hA0_nn hA1_nn) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (sqrtAdd2 _ _ hSM0_nn htop0) ?_
    refine add_le_add (le_trans (sqrtAdd2 _ _ hS0_nn hmid0) ?_) ?_
    · refine add_le_add ?_ ?_
      · refine le_trans (sqrtFinSum (Finset.range (q - 1)) _ hterm0) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 : Real.sqrt (K0 i * (1 + J 4) * (1 + J (i + 4)) *
              J (q - i + 1)) =
            Real.sqrt (K0 i) * Real.sqrt (1 + J 4) *
              Real.sqrt (1 + J (i + 4)) * Real.sqrt (J (q - i + 1)) := by
          rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (hK0_nn i)
              (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (i + 4)])),
            Real.sqrt_mul (mul_nonneg (hK0_nn i)
              (by linarith only [hJ_nn 4])),
            Real.sqrt_mul (hK0_nn i)]
        rw [h1]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        refine mul_le_mul ?_ (sqrtOnePlus _ (hJ_nn (i + 4)))
          (Real.sqrt_nonneg _) ?_
        · exact mul_le_mul_of_nonneg_left (sqrtOnePlus _ (hJ_nn 4))
            (Real.sqrt_nonneg _)
        · exact mul_nonneg (Real.sqrt_nonneg _)
            (by linarith only [Real.sqrt_nonneg (J 4)])
      · have h1 : Real.sqrt (K0 (q - 1) * (1 + J 4) * (1 + J (q - 1 + 2)) *
              J 4) =
            Real.sqrt (K0 (q - 1)) * Real.sqrt (1 + J 4) *
              Real.sqrt (1 + J (q - 1 + 2)) * Real.sqrt (J 4) := by
          rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (hK0_nn (q - 1))
              (by linarith only [hJ_nn 4]))
              (by linarith only [hJ_nn (q - 1 + 2)])),
            Real.sqrt_mul (mul_nonneg (hK0_nn (q - 1))
              (by linarith only [hJ_nn 4])),
            Real.sqrt_mul (hK0_nn (q - 1))]
        rw [h1]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        refine mul_le_mul ?_ (sqrtOnePlus _ (hJ_nn (q - 1 + 2)))
          (Real.sqrt_nonneg _) ?_
        · exact mul_le_mul_of_nonneg_left (sqrtOnePlus _ (hJ_nn 4))
            (Real.sqrt_nonneg _)
        · exact mul_nonneg (Real.sqrt_nonneg _)
            (by linarith only [Real.sqrt_nonneg (J 4)])
    · have h1 : Real.sqrt (K0 q * (1 + J 4) * (1 + J (q + 2)) * J 3) =
          Real.sqrt (K0 q) * Real.sqrt (1 + J 4) *
            Real.sqrt (1 + J (q + 2)) * Real.sqrt (J 3) := by
        rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (hK0_nn q)
            (by linarith only [hJ_nn 4])) (by linarith only [hJ_nn (q + 2)])),
          Real.sqrt_mul (mul_nonneg (hK0_nn q)
            (by linarith only [hJ_nn 4])),
          Real.sqrt_mul (hK0_nn q)]
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul ?_ (sqrtOnePlus _ (hJ_nn (q + 2)))
        (Real.sqrt_nonneg _) ?_
      · exact mul_le_mul_of_nonneg_left (sqrtOnePlus _ (hJ_nn 4))
          (Real.sqrt_nonneg _)
      · exact mul_nonneg (Real.sqrt_nonneg _)
          (by linarith only [Real.sqrt_nonneg (J 4)])
  · refine le_trans (sqrtAdd2 _ _ hS1_nn htop1) ?_
    refine add_le_add ?_ ?_
    · refine le_trans (sqrtFinSum (Finset.range q) _ hterm1) ?_
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 : Real.sqrt (K1 i * (1 + J (i + 4)) * J (q - i + 2)) =
          Real.sqrt (K1 i) * Real.sqrt (1 + J (i + 4)) *
            Real.sqrt (J (q - i + 2)) := by
        rw [Real.sqrt_mul (mul_nonneg (hK1_nn i)
            (by linarith only [hJ_nn (i + 4)])), Real.sqrt_mul (hK1_nn i)]
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left (sqrtOnePlus _ (hJ_nn (i + 4)))
        (Real.sqrt_nonneg _)
    · have h1 : Real.sqrt (K1 q * (1 + J (q + 2)) * J 4) =
          Real.sqrt (K1 q) * Real.sqrt (1 + J (q + 2)) *
            Real.sqrt (J 4) := by
        rw [Real.sqrt_mul (mul_nonneg (hK1_nn q)
            (by linarith only [hJ_nn (q + 2)])), Real.sqrt_mul (hK1_nn q)]
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left (sqrtOnePlus _ (hJ_nn (q + 2)))
        (Real.sqrt_nonneg _)

theorem firstOrderAction_perIndex_linear_bound (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Cq K0 K1 : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K1 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                (I := I) (M := M) T)‖ ≤
          Cq q * ((∑ i ∈ Finset.range (q - 1), K0 i *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range (q - i + 1),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 (q - 1) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q - 1 + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K0 q *
                  (1 + Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
            (∑ i ∈ Finset.range q, K1 i *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (i + 4),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range (q - i + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
                K1 q *
                  (1 + Real.sqrt (∑ j ∈ Finset.range (q + 2),
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
                  Real.sqrt (∑ j ∈ Finset.range 4,
                    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2))) :=
  firstOrderAction_perIndex_linear_bound_background (I := I) (M := M) hDim g g

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
