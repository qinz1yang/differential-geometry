import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.H1H2Composition

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped ContDiff Manifold Topology BigOperators ENNReal
open MeasureTheory
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem operatorFieldComposition_hn_sup_bound (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) ≤ A ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g p r x
          (W.toSection x) ≤ B ^ 2) →
        (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p c j
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          C n * (B ^ 2 * ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 +
              A ^ 2 * ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := by
  classical
  choose G hG hgrid using fun j : ℕ =>
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoTerm_rs_le
      (I := I) (M := M) g r p c r j
  refine ⟨fun n => ∑ j ∈ Finset.range (n + 1), operatorFieldApplicationGdiag (E := E) j * G j, ?_, ?_⟩
  · intro n
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) j) (hG j)
  intro n Φ W A B hA hB hΦsup hWsup
  set SΦ : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 with hSΦ_def
  set SW : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 with hSW_def
  have hSΦ_nn : (0 : ℝ) ≤ SΦ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSW_nn : (0 : ℝ) ≤ SW := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR_nn : (0 : ℝ) ≤ B ^ 2 * SΦ + A ^ 2 * SW := by positivity
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g p c j
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        operatorFieldApplicationGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by
    intro j hj
    have hjn : j + 1 ≤ n + 1 := by
      simp only [Finset.mem_range] at hj; omega
    set grid : M → ℝ := fun x =>
      ∑ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (c + m) x
            ((iteratedCovGrad (I := I) g r c m Φ).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
              ((iteratedCovGrad (I := I) g p r l W).toSection x) with hgrid_def
    obtain ⟨hgInt, hgBound⟩ := hgrid j Φ W A B hA hB hΦsup hWsup
    have hgInt' : Integrable grid (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [hgrid_def] using hgInt
    have hgBound' :
        (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G j * (B ^ 2 * (∑ m ∈ Finset.range (j + 1),
                ‖iteratedCovGrad (I := I) g r c m Φ‖ ^ 2) +
            A ^ 2 * ∑ l ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2) := by
      simpa only [hgrid_def] using hgBound
    have hΦwin : (∑ m ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g r c m Φ‖ ^ 2) ≤ SΦ := by
      rw [hSΦ_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
        (fun m _ _ => sq_nonneg _)
    have hWwin : (∑ l ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2) ≤ SW := by
      rw [hSW_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
        (fun l _ _ => sq_nonneg _)
    have hgFinal : (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by
      refine hgBound'.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (hG j))
      · exact mul_le_mul_of_nonneg_left hΦwin (sq_nonneg B)
      · exact mul_le_mul_of_nonneg_left hWwin (sq_nonneg A)
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + j)
      (iteratedCovGrad (I := I) g p c j
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W))
      (fun x => operatorFieldApplicationGdiag (E := E) j * grid x)
      (hgInt'.const_mul (operatorFieldApplicationGdiag (E := E) j))
      (fun x => by
        simpa only [hgrid_def] using
          (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
            (I := I) (M := M) g j p r c Φ W x))
    calc ‖iteratedCovGrad (I := I) g p c j
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2
        ≤ ∫ x, operatorFieldApplicationGdiag (E := E) j * grid x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hkey
      _ = operatorFieldApplicationGdiag (E := E) j *
            ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ operatorFieldApplicationGdiag (E := E) j * (G j * (B ^ 2 * SΦ + A ^ 2 * SW)) :=
          mul_le_mul_of_nonneg_left hgFinal (operatorFieldApplicationGdiag_nonneg (E := E) j)
      _ = operatorFieldApplicationGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by ring
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ ∑ j ∈ Finset.range (n + 1),
          operatorFieldApplicationGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (n + 1), operatorFieldApplicationGdiag (E := E) j * G j) *
          (B ^ 2 * SΦ + A ^ 2 * SW) := by
        rw [Finset.sum_mul]

theorem operatorFieldComposition_jet_mul (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ), Module.finrank ℝ E / 2 + 1 ≤ n →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
          (∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) g p c j
                (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
            C n * (∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) *
              ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := by
  classical
  obtain ⟨CΦ, hCΦ, hΦpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r c
  obtain ⟨CW, hCW, hWpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g p r
  obtain ⟨K, hK, hKle⟩ := operatorFieldComposition_hn_sup_bound (I := I) (M := M) g p r c
  refine ⟨fun n => K n * (CW ^ 2 + CΦ ^ 2), ?_, ?_⟩
  · intro n
    exact mul_nonneg (hK n) (by positivity)
  intro n hn Φ W
  set SΦ : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 with hSΦ_def
  set SW : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 with hSW_def
  have hSΦ_nn : (0 : ℝ) ≤ SΦ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSW_nn : (0 : ℝ) ≤ SW := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hwin : Module.finrank ℝ E / 2 + 2 ≤ n + 1 := by omega
  set A : ℝ := CΦ * Real.sqrt SΦ with hA_def
  set B : ℝ := CW * Real.sqrt SW with hB_def
  have hA : (0 : ℝ) ≤ A := mul_nonneg hCΦ (Real.sqrt_nonneg _)
  have hB : (0 : ℝ) ≤ B := mul_nonneg hCW (Real.sqrt_nonneg _)
  have hA2 : A ^ 2 = CΦ ^ 2 * SΦ := by
    rw [hA_def, mul_pow, Real.sq_sqrt hSΦ_nn]
  have hB2 : B ^ 2 = CW ^ 2 * SW := by
    rw [hB_def, mul_pow, Real.sq_sqrt hSW_nn]
  have hΦsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r c x
      (Φ.toSection x) ≤ A ^ 2 := by
    intro x
    refine (hΦpt Φ x).trans ?_
    rw [hA2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CΦ)
    rw [hSΦ_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun j _ _ => sq_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g p r x
      (W.toSection x) ≤ B ^ 2 := by
    intro x
    refine (hWpt W x).trans ?_
    rw [hB2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CW)
    rw [hSW_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun j _ _ => sq_nonneg _)
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ K n * (B ^ 2 * SΦ + A ^ 2 * SW) :=
        hKle n Φ W A B hA hB hΦsup hWsup
    _ = K n * (CW ^ 2 + CΦ ^ 2) * SΦ * SW := by
        rw [hA2, hB2]; ring

theorem operatorFieldComposition_hn_hn_to_hn_bound (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ), 2 ≤ n →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p c j
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤ (C n * A * B) ^ 2 := by
  classical
  obtain ⟨K, hK, hKle⟩ := operatorFieldComposition_jet_mul (I := I) (M := M) g p r c
  refine ⟨fun n => Real.sqrt (K n), fun n => Real.sqrt_nonneg _, ?_⟩
  intro n hn Φ W A B hA hB hΦ hW
  have hgate : Module.finrank ℝ E / 2 + 1 ≤ n := by rw [hDim]; omega
  have hSΦ_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Real.sqrt (K n) ^ 2 = K n := Real.sq_sqrt (hK n)
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ K n * (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) *
          ∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := hKle n hgate Φ W
    _ ≤ K n * A ^ 2 * B ^ 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hΦ (hK n)) hW
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (mul_nonneg (hK n) (sq_nonneg A))
    _ = (Real.sqrt (K n) * A * B) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
