import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.H1H2Composition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Grid.Regularity

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

private lemma triGrid4_le
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    {i : ℕ} (hi : i < 4) :
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
      ∑ n ∈ Finset.range 4, a n *
        ∑ l ∈ Finset.range (4 - n), b l := by
  have hi4 : i + 1 ≤ 4 := by omega
  calc
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
        ∑ n ∈ Finset.range (i + 1), a n *
          ∑ l ∈ Finset.range (4 - n), b l := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (ha n)
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega))
      intro l _ _
      exact hb l
    _ ≤ ∑ n ∈ Finset.range 4, a n *
          ∑ l ∈ Finset.range (4 - n), b l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi4)
      intro n _ _
      exact mul_nonneg (ha n) (Finset.sum_nonneg fun l _ => hb l)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem operatorFieldComposition_h3_sup_uniform_bound
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
          (A B : ℝ), 0 ≤ A → 0 ≤ B →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g r c x
              (Φ.toSection x) ≤ A ^ 2) →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g p r x
              (W.toSection x) ≤ B ^ 2) →
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g p c j
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
            C * (B ^ 2 * ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 +
              A ^ 2 * ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := by
  classical
  let D : ℝ := ∑ i ∈ Finset.range 4, operatorFieldApplicationGdiag (E := E) i
  let Cg : ℝ := gridRSClassC (E := E) (I := I) (M := M) gBase Λ 3
  let C : ℝ := D * Cg
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact Finset.sum_nonneg (fun i _ => operatorFieldApplicationGdiag_nonneg (E := E) i)
  have hCg : 0 ≤ Cg := by
    simpa only [Cg] using
      gridRSClassC_nonneg (E := E) (I := I) (M := M) gBase Λ 3
  have hC : 0 ≤ C := mul_nonneg hD hCg
  refine ⟨C, hC, ?_⟩
  intro g hEq Φ W A B hA hB hΦpt hWpt
  let grid : M → ℝ := fun x =>
    ∑ n ∈ Finset.range 4,
      riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
          ((iteratedCovGrad (I := I) g r c n Φ).toSection x) *
        ∑ l ∈ Finset.range (4 - n),
          riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x)
  obtain ⟨hgridInt, hgridBd⟩ :=
    (grid_rs_bound (I := I) (M := M) g r p c r 3).2
      Φ W A B hA hB hΦpt hWpt
  have hgridInt' : Integrable grid
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [grid] using hgridInt
  let SΦ : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2
  let SW : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2
  have hinner : 0 ≤ B ^ 2 * SΦ + A ^ 2 * SW := by
    exact add_nonneg
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hgridBd' :
      (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        Cg * (B ^ 2 * SΦ + A ^ 2 * SW) := by
    calc
      _ ≤ gridRsConst (I := I) (M := M) g 3 *
          (B ^ 2 * SΦ + A ^ 2 * SW) := by
        simpa only [grid, SΦ, SW] using hgridBd
      _ ≤ Cg * (B ^ 2 * SΦ + A ^ 2 * SW) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Cg] using
            grid_rs_const_le (I := I) (M := M) gBase g hEq 3)
          hinner
  have hterm : ∀ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g p c i
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro i hi
    have hpoint : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g p (c + i) x
            ((iteratedCovGrad (I := I) g p c i
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)).toSection x) ≤
          operatorFieldApplicationGdiag (E := E) i * grid x := by
      intro x
      refine (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g i p r c Φ W x).trans ?_
      apply mul_le_mul_of_nonneg_left _ (operatorFieldApplicationGdiag_nonneg (E := E) i)
      simpa only [grid] using
        (triGrid4_le
          (fun n => riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
            ((iteratedCovGrad (I := I) g r c n Φ).toSection x))
          (fun l => riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x))
          (fun n => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g r (c + n) x _)
          (fun l => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g p (r + l) x _)
          (Finset.mem_range.mp hi))
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + i)
      (iteratedCovGrad (I := I) g p c i
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W))
      (fun x => operatorFieldApplicationGdiag (E := E) i * grid x)
      (hgridInt'.const_mul (operatorFieldApplicationGdiag (E := E) i)) hpoint
    calc
      _ ≤ ∫ x, operatorFieldApplicationGdiag (E := E) i * grid x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hkey
      _ = operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g p c i
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
        ∑ i ∈ Finset.range 4, operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      Finset.sum_le_sum hterm
    _ = D * ∫ x, grid x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [D]
      rw [Finset.sum_mul]
    _ ≤ D * (Cg * (B ^ 2 * SΦ + A ^ 2 * SW)) :=
      mul_le_mul_of_nonneg_left hgridBd' hD
    _ = C * (B ^ 2 * SΦ + A ^ 2 * SW) := by
      dsimp only [C]
      ring
    _ = C * (B ^ 2 * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 +
        A ^ 2 * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
