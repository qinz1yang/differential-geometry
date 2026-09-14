import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Analysis

def jetRiemannBound (n : ℕ) (C1 C2 K : ℝ) : ℝ :=
  2 * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1) + K * (3 * C2)))
    + (n : ℝ) * (2 * ((n : ℝ) * (K * (3 * C1)) * ((n : ℝ) * (K * (3 * C1)))))

end Analysis

namespace Geometry
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem extChartAt_center_mem_interior (α : M) :
    extChartAt I α α ∈ interior (extChartAt I α).target :=
  extChartAt_target_subset_interior_of_boundaryless (I := I) α
    ((extChartAt I α).map_source (mem_extChartAt_source α))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRiemannCLM_centeredChartBasis_eq_jet
    (g : SmoothRiemannianMetric I M) (α : M)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) (extChartAt I α α))
    (hG1 : ∀ᶠ w in nhds (extChartAt I α α),
      DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w)
      (extChartAt I α α))
    (i j k : Fin (Module.finrank ℝ E)) :
    Connection.chartRiemannCLM (I := I) g α
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α j)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α k)
      = ∑ l : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.jetRiemann
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
            (DifferentialGeometry.Analysis.jet2 (chartGramPi (I := I) g α)
              (extChartAt I α α)) k i j l •
          DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α l := by
  rw [DifferentialGeometry.Geometry.Connection.chartRiemannCLM_apply]
  refine (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis
    (I := I) α).repr.injective ?_
  ext l'
  simp only [map_sum, map_smul, Module.Basis.repr_self_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply]
  simp only [smul_eq_mul, ite_mul, mul_ite, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact chartRiemann_eq_jet (I := I) g α (extChartAt_center_mem_interior (I := I) α)
    hG hG1 hG2 k i j l'

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem curvCovDeriv_zero_eq_metricRm04StandardAt
    (g : SmoothRiemannianMetric I M) (x : M) (X Y Z W : TangentSpace I x) :
    CheegerGromovCompactness.curvCovDeriv (I := I) (M := M) g 0 x
        (vec4 (I := I) X Y Z W) =
      metricRm04StandardAt (I := I) g x X Y Z W := by
  rw [CheegerGromovCompactness.curvZero_apply,
    Connection.riemannOp_eq_chartRiemannCLM_apply,
    metricRm04StandardAt_eq_chartRiemannCLM]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem metricRm04StandardAt_centeredChartBasis_eq_jet
    (g : SmoothRiemannianMetric I M) (α : M)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) (extChartAt I α α))
    (hG1 : ∀ᶠ w in nhds (extChartAt I α α),
      DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w)
      (extChartAt I α α))
    (i j k l : Fin (Module.finrank ℝ E)) :
    metricRm04StandardAt (I := I) g α
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α j)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α k)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α l)
      = ∑ l' : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α α l l' *
            DifferentialGeometry.Analysis.jetRiemann
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
              (DifferentialGeometry.Analysis.jet2 (chartGramPi (I := I) g α)
                (extChartAt I α α)) k i j l' := by
  rw [metricRm04StandardAt_eq_chartRiemannCLM, chartRiemannCLM_centeredChartBasis_eq_jet
    (I := I) g α hG hG1 hG2 i j k]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [smul_eq_mul,
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    ← DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) α l,
    ← DifferentialGeometry.Geometry.Connection.chartBasisVecFiber_self (I := I) α l']
  ring

private theorem abs_fin_sum_le (n : ℕ) {f : Fin n → ℝ} {C : ℝ} (h : ∀ i, |f i| ≤ C) :
    |∑ i, f i| ≤ (n : ℝ) * C := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => h i
    _ = (n : ℝ) * C := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

private theorem abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b - c| ≤ |a + b| + |c| := abs_sub_le_abs_add (a + b) c
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le a b
  linarith

private theorem abs_jetChristoffel_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Fin n → E) {p : Analysis.MatJet E n} {C1 K : ℝ}
    (h1 : ∀ (i l m : Fin n), |p.2.1 (b i) l m| ≤ C1)
    (hK : ∀ k l : Fin n, |(Matrix.of p.1)⁻¹ k l| ≤ K)
    (hK0 : 0 ≤ K) (i j k : Fin n) :
    |Analysis.jetChristoffel b p i j k| ≤ (n : ℝ) * (K * (3 * C1)) := by
  classical
  rw [Analysis.jetChristoffel]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
          (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)| ≤
        (n : ℝ) * (K * (3 * C1)) :=
    abs_fin_sum_le n (fun l => by
      rw [abs_mul]
      refine mul_le_mul (hK k l) ?_ (abs_nonneg _) hK0
      calc
        |p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j|
            ≤ |p.2.1 (b i) l j| + |p.2.1 (b j) l i| + |p.2.1 (b l) i j| :=
              abs_add_sub_le _ _ _
        _ ≤ C1 + C1 + C1 := by linarith [h1 i l j, h1 j l i, h1 l i j]
        _ = 3 * C1 := by ring)
  calc
    (1 / 2) * |∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
        (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)|
        ≤ 1 * |∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
            (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)| :=
          mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
    _ = |∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
            (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)| := one_mul _
    _ ≤ (n : ℝ) * (K * (3 * C1)) := hsum

private theorem abs_jetChristoffelDeriv_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Fin n → E) {p : Analysis.MatJet E n} {C1 C2 K : ℝ}
    (h1 : ∀ (i l m : Fin n), |p.2.1 (b i) l m| ≤ C1)
    (h2 : ∀ (m i l j : Fin n), |p.2.2 (b m) (b i) l j| ≤ C2)
    (hK : ∀ k l : Fin n, |(Matrix.of p.1)⁻¹ k l| ≤ K)
    (hC1 : 0 ≤ C1) (hK0 : 0 ≤ K) (m i j k : Fin n) :
    |Analysis.jetChristoffelDeriv b p m i j k| ≤
      (n : ℝ) *
        ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
          + K * (3 * C2)) := by
  classical
  have htri1 : ∀ l : Fin n, |p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j| ≤ 3 * C1 := by
    intro l
    refine le_trans (abs_add_sub_le _ _ _) ?_
    have := h1 i l j
    have := h1 j l i
    have := h1 l i j
    linarith
  have htri2 : ∀ l : Fin n, |p.2.2 (b m) (b i) l j + p.2.2 (b m) (b j) l i
      - p.2.2 (b m) (b l) i j| ≤ 3 * C2 := by
    intro l
    refine le_trans (abs_add_sub_le _ _ _) ?_
    have := h2 m i l j
    have := h2 m j l i
    have := h2 m l i j
    linarith
  have hfirst : ∀ l : Fin n,
      |∑ a : Fin n, ∑ c : Fin n,
        (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * p.2.1 (b m) a c| ≤
          (n : ℝ) *
            ((n : ℝ) * (K * (K * C1))) := fun l =>
    abs_fin_sum_le n (fun a =>
      abs_fin_sum_le n (fun c => by
        rw [abs_mul, abs_mul]
        refine le_trans (mul_le_mul (mul_le_mul (hK k a) (hK c l) (abs_nonneg _) hK0)
          (h1 m a c) (abs_nonneg _) (mul_nonneg hK0 hK0)) ?_
        exact le_of_eq (by ring)))
  rw [Analysis.jetChristoffelDeriv, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum : |∑ l : Fin n,
      ((-∑ a : Fin n, ∑ c : Fin n,
          (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * p.2.1 (b m) a c) *
          (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)
        + (Matrix.of p.1)⁻¹ k l *
          (p.2.2 (b m) (b i) l j + p.2.2 (b m) (b j) l i - p.2.2 (b m) (b l) i j))| ≤
      (n : ℝ) *
        ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
          + K * (3 * C2)) :=
    abs_fin_sum_le n (fun l => by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg]
        refine le_trans (mul_le_mul (hfirst l) (htri1 l) (abs_nonneg _) ?_)
          (le_of_eq (by ring))
        exact mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hK0 (mul_nonneg hK0 hC1)))
      · rw [abs_mul]
        exact mul_le_mul (hK k l) (htri2 l) (abs_nonneg _) hK0)
  calc
    (1 / 2) * |∑ l : Fin n,
        ((-∑ a : Fin n, ∑ c : Fin n,
            (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * p.2.1 (b m) a c) *
            (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)
          + (Matrix.of p.1)⁻¹ k l *
            (p.2.2 (b m) (b i) l j + p.2.2 (b m) (b j) l i - p.2.2 (b m) (b l) i j))|
        ≤ 1 * |∑ l : Fin n,
            ((-∑ a : Fin n, ∑ c : Fin n,
                (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * p.2.1 (b m) a c) *
                (p.2.1 (b i) l j + p.2.1 (b j) l i - p.2.1 (b l) i j)
              + (Matrix.of p.1)⁻¹ k l *
                (p.2.2 (b m) (b i) l j + p.2.2 (b m) (b j) l i - p.2.2 (b m) (b l) i j))| :=
          mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
    _ = _ := one_mul _
    _ ≤ (n : ℝ) *
        ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
          + K * (3 * C2)) := hsum

private theorem abs_jetRiemann_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Fin n → E) {p : Analysis.MatJet E n} {C1 C2 K : ℝ}
    (h1 : ∀ (i l m : Fin n), |p.2.1 (b i) l m| ≤ C1)
    (h2 : ∀ (m i l j : Fin n), |p.2.2 (b m) (b i) l j| ≤ C2)
    (hK : ∀ k l : Fin n, |(Matrix.of p.1)⁻¹ k l| ≤ K)
    (hC1 : 0 ≤ C1) (hK0 : 0 ≤ K) (i j k l : Fin n) :
    |Analysis.jetRiemann b p i j k l| ≤
      2 * ((n : ℝ) *
        ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
          + K * (3 * C2)))
      + (n : ℝ) *
          (2 * ((n : ℝ) * (K * (3 * C1)) *
            ((n : ℝ) * (K * (3 * C1))))) := by
  classical
  have hC3 : (0 : ℝ) ≤ 3 * C1 := by linarith
  have hΓ : ∀ a c e : Fin n,
      |Analysis.jetChristoffel b p a c e| ≤ (n : ℝ) * (K * (3 * C1)) :=
    fun a c e => abs_jetChristoffel_le b h1 hK hK0 a c e
  have hD : ∀ a c e f : Fin n,
      |Analysis.jetChristoffelDeriv b p a c e f| ≤
        (n : ℝ) *
          ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
            + K * (3 * C2)) :=
    fun a c e f => abs_jetChristoffelDeriv_le b h1 h2 hK hC1 hK0 a c e f
  have hGnn : (0 : ℝ) ≤ (n : ℝ) * (K * (3 * C1)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hK0 hC3)
  have hS : |∑ m : Fin n,
        (Analysis.jetChristoffel b p j m l * Analysis.jetChristoffel b p i k m
          - Analysis.jetChristoffel b p k m l * Analysis.jetChristoffel b p i j m)| ≤
      (n : ℝ) *
        (2 * ((n : ℝ) * (K * (3 * C1)) *
          ((n : ℝ) * (K * (3 * C1))))) :=
    abs_fin_sum_le n (fun m => by
      have hx : |Analysis.jetChristoffel b p j m l * Analysis.jetChristoffel b p i k m| ≤
          ((n : ℝ) * (K * (3 * C1))) *
            ((n : ℝ) * (K * (3 * C1))) := by
        rw [abs_mul]
        exact mul_le_mul (hΓ j m l) (hΓ i k m) (abs_nonneg _) hGnn
      have hy : |Analysis.jetChristoffel b p k m l * Analysis.jetChristoffel b p i j m| ≤
          ((n : ℝ) * (K * (3 * C1))) *
            ((n : ℝ) * (K * (3 * C1))) := by
        rw [abs_mul]
        exact mul_le_mul (hΓ k m l) (hΓ i j m) (abs_nonneg _) hGnn
      linarith [abs_sub_le_abs_add
        (Analysis.jetChristoffel b p j m l * Analysis.jetChristoffel b p i k m)
        (Analysis.jetChristoffel b p k m l * Analysis.jetChristoffel b p i j m)])
  rw [Analysis.jetRiemann]
  calc
    |Analysis.jetChristoffelDeriv b p j i k l - Analysis.jetChristoffelDeriv b p k i j l
        + ∑ m : Fin n, (Analysis.jetChristoffel b p j m l * Analysis.jetChristoffel b p i k m
          - Analysis.jetChristoffel b p k m l * Analysis.jetChristoffel b p i j m)|
        ≤ |Analysis.jetChristoffelDeriv b p j i k l - Analysis.jetChristoffelDeriv b p k i j l|
          + |∑ m : Fin n, (Analysis.jetChristoffel b p j m l * Analysis.jetChristoffel b p i k m
            - Analysis.jetChristoffel b p k m l * Analysis.jetChristoffel b p i j m)| :=
          abs_add_le _ _
    _ ≤ (|Analysis.jetChristoffelDeriv b p j i k l|
          + |Analysis.jetChristoffelDeriv b p k i j l|)
          + (n : ℝ) *
            (2 * ((n : ℝ) * (K * (3 * C1)) *
              ((n : ℝ) * (K * (3 * C1))))) :=
          add_le_add (abs_sub_le_abs_add _ _) hS
    _ ≤ ((n : ℝ) *
          ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
            + K * (3 * C2))
        + (n : ℝ) *
          ((n : ℝ) * ((n : ℝ) * (K * (K * C1))) * (3 * C1)
            + K * (3 * C2)))
        + (n : ℝ) *
          (2 * ((n : ℝ) * (K * (3 * C1)) *
            ((n : ℝ) * (K * (3 * C1))))) :=
          add_le_add (add_le_add (hD j i k l) (hD k i j l)) le_rfl
    _ = _ := by ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem abs_metricRm04StandardAt_centeredChartBasis_le_of_jet_bounds
    (g : SmoothRiemannianMetric I M) (α : M)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) (extChartAt I α α))
    (hG1 : ∀ᶠ w in nhds (extChartAt I α α),
      DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w)
      (extChartAt I α α))
    {C0 C1 C2 K : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hK0 : 0 ≤ K)
    (h0 : ∀ l m : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α α l m| ≤ C0)
    (h1 : ∀ (i l m : Fin (Module.finrank ℝ E)),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l m)
        (extChartAt I α α)| ≤ C1)
    (h2 : ∀ (m i l j : Fin (Module.finrank ℝ E)),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l j))
        (extChartAt I α α)| ≤ C2)
    (hK : ∀ k l : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Geometry.Operator.chartInvGramOnE (I := I) g α k l
        (extChartAt I α α)| ≤ K)
    (i j k l : Fin (Module.finrank ℝ E)) :
    |metricRm04StandardAt (I := I) g α
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α j)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α k)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α l)| ≤
      (Module.finrank ℝ E : ℝ) *
        (C0 * Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K) := by
  classical
  have hJ : ∀ l' : Fin (Module.finrank ℝ E),
      |Analysis.jetRiemann (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
        (Analysis.jet2 (chartGramPi (I := I) g α) (extChartAt I α α)) k i j l'| ≤
        Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K := by
    intro l'
    exact abs_jetRiemann_le (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
      (fun i' l' m' => by
        rw [jet2_chartGram_d1 (I := I) g α hG i' l' m']; exact h1 i' l' m')
      (fun m' i' l' j' => by
        rw [jet2_chartGram_d2 (I := I) g α hG1 hG2 m' i' l' j']; exact h2 m' i' l' j')
      (fun k' l' => by
        rw [jet2_chartGram_invGram (I := I) g α (extChartAt I α α) k' l']; exact hK k' l')
      hC1 hK0 k i j l'
  rw [metricRm04StandardAt_centeredChartBasis_eq_jet (I := I) g α hG hG1 hG2 i j k l]
  calc
    |∑ l' : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α α l l' *
          Analysis.jetRiemann (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
            (Analysis.jet2 (chartGramPi (I := I) g α) (extChartAt I α α)) k i j l'|
        ≤ ∑ l' : Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α α l l' *
              Analysis.jetRiemann (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
                (Analysis.jet2 (chartGramPi (I := I) g α) (extChartAt I α α)) k i j l'| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l' : Fin (Module.finrank ℝ E),
          C0 * Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K :=
          Finset.sum_le_sum (fun l' _ => by
            rw [abs_mul]
            exact mul_le_mul (h0 l l') (hJ l') (abs_nonneg _) hC0)
    _ = (Module.finrank ℝ E : ℝ) *
          (C0 * Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [I.Boundaryless] in
private theorem coordInner0S_four_le_of_component_bounds
    {Idx : Type*} [Fintype Idx] {x : M}
    {A : Tensor0SBundle.Tensor0SSpace 4 I x}
    (basis : Module.Basis Idx ℝ (TangentSpace I x)) (gInv : Idx → Idx → ℝ)
    {K M : ℝ} (hK0 : 0 ≤ K) (hM0 : 0 ≤ M)
    (hK : ∀ i j : Idx, |gInv i j| ≤ K)
    (hA : ∀ I0 : Fin 4 → Idx, |A (fun a => basis (I0 a))| ≤ M) :
    Tensor0SBundle.coordInner0S (I := I) (x := x) 4 gInv A A basis ≤
      (Fintype.card Idx : ℝ) ^ 4 * ((Fintype.card Idx : ℝ) ^ 4 * (K ^ 4 * M ^ 2)) := by
  classical
  have hprod : ∀ I0 J0 : Fin 4 → Idx,
      |∏ a : Fin 4, gInv (I0 a) (J0 a)| ≤ K ^ 4 := by
    intro I0 J0
    rw [Finset.abs_prod]
    calc
      ∏ a : Fin 4, |gInv (I0 a) (J0 a)| ≤ ∏ _a : Fin 4, K :=
        Finset.prod_le_prod (fun a _ => abs_nonneg _) (fun a _ => hK _ _)
      _ = K ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ I0 J0 : Fin 4 → Idx,
      (∏ a : Fin 4, gInv (I0 a) (J0 a)) * A (fun a => basis (I0 a)) *
          A (fun a => basis (J0 a)) ≤ K ^ 4 * M ^ 2 := by
    intro I0 J0
    refine le_trans (le_abs_self _) (le_trans (le_of_eq (by rw [abs_mul, abs_mul])) ?_)
    refine le_trans (mul_le_mul
      (mul_le_mul (hprod I0 J0) (hA I0) (abs_nonneg _) (pow_nonneg hK0 4))
      (hA J0) (abs_nonneg _) (by positivity)) ?_
    exact le_of_eq (by ring)
  calc
    Tensor0SBundle.coordInner0S (I := I) (x := x) 4 gInv A A basis
        = ∑ I0 : Fin 4 → Idx, ∑ J0 : Fin 4 → Idx,
            (∏ a : Fin 4, gInv (I0 a) (J0 a)) * A (fun a => basis (I0 a)) *
              A (fun a => basis (J0 a)) := by
          simp only [Tensor0SBundle.coordInner0S, Tensor0SBundle.tensor0SComponent_apply]
    _ ≤ ∑ _I0 : Fin 4 → Idx, ∑ _J0 : Fin 4 → Idx, (K ^ 4 * M ^ 2) :=
          Finset.sum_le_sum (fun I0 _ => Finset.sum_le_sum (fun J0 _ => hterm I0 J0))
    _ = (Fintype.card Idx : ℝ) ^ 4 *
          ((Fintype.card Idx : ℝ) ^ 4 * (K ^ 4 * M ^ 2)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
            Fintype.card_fin, Nat.cast_pow]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem curvDerivNorm_zero_le_of_centralChart_component_bounds
    (g : SmoothRiemannianMetric I M) (α : M) {K M : ℝ} (hK0 : 0 ≤ K) (hM0 : 0 ≤ M)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g α
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α)
      (fun i j => DifferentialGeometry.Geometry.Operator.chartInvGramOnE (I := I) g α i j
        (extChartAt I α α)))
    (hK : ∀ i j : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Geometry.Operator.chartInvGramOnE (I := I) g α i j
        (extChartAt I α α)| ≤ K)
    (hcomp : ∀ i j k l : Fin (Module.finrank ℝ E),
      |metricRm04StandardAt (I := I) g α
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α j)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α k)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α l)| ≤ M) :
    CheegerGromovCompactness.curvDerivNorm (I := I) 0 g α ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4 *
        ((Module.finrank ℝ E : ℝ) ^ 4 * (K ^ 4 * M ^ 2))) := by
  classical
  rw [CheegerGromovCompactness.curvDerivNorm,
    CheegerGromovCompactness.curvDerivNormSq,
    Tensor0SBundle.normSq0S_eq_coord (I := I) g α 4
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α) _ hinv]
  refine Real.sqrt_le_sqrt ?_
  refine le_trans (coordInner0S_four_le_of_component_bounds (I := I)
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α) _
    hK0 hM0 hK (fun I0 => ?_)) (le_of_eq (by simp only [Fintype.card_fin]))
  have hvec : (fun a : Fin 4 =>
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α (I0 a)) =
      vec4
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α (I0 0))
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α (I0 1))
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α (I0 2))
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α (I0 3)) := by
    funext a
    fin_cases a <;> simp [vec4] <;> rfl
  rw [hvec, curvCovDeriv_zero_eq_metricRm04StandardAt]
  exact hcomp _ _ _ _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem abs_metricRm04StandardAt_centeredChartBasis_le_of_jetBounds
    (g : SmoothRiemannianMetric I M) (α : M)
    {C0 C1 C2 K : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hK0 : 0 ≤ K)
    (h0 : ∀ l m : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α α l m| ≤ C0)
    (h1 : ∀ (i l m : Fin (Module.finrank ℝ E)),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l m)
        (extChartAt I α α)| ≤ C1)
    (h2 : ∀ (m i l j : Fin (Module.finrank ℝ E)),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) g α l j))
        (extChartAt I α α)| ≤ C2)
    (hK : ∀ k l : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Geometry.Operator.chartInvGramOnE (I := I) g α k l
        (extChartAt I α α)| ≤ K)
    (i j k l : Fin (Module.finrank ℝ E)) :
    |metricRm04StandardAt (I := I) g α
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α j)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α k)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) α l)| ≤
      (Module.finrank ℝ E : ℝ) *
        (C0 * Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K) := by
  have hmem : extChartAt I α α ∈ interior (extChartAt I α).target :=
    extChartAt_center_mem_interior (I := I) α
  have hcdAt : ∀ w : E, w ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (chartGramPi (I := I) g α) w := by
    intro w hw
    have htw : (extChartAt I α).target ∈ 𝓝 w :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hw) interior_subset
    exact contDiffAt_pi.2 (fun l => contDiffAt_pi.2 (fun m =>
      (DifferentialGeometry.Geometry.Operator.chartGramOnE_contDiffOn (I := I) g α l m).contDiffAt
        htw))
  refine abs_metricRm04StandardAt_centeredChartBasis_le_of_jet_bounds (I := I) g α
    ?_ ?_ ?_ hC0 hC1 hK0 h0 h1 h2 hK i j k l
  · exact (hcdAt _ hmem).differentiableAt (by simp)
  · exact Filter.eventually_of_mem (isOpen_interior.mem_nhds hmem)
      (fun w hw => (hcdAt w hw).differentiableAt (by simp))
  · exact (((hcdAt _ hmem).of_le (by decide : (2 : ℕ∞) ≤ ∞)).fderiv_right
      (m := 1) (n := 2) (by decide)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem curvDerivNorm_zero_eq_zero_of_finrank_le_one
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank ℝ E ≤ 1) (x : M) :
    CheegerGromovCompactness.curvDerivNorm (I := I) 0 g x = 0 := by
  have hzero : metricRm04At (I := I) g x = 0 :=
    metricRm04At_eq_zero_of_finrank_le_one g hE x
  rw [CheegerGromovCompactness.curvDerivNorm,
    CheegerGromovCompactness.curvDerivNormSq]
  have hcomp : CheegerGromovCompactness.curvCovDeriv (I := I) (M := M) g 0 x = 0 := by
    rw [show CheegerGromovCompactness.curvCovDeriv (I := I) (M := M) g 0 =
        metricRm04 (I := I) (M := M) g from rfl,
      metricRm04_apply, hzero]
  rw [hcomp, (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) g x (0 + 4) 0).mpr rfl,
    Real.sqrt_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem curvDerivNorm_zero_le_chartJetBound_of_finrank_le_one
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank ℝ E ≤ 1) (x : M)
    (C0 C1 C2 K : ℝ) :
    CheegerGromovCompactness.curvDerivNorm (I := I) 0 g x ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4 *
        ((Module.finrank ℝ E : ℝ) ^ 4 *
          (K ^ 4 * ((Module.finrank ℝ E : ℝ) *
            (C0 * Analysis.jetRiemannBound (Module.finrank ℝ E) C1 C2 K)) ^ 2))) := by
  rw [curvDerivNorm_zero_eq_zero_of_finrank_le_one (I := I) g hE x]
  exact Real.sqrt_nonneg _

end Curvature
end Geometry
end DifferentialGeometry
