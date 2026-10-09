import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Tensor.Coordinates.PartialDerivative
import DifferentialGeometry.Analysis.Normed.Matrix.Entrywise

noncomputable section

open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Geometry.Operator (chartGramOnE)

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartGramDiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M) : ℝ :=
  Matrix.entrywiseL1 (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x - DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x)

lemma chartGramDiffSum_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M) :
    0 ≤ chartGramDiffSum (I := I) (M := M) g₁ g₂ α x :=
  Matrix.entrywiseL1_nonneg _

lemma chartGramMatrix_sub_entry_abs_le_chartGramDiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x p q - DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x p q| ≤
      chartGramDiffSum (I := I) (M := M) g₁ g₂ α x := by
  have h := Matrix.abs_entry_le_entrywiseL1
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x - DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x) p q
  rwa [Matrix.sub_apply] at h

section

attribute [local instance] Fintype.ofFinite Classical.propDecidable

def chartGramPartialAbsDiffEntry (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) ×
      (Fin (Module.finrank ℝ E))) : ℝ :=
  |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.1 p.2.2) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.1 p.2.2) y|

def chartGramPartialDiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p, chartGramPartialAbsDiffEntry (I := I) (M := M) g₁ g₂ α y p

lemma chartGramPartialDiffSum_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (a l b : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g₁ α l b) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g₂ α l b) y| ≤
      chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h := Finset.single_le_sum
    (f := chartGramPartialAbsDiffEntry (I := I) (M := M) g₁ g₂ α y)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (l, a, b))
  exact h

def chartGramPartial2AbsDiffEntry (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) ×
      (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) : ℝ :=
  |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.2.2.1 p.2.2.2)) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.2.2.1 p.2.2.2)) y|

def chartGramPartial2DiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p, chartGramPartial2AbsDiffEntry (I := I) (M := M) g₁ g₂ α y p

lemma chartGramPartial2DiffSum_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma partialDeriv2_chartGramOnE_sub_abs_le_chartGramPartial2DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (c a l b : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g₁ α l b)) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g₂ α l b)) y| ≤
      chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h := Finset.single_le_sum
    (f := chartGramPartial2AbsDiffEntry (I := I) (M := M) g₁ g₂ α y)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (c, a, l, b))
  exact h

def chartMetricJet1DiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y)
    + chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y

def chartMetricJet2DiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y
    + chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y

lemma chartMetricJet1DiffSum_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartGramDiffSum_nonneg _ _ _ _)
    (chartGramPartialDiffSum_nonneg _ _ _ _)

lemma chartMetricJet2DiffSum_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (chartMetricJet1DiffSum_nonneg _ _ _ _)
    (chartGramPartial2DiffSum_nonneg _ _ _ _)

lemma chartGramDiffSum_le_chartMetricJet1DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) ≤
      chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (chartGramPartialDiffSum_nonneg _ _ _ _)

lemma chartGramPartialDiffSum_le_chartMetricJet1DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartGramDiffSum_nonneg _ _ _ _)

lemma chartMetricJet1DiffSum_le_chartMetricJet2DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (chartGramPartial2DiffSum_nonneg _ _ _ _)

lemma chartGramPartial2DiffSum_le_chartMetricJet2DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (chartMetricJet1DiffSum_nonneg _ _ _ _)

end

section

variable [NeZero (Module.finrank ℝ E)]

local notation "D3Idx" =>
  Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E)

def chartGramPartial3DiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  ∑ p : D3Idx,
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₁ α p.2.2.2.1 p.2.2.2.2))) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.2.2.1
            (chartGramOnE (I := I) g₂ α p.2.2.2.1 p.2.2.2.2))) y|

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv3_chartGramOnE_sub_abs_le_chartGramPartial3DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (d c m a b : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b))) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b))) y| ≤
      chartGramPartial3DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  let p : D3Idx := (d, (c, (m, (a, b))))
  have h := Finset.single_le_sum
    (f := fun q : D3Idx =>
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.1
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₁ α q.2.2.2.1 q.2.2.2.2))) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.1
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.1
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q.2.2.1
              (chartGramOnE (I := I) g₂ α q.2.2.2.1 q.2.2.2.2))) y|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  simpa only [chartGramPartial3DiffSum, p] using h

omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramPartial3DiffSum_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartGramPartial3DiffSum (I := I) (M := M) g₁ g₂ α y := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

def chartMetricJet3DiffSum (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y +
    chartGramPartial3DiffSum (I := I) (M := M) g₁ g₂ α y

omit [NeZero (Module.finrank ℝ E)] in
theorem chartMetricJet3DiffSum_nonneg
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartMetricJet3DiffSum (I := I) (M := M) g₁ g₂ α y :=
  add_nonneg (DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg _ _ _ _)
    (chartGramPartial3DiffSum_nonneg (I := I) (M := M) g₁ g₂ α y)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartMetricJet2DiffSum_le_chartMetricJet3DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet3DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_right (chartGramPartial3DiffSum_nonneg (I := I) (M := M) g₁ g₂ α y)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramPartial3DiffSum_le_chartMetricJet3DiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E) :
    chartGramPartial3DiffSum (I := I) (M := M) g₁ g₂ α y ≤
      chartMetricJet3DiffSum (I := I) (M := M) g₁ g₂ α y :=
  le_add_of_nonneg_left (DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg _ _ _ _)

end

end DifferentialGeometry.Tensor.Coordinates
