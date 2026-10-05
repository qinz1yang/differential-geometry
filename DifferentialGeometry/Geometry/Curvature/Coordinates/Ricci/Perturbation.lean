import DifferentialGeometry.Geometry.Curvature.Coordinates.Ricci.Decomposition
import DifferentialGeometry.Geometry.Metric.Coordinates.JetDifference

namespace DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by ring_nf
    _ ≤ |a| + |(-b)| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderTerm_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Cdiff : ℝ}
    (hCdiff : ∀ m i j k : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
        Cdiff * DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y)
    (i k : Fin (Module.finrank ℝ E)) :
    |chartRicciSecondOrderTerm (I := I) g₁ α i k y -
        chartRicciSecondOrderTerm (I := I) g₂ α i k y| ≤
      2 * (Module.finrank ℝ E : ℝ) * Cdiff *
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartRicciSecondOrderTerm, chartRicciSecondOrderTerm, ← Finset.sum_sub_distrib]
  set jet2 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hjet2_nn : 0 ≤ jet2 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg _ _ _ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) => 2 * Cdiff * jet2) (fun j _ => ?_)) ?_
  · have hjk :
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y) -
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y -
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y) =
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y) := by ring
    rw [hjk]
    refine (abs_sub_le_abs_add_abs _ _).trans ?_
    have h1 := hCdiff j i k j
    have h2 := hCdiff k i j j
    calc |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y| +
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y|
        ≤ Cdiff * jet2 + Cdiff * jet2 := add_le_add h1 h2
      _ = 2 * Cdiff * jet2 := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show 2 * (Module.finrank ℝ E : ℝ) * Cdiff * jet2 =
          (Module.finrank ℝ E : ℝ) * (2 * Cdiff * jet2) by ring]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciFirstOrderTerm_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Clip Mg : ℝ} (hClip_nn : 0 ≤ Clip) (hMg_nn : 0 ≤ Mg)
    (hClip : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y -
          chartChristoffel (I := I) g₂ α i j k y| ≤
        Clip * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y)
    (hMg1 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y| ≤ Mg)
    (hMg2 : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₂ α i j k y| ≤ Mg)
    (i k : Fin (Module.finrank ℝ E)) :
    |chartRicciFirstOrderTerm (I := I) g₁ α i k y -
        chartRicciFirstOrderTerm (I := I) g₂ α i k y| ≤
      4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg *
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartRicciFirstOrderTerm, chartRicciFirstOrderTerm, ← Finset.sum_sub_distrib]
  set jet1 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg _ _ _ _
  have hprod : ∀ a₁ a₂ a₃ a₄ a₅ a₆ : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α a₁ a₂ a₃ y *
            chartChristoffel (I := I) g₁ α a₄ a₅ a₆ y -
          chartChristoffel (I := I) g₂ α a₁ a₂ a₃ y *
            chartChristoffel (I := I) g₂ α a₄ a₅ a₆ y| ≤
        2 * Clip * Mg * jet1 := by
    intro a₁ a₂ a₃ a₄ a₅ a₆
    set A₁ := chartChristoffel (I := I) g₁ α a₁ a₂ a₃ y
    set A₂ := chartChristoffel (I := I) g₂ α a₁ a₂ a₃ y
    set B₁ := chartChristoffel (I := I) g₁ α a₄ a₅ a₆ y
    set B₂ := chartChristoffel (I := I) g₂ α a₄ a₅ a₆ y
    have hsplit : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have hA : |A₁ - A₂| ≤ Clip * jet1 := hClip a₁ a₂ a₃
    have hB : |B₁ - B₂| ≤ Clip * jet1 := hClip a₄ a₅ a₆
    have hB₁ : |B₁| ≤ Mg := hMg1 a₄ a₅ a₆
    have hA₂ : |A₂| ≤ Mg := hMg2 a₁ a₂ a₃
    calc |(A₁ - A₂) * B₁| + |A₂ * (B₁ - B₂)|
        = |A₁ - A₂| * |B₁| + |A₂| * |B₁ - B₂| := by rw [abs_mul, abs_mul]
      _ ≤ (Clip * jet1) * Mg + Mg * (Clip * jet1) :=
          add_le_add (mul_le_mul hA hB₁ (abs_nonneg _) (mul_nonneg hClip_nn hjet1_nn))
            (mul_le_mul hA₂ hB (abs_nonneg _) hMg_nn)
      _ = 2 * Clip * Mg * jet1 := by ring
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      |∑ m : Fin (Module.finrank ℝ E),
          ((chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y) -
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y))| ≤
        (Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1) := by
    intro j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum
      (g := fun _ : Fin (Module.finrank ℝ E) => 4 * Clip * Mg * jet1) (fun m _ => ?_)) ?_
    · have hrearr :
          (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y) -
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y) =
          (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y) -
            (chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y) := by ring
      rw [hrearr]
      refine (abs_sub_le_abs_add_abs _ _).trans ?_
      have h1 := hprod j m j i k m
      have h2 := hprod k m j i j m
      calc |chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y| +
            |chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y|
          ≤ 2 * Clip * Mg * jet1 + 2 * Clip * Mg * jet1 := add_le_add h1 h2
        _ = 4 * Clip * Mg * jet1 := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) =>
      (Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1)) (fun j _ => ?_)) ?_
  · have hreorg : ∀ j : Fin (Module.finrank ℝ E),
        ((∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₁ α j m j y *
                chartChristoffel (I := I) g₁ α i k m y -
              chartChristoffel (I := I) g₁ α k m j y *
                chartChristoffel (I := I) g₁ α i j m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₂ α j m j y *
                chartChristoffel (I := I) g₂ α i k m y -
              chartChristoffel (I := I) g₂ α k m j y *
                chartChristoffel (I := I) g₂ α i j m y))) =
          ∑ m : Fin (Module.finrank ℝ E),
            ((chartChristoffel (I := I) g₁ α j m j y *
                  chartChristoffel (I := I) g₁ α i k m y -
                chartChristoffel (I := I) g₁ α k m j y *
                  chartChristoffel (I := I) g₁ α i j m y) -
              (chartChristoffel (I := I) g₂ α j m j y *
                  chartChristoffel (I := I) g₂ α i k m y -
                chartChristoffel (I := I) g₂ α k m j y *
                  chartChristoffel (I := I) g₂ α i j m y)) := by
      intro j
      exact (Finset.sum_sub_distrib
        (f := fun m : Fin (Module.finrank ℝ E) =>
          chartChristoffel (I := I) g₁ α j m j y *
              chartChristoffel (I := I) g₁ α i k m y -
            chartChristoffel (I := I) g₁ α k m j y *
              chartChristoffel (I := I) g₁ α i j m y)
        (g := fun m : Fin (Module.finrank ℝ E) =>
          chartChristoffel (I := I) g₂ α j m j y *
              chartChristoffel (I := I) g₂ α i k m y -
            chartChristoffel (I := I) g₂ α k m j y *
              chartChristoffel (I := I) g₂ α i j m y)).symm
    rw [hreorg j]
    exact hinner j
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show 4 * (Module.finrank ℝ E : ℝ) ^ 2 * Clip * Mg * jet1 =
          (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) * (4 * Clip * Mg * jet1)) by ring]

end

section

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry.Geometry.Operator

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicci_abs_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E)
    {CΓ CdΓ : ℝ} (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b c y| ≤ CΓ)
    (hdΓ : ∀ m a b c : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g α a b c) y| ≤ CdΓ) :
    |chartRicciTensor (I := I) g α i k y| ≤
      (Module.finrank ℝ E : ℝ) *
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
  classical
  have hprod : ∀ a b c d e f : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α a b c y *
          chartChristoffel (I := I) g α d e f y| ≤ CΓ ^ 2 := by
    intro a b c d e f
    rw [abs_mul]
    calc
      |chartChristoffel (I := I) g α a b c y| *
          |chartChristoffel (I := I) g α d e f y|
          ≤ CΓ * CΓ := mul_le_mul (hΓ a b c) (hΓ d e f) (abs_nonneg _) hCΓ
      _ = CΓ ^ 2 := by ring
  have hRiem : ∀ j l : Fin (Module.finrank ℝ E),
      |chartRiemannTensor (I := I) g α i j k l y| ≤
        2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
    intro j l
    rw [chartRiemannTensor_def]
    have hderiv :
        |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y| ≤
          2 * CdΓ := by
      rw [sub_eq_add_neg]
      calc
        |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y +
            -DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y|
            ≤ |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                  (chartChristoffel (I := I) g α i k l) y| +
                |-DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k
                  (chartChristoffel (I := I) g α i j l) y| := abs_add_le _ _
        _ = |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                  (chartChristoffel (I := I) g α i k l) y| +
                |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k
                  (chartChristoffel (I := I) g α i j l) y| := by rw [abs_neg]
        _ ≤ CdΓ + CdΓ := add_le_add (hdΓ j i k l) (hdΓ k i j l)
        _ = 2 * CdΓ := by ring
    have hquad :
        |∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)| ≤
          2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
      calc
        |∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)|
            ≤ ∑ m : Fin (Module.finrank ℝ E),
                |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y -
                  chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m : Fin (Module.finrank ℝ E), (2 * CΓ ^ 2) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [sub_eq_add_neg]
          calc
            |chartChristoffel (I := I) g α j m l y *
                  chartChristoffel (I := I) g α i k m y +
                -(chartChristoffel (I := I) g α k m l y *
                  chartChristoffel (I := I) g α i j m y)|
                ≤ |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y| +
                  |-(chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y)| := abs_add_le _ _
            _ = |chartChristoffel (I := I) g α j m l y *
                    chartChristoffel (I := I) g α i k m y| +
                  |chartChristoffel (I := I) g α k m l y *
                    chartChristoffel (I := I) g α i j m y| := by rw [abs_neg]
            _ ≤ CΓ ^ 2 + CΓ ^ 2 := add_le_add
                  (hprod j m l i k m) (hprod k m l i j m)
            _ = 2 * CΓ ^ 2 := by ring
        _ = 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    calc
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m l y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m l y *
                chartChristoffel (I := I) g α i j m y)|
          ≤ |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                (chartChristoffel (I := I) g α i k l) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k
                (chartChristoffel (I := I) g α i j l) y| +
            |∑ m : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) g α j m l y *
                  chartChristoffel (I := I) g α i k m y -
                chartChristoffel (I := I) g α k m l y *
                  chartChristoffel (I := I) g α i j m y)| := abs_add_le _ _
      _ ≤ 2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2 :=
        add_le_add hderiv hquad
  rw [chartRicciTensor_def]
  calc
    |∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α i j k j y|
        ≤ ∑ j : Fin (Module.finrank ℝ E),
          |chartRiemannTensor (I := I) g α i j k j y| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (Module.finrank ℝ E),
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
          exact Finset.sum_le_sum fun j _ => hRiem j j
    _ = (Module.finrank ℝ E : ℝ) *
        (2 * CdΓ + 2 * (Module.finrank ℝ E : ℝ) * CΓ ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]

end

end DifferentialGeometry.Geometry.Curvature
