import DifferentialGeometry.Geometry.Metric.Coordinates.JetDifference
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.ChristoffelDerivative
import DifferentialGeometry.Geometry.Metric.Coordinates.InverseGramPerturbation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    {Cinv M_b P : ℝ}
    (hP_nn : 0 ≤ P) (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hP : ∀ i j l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) g₁ α i j l y| ≤ P)
    (hCinv : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (hCinv_nn : 0 ≤ Cinv)
    (i j k : Fin (Module.finrank ℝ E)) :
    |chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) *
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket, chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  set jet1 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg _ _ _ _
  rw [show (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) * jet1 =
        (1 / 2 : ℝ) * ((Module.finrank ℝ E : ℝ) * ((Cinv * P + 3 * M_b) * jet1)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1/2)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) => (Cinv * P + 3 * M_b) * jet1)
    (fun l _ => ?_)) ?_
  · have hsplit :
        chartInvGramOnE (I := I) g₁ α k l y * chartChristoffelBracket (I := I) g₁ α i j l y -
          chartInvGramOnE (I := I) g₂ α k l y * chartChristoffelBracket (I := I) g₂ α i j l y =
        (chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            chartChristoffelBracket (I := I) g₁ α i j l y +
          chartInvGramOnE (I := I) g₂ α k l y *
            (chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y) := by
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have hbracketDiff :
        |chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y| ≤
          3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y := by
      have h1 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
        g₁ g₂ α y i l j
      have h2 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
        g₁ g₂ α y j l i
      have h3 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
        g₁ g₂ α y l i j
      set d1 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y with hd1
      set d2 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y with hd2
      set d3 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y with hd3
      have hbrk_eq :
          chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y =
            d1 + d2 - d3 := by
        simp only [hd1, hd2, hd3, chartChristoffelBracket]; ring
      have htri : |d1 + d2 - d3| ≤ |d1| + |d2| + |d3| := by
        calc |d1 + d2 - d3| = |d1 + d2 + (-d3)| := by ring_nf
          _ ≤ |d1 + d2| + |(-d3)| := abs_add_le _ _
          _ ≤ (|d1| + |d2|) + |(-d3)| := by gcongr; exact abs_add_le _ _
          _ = |d1| + |d2| + |d3| := by rw [abs_neg]
      rw [hbrk_eq]
      calc |d1 + d2 - d3| ≤ |d1| + |d2| + |d3| := htri
        _ ≤ DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y +
              DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y +
              DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y :=
            add_le_add (add_le_add h1 h2) h3
        _ = 3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y := by ring
    have hsum1 :
        |(chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
            chartChristoffelBracket (I := I) g₁ α i j l y| ≤
          Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) * P := by
      rw [abs_mul]
      refine mul_le_mul (hCinv k l) (hP i j l) (abs_nonneg _)
        (mul_nonneg hCinv_nn (DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_nonneg _ _ _ _))
    have hsum2 :
        |chartInvGramOnE (I := I) g₂ α k l y *
            (chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y)| ≤
          M_b * (3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y) := by
      rw [abs_mul]
      refine mul_le_mul (hMb k l) hbracketDiff (abs_nonneg _) hMb_nn
    refine (add_le_add hsum1 hsum2).trans ?_
    have hgram_le : DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) ≤
        jet1 := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y
    have hpartial_le : 3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y ≤ 3 * jet1 :=
      mul_le_mul_of_nonneg_left (DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum_le_chartMetricJet1DiffSum _ _ _ _) (by norm_num)
    calc Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) * P +
            M_b * (3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y)
        ≤ Cinv * jet1 * P + M_b * (3 * jet1) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_right ?_ hP_nn
            exact mul_le_mul_of_nonneg_left hgram_le hCinv_nn
          · exact mul_le_mul_of_nonneg_left hpartial_le hMb_nn
      _ = (Cinv * P + 3 * M_b) * jet1 := by ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelBracketDeriv_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (y : E)
    (m i j l : Fin (Module.finrank ℝ E)) :
    |chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
        chartChristoffelBracketDeriv (I := I) g₂ α m i j l y| ≤
      3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  have h1 := DifferentialGeometry.Tensor.Coordinates.partialDeriv2_chartGramOnE_sub_abs_le_chartGramPartial2DiffSum (I := I) (M := M)
    g₁ g₂ α y m i l j
  have h2 := DifferentialGeometry.Tensor.Coordinates.partialDeriv2_chartGramOnE_sub_abs_le_chartGramPartial2DiffSum (I := I) (M := M)
    g₁ g₂ α y m j l i
  have h3 := DifferentialGeometry.Tensor.Coordinates.partialDeriv2_chartGramOnE_sub_abs_le_chartGramPartial2DiffSum (I := I) (M := M)
    g₁ g₂ α y m l i j
  set e1 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j)) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j)) y with he1
  set e2 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i)) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i)) y with he2
  set e3 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j)) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j)) y with he3
  have heq : chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
      chartChristoffelBracketDeriv (I := I) g₂ α m i j l y = e1 + e2 - e3 := by
    simp only [he1, he2, he3, chartChristoffelBracketDeriv]; ring
  rw [heq]
  calc |e1 + e2 - e3| = |e1 + e2 + (-e3)| := by ring_nf
    _ ≤ |e1 + e2| + |(-e3)| := abs_add_le _ _
    _ ≤ (|e1| + |e2|) + |(-e3)| := by gcongr; exact abs_add_le _ _
    _ = |e1| + |e2| + |e3| := by rw [abs_neg]
    _ ≤ DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y +
          DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y +
          DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y :=
        add_le_add (add_le_add h1 h2) h3
    _ = 3 * DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartChristoffel_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cd Cinv M_b P D R : ℝ}
    (hCd_nn : 0 ≤ Cd) (hCinv_nn : 0 ≤ Cinv) (hMb_nn : 0 ≤ M_b)
    (hP_nn : 0 ≤ P) (hD_nn : 0 ≤ D) (hR_nn : 0 ≤ R)
    (m i j k : Fin (Module.finrank ℝ E))
    (hCd : ∀ k l, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
        Cd * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y)
    (hMb2 : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hP : ∀ i j l, |chartChristoffelBracket (I := I) g₁ α i j l y| ≤ P)
    (hD : ∀ k l, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤ D)
    (hR : ∀ i j l, |chartChristoffelBracketDeriv (I := I) g₁ α m i j l y| ≤ R)
    (hCinv : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y -
        chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) *
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ α m i j k hy,
    partialDeriv_chartChristoffel_eq (I := I) g₂ α m i j k hy,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  set jet2 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hjet2_nn : 0 ≤ jet2 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg _ _ _ _
  set jet1 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_le : jet1 ≤ jet2 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_le_chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y
  have hjet1_nn : 0 ≤ jet1 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg _ _ _ _
  set gd : ℝ := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_nn : 0 ≤ gd := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_nonneg _ _ _ _
  have hgd_le2 : gd ≤ jet2 :=
    le_trans (DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y) hjet1_le
  rw [show (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2 =
      (1 / 2 : ℝ) * ((Module.finrank ℝ E : ℝ) *
        ((Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1/2)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (g := fun _ : Fin (Module.finrank ℝ E) =>
      (Cd * P + 3 * D + Cinv * R + 3 * M_b) * jet2) (fun l _ => ?_)) ?_
  · have hsplit :
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y *
              chartChristoffelBracket (I := I) g₁ α i j l y +
            chartInvGramOnE (I := I) g₁ α k l y *
              chartChristoffelBracketDeriv (I := I) g₁ α m i j l y) -
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
              chartChristoffelBracket (I := I) g₂ α i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              chartChristoffelBracketDeriv (I := I) g₂ α m i j l y) =
        ((DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
              chartChristoffelBracket (I := I) g₁ α i j l y +
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
              (chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y)) +
          ((chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
              chartChristoffelBracketDeriv (I := I) g₁ α m i j l y +
            chartInvGramOnE (I := I) g₂ α k l y *
              (chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
                chartChristoffelBracketDeriv (I := I) g₂ α m i j l y)) := by ring
    rw [hsplit]
    have hA1 : |(DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y) *
          chartChristoffelBracket (I := I) g₁ α i j l y| ≤ Cd * P * jet2 := by
      rw [abs_mul]
      calc |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| *
            |chartChristoffelBracket (I := I) g₁ α i j l y|
          ≤ (Cd * jet1) * P := mul_le_mul (hCd k l) (hP i j l) (abs_nonneg _)
              (mul_nonneg hCd_nn hjet1_nn)
        _ = Cd * P * jet1 := by ring
        _ ≤ Cd * P * jet2 := mul_le_mul_of_nonneg_left hjet1_le (mul_nonneg hCd_nn hP_nn)
    have hA2 : |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y *
          (chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y)| ≤
          3 * D * jet2 := by
      rw [abs_mul]
      have hbrkdiff : |chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y| ≤
          3 * jet2 := by
        have h1 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
          g₁ g₂ α y i l j
        have h2 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
          g₁ g₂ α y j l i
        have h3 := DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M)
          g₁ g₂ α y l i j
        have hps_le2 : DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y ≤ jet2 :=
          le_trans (DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y) hjet1_le
        set d1 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₁ α l j) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g₂ α l j) y with hd1
        set d2 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₁ α l i) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g₂ α l i) y with hd2
        set d3 : ℝ := DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₁ α i j) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g₂ α i j) y with hd3
        have hbrk_eq : chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y =
            d1 + d2 - d3 := by simp only [hd1, hd2, hd3, chartChristoffelBracket]; ring
        rw [hbrk_eq]
        calc |d1 + d2 - d3| = |d1 + d2 + (-d3)| := by ring_nf
          _ ≤ |d1 + d2| + |(-d3)| := abs_add_le _ _
          _ ≤ (|d1| + |d2|) + |(-d3)| := by gcongr; exact abs_add_le _ _
          _ = |d1| + |d2| + |d3| := by rw [abs_neg]
          _ ≤ jet2 + jet2 + jet2 :=
              add_le_add (add_le_add (h1.trans hps_le2) (h2.trans hps_le2)) (h3.trans hps_le2)
          _ = 3 * jet2 := by ring
      calc |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| *
            |chartChristoffelBracket (I := I) g₁ α i j l y - chartChristoffelBracket (I := I) g₂ α i j l y|
          ≤ D * (3 * jet2) := mul_le_mul (hD k l) hbrkdiff (abs_nonneg _) hD_nn
        _ = 3 * D * jet2 := by ring
    have hB1 : |(chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y) *
          chartChristoffelBracketDeriv (I := I) g₁ α m i j l y| ≤ Cinv * R * jet2 := by
      rw [abs_mul]
      calc |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| *
            |chartChristoffelBracketDeriv (I := I) g₁ α m i j l y|
          ≤ (Cinv * gd) * R := mul_le_mul (hCinv k l) (hR i j l) (abs_nonneg _)
              (mul_nonneg hCinv_nn hgd_nn)
        _ = Cinv * R * gd := by ring
        _ ≤ Cinv * R * jet2 := mul_le_mul_of_nonneg_left hgd_le2 (mul_nonneg hCinv_nn hR_nn)
    have hB2 : |chartInvGramOnE (I := I) g₂ α k l y *
          (chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
            chartChristoffelBracketDeriv (I := I) g₂ α m i j l y)| ≤ 3 * M_b * jet2 := by
      rw [abs_mul]
      have hbdderiv : |chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
          chartChristoffelBracketDeriv (I := I) g₂ α m i j l y| ≤ 3 * jet2 := by
        refine (chartChristoffelBracketDeriv_sub_abs_le (I := I) (M := M) g₁ g₂ α y m i j l).trans ?_
        have hp2_le2 : DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum (I := I) (M := M) g₁ g₂ α y ≤ jet2 :=
          DifferentialGeometry.Tensor.Coordinates.chartGramPartial2DiffSum_le_chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y
        exact mul_le_mul_of_nonneg_left hp2_le2 (by norm_num)
      calc |chartInvGramOnE (I := I) g₂ α k l y| *
            |chartChristoffelBracketDeriv (I := I) g₁ α m i j l y -
              chartChristoffelBracketDeriv (I := I) g₂ α m i j l y|
          ≤ M_b * (3 * jet2) := mul_le_mul (hMb2 k l) hbdderiv (abs_nonneg _) hMb_nn
        _ = 3 * M_b * jet2 := by ring
    refine (abs_add_le _ _).trans ?_
    refine le_trans (add_le_add ((abs_add_le _ _).trans (add_le_add hA1 hA2))
      ((abs_add_le _ _).trans (add_le_add hB1 hB2))) (le_of_eq ?_)
    ring
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

private lemma abs_add_sub_le (A B C : ℝ) :
    |A + B - C| ≤ |A| + |B| + |C| := by
  calc
    |A + B - C| = |A + B + (-C)| := by ring_nf
    _ ≤ |A + B| + |(-C)| := abs_add_le _ _
    _ ≤ (|A| + |B|) + |(-C)| := by gcongr; exact abs_add_le _ _
    _ = |A| + |B| + |C| := by rw [abs_neg]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelBracket_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ m a c, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (chartGramOnE (I := I) g α a c) y| ≤ Q)
    (i j l : Fin (Module.finrank ℝ E)) :
    |chartChristoffelBracket (I := I) g α i j l y| ≤ 3 * Q := by
  unfold chartChristoffelBracket
  exact (abs_add_sub_le _ _ _).trans <| by
    calc
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y| +
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y| +
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y|
          ≤ Q + Q + Q := add_le_add (add_le_add (hQ i l j) (hQ j l i)) (hQ l i j)
      _ = 3 * Q := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E)
    (i j k : Fin (Module.finrank ℝ E)) {M_b Q : ℝ}
    (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hQ : ∀ l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) g α i j l y| ≤ Q) :
    |chartChristoffel (I := I) g α i j k y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * Q := by
  classical
  rw [chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y * chartChristoffelBracket (I := I) g α i j l y| ≤
        ∑ _l : Fin (Module.finrank ℝ E), M_b * Q := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hMb l) (hQ l) (abs_nonneg _) hMb_nn
  calc
    (1 / 2 : ℝ) *
        |∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y * chartChristoffelBracket (I := I) g α i j l y|
        ≤ (1 / 2 : ℝ) * ∑ _l : Fin (Module.finrank ℝ E), M_b * Q :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * Q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelBracketDeriv_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ c m a q, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g α a q)) y| ≤ Q)
    (c i j l : Fin (Module.finrank ℝ E)) :
    |chartChristoffelBracketDeriv (I := I) g α c i j l y| ≤ 3 * Q := by
  unfold chartChristoffelBracketDeriv
  exact (abs_add_sub_le _ _ _).trans <| by
    calc
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y| +
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) y| +
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y|
        ≤ Q + Q + Q := add_le_add
          (add_le_add (hQ c i l j) (hQ c j l i)) (hQ c l i j)
      _ = 3 * Q := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (m i j k : Fin (Module.finrank ℝ E))
    {M_b D P R : ℝ} (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D)
    (hMb : ∀ l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hD : ∀ l : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y| ≤ D)
    (hP : ∀ l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) g α i j l y| ≤ P)
    (hR : ∀ l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracketDeriv (I := I) g α m i j l y| ≤ R) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y| ≤
      (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R) := by
  classical
  rw [partialDeriv_chartChristoffel_eq (I := I) g α m i j k hy, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
              chartChristoffelBracket (I := I) g α i j l y +
            chartInvGramOnE (I := I) g α k l y *
              chartChristoffelBracketDeriv (I := I) g α m i j l y)| ≤
        ∑ _l : Fin (Module.finrank ℝ E), (D * P + M_b * R) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (hD l) (hP l) (abs_nonneg _) hD_nn)
      (mul_le_mul (hMb l) (hR l) (abs_nonneg _) hMb_nn)
  calc
    (1 / 2 : ℝ) *
        |∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
              chartChristoffelBracket (I := I) g α i j l y +
            chartInvGramOnE (I := I) g α k l y *
              chartChristoffelBracketDeriv (I := I) g α m i j l y)|
        ≤ (1 / 2 : ℝ) *
          ∑ _l : Fin (Module.finrank ℝ E), (D * P + M_b * R) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
