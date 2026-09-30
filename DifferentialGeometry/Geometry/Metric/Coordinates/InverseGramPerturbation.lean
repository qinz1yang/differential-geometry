import DifferentialGeometry.Geometry.Metric.Coordinates.JetDifference
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Analysis.Normed.Matrix.Entrywise
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartInverseGramDerivative
import Mathlib.Tactic.Ring

noncomputable section

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartInvGramMatrix_entry_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {M_b D : ℝ}
    (hM1 : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b)
    (hM2 : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b)
    (hD : ∀ p q,
      |DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x p q - DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x p q| ≤ D)
    (k l : Fin (Module.finrank ℝ E)) :
    |chartInvGramMatrix (I := I) g₁ α x k l -
        chartInvGramMatrix (I := I) g₂ α x k l| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * D := by
  classical
  have hA_unit : IsUnit (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g₁ α hx))
  have hB_unit : IsUnit (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g₂ α hx))
  have hD' : ∀ p q,
      |(DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x - DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x) p q| ≤ D := by
    intro p q
    rw [Matrix.sub_apply, abs_sub_comm]
    exact hD p q
  have hinvA : ∀ p q, |(DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x)⁻¹ p q| ≤ M_b := by
    intro p q
    have := hM1 p q
    unfold chartInvGramMatrix at this
    exact this
  have hinvB : ∀ p q, |(DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x)⁻¹ p q| ≤ M_b := by
    intro p q
    have := hM2 p q
    unfold chartInvGramMatrix at this
    exact this
  have h := Matrix.inv_entry_sub_abs_le_of_entry_bound
    (A := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₁ α x) (B := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g₂ α x)
    hA_unit hB_unit hinvA hinvB hD' k l
  unfold chartInvGramMatrix
  exact h

theorem chartInvGramMatrix_entry_sub_abs_le_chartGramDiffSum
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {M_b : ℝ}
    (hM1 : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b)
    (hM2 : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b)
    (k l : Fin (Module.finrank ℝ E)) :
    |chartInvGramMatrix (I := I) g₁ α x k l -
        chartInvGramMatrix (I := I) g₂ α x k l| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 *
        DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α x :=
  chartInvGramMatrix_entry_sub_abs_le (I := I) (M := M) g₁ g₂ α hx hM1 hM2
    (fun p q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_sub_entry_abs_le_chartGramDiffSum (I := I) (M := M)
      g₁ g₂ α x p q) k l

section

variable [NeZero (Module.finrank ℝ E)]

attribute [local instance] Fintype.ofFinite Classical.propDecidable

private lemma abs_triple_prod_sub_le (A₁ A₂ B₁ B₂ C₁ C₂ : ℝ) :
    |A₁ * B₁ * C₁ - A₂ * B₂ * C₂| ≤
      |A₁ - A₂| * |B₁| * |C₁| + |A₂| * |B₁ - B₂| * |C₁| +
        |A₂| * |B₂| * |C₁ - C₂| := by
  have hsplit : A₁ * B₁ * C₁ - A₂ * B₂ * C₂ =
      (A₁ - A₂) * B₁ * C₁ + A₂ * (B₁ - B₂) * C₁ + A₂ * B₂ * (C₁ - C₂) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans ?_) (le_of_eq ?_)
  · refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
    · rw [abs_mul, abs_mul]
    · rw [abs_mul, abs_mul]
  · rw [abs_mul, abs_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_chartInvGramOnE_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {Cinv M_b Q : ℝ}
    (hMb_nn : 0 ≤ M_b) (hQ_nn : 0 ≤ Q) (hCinv_nn : 0 ≤ Cinv)
    (hMb1 : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y| ≤ M_b)
    (hMb2 : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b)
    (hQ : ∀ m a b, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤ Q)
    (hCinv : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y -
        chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y))
    (m k l : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) *
        DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g₁ α y m k l hy,
    partialDeriv_chartInvGramOnE_eq (I := I) g₂ α y m k l hy]
  rw [neg_sub_neg, abs_sub_comm, ← Finset.sum_sub_distrib]
  set jet1 : ℝ := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y with hjet1_def
  have hjet1_nn : 0 ≤ jet1 := DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg _ _ _ _
  set gd : ℝ := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) with hgd
  have hgd_le : gd ≤ jet1 := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y
  have hgd_nn : 0 ≤ gd := DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum_nonneg _ _ _ _
  have hterm : ∀ a : Fin (Module.finrank ℝ E),
      |(∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₁ α k a y *
            chartInvGramOnE (I := I) g₁ α b l y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y) -
        (∑ b : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g₂ α k a y *
            chartInvGramOnE (I := I) g₂ α b l y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y)| ≤
        (Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
      (2 * Cinv * M_b * Q + M_b ^ 2) * jet1) (fun b _ => ?_)) ?_
    · have htp := abs_triple_prod_sub_le
        (chartInvGramOnE (I := I) g₁ α k a y) (chartInvGramOnE (I := I) g₂ α k a y)
        (chartInvGramOnE (I := I) g₁ α b l y) (chartInvGramOnE (I := I) g₂ α b l y)
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y)
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y)
      refine htp.trans ?_
      have hC_ka : |chartInvGramOnE (I := I) g₁ α k a y -
          chartInvGramOnE (I := I) g₂ α k a y| ≤ Cinv * gd := hCinv k a
      have hC_bl : |chartInvGramOnE (I := I) g₁ α b l y -
          chartInvGramOnE (I := I) g₂ α b l y| ≤ Cinv * gd := hCinv b l
      have hP_ab : |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤
          DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y :=
        DifferentialGeometry.Tensor.Coordinates.partialDeriv_chartGramOnE_sub_abs_le_chartGramPartialDiffSum (I := I) (M := M) g₁ g₂ α y m a b
      have hP_ab' : |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤ jet1 :=
        hP_ab.trans (DifferentialGeometry.Tensor.Coordinates.chartGramPartialDiffSum_le_chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y)
      have ht1 : |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₁ α b l y| *
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤
          Cinv * M_b * Q * jet1 := by
        calc |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₁ α b l y| *
                |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y|
            ≤ (Cinv * gd) * M_b * Q := by
              refine mul_le_mul (mul_le_mul hC_ka (hMb1 b l) (abs_nonneg _)
                (mul_nonneg hCinv_nn hgd_nn)) (hQ m a b) (abs_nonneg _) ?_
              exact mul_nonneg (mul_nonneg hCinv_nn hgd_nn) hMb_nn
          _ = Cinv * M_b * Q * gd := by ring
          _ ≤ Cinv * M_b * Q * jet1 :=
              mul_le_mul_of_nonneg_left hgd_le
                (mul_nonneg (mul_nonneg hCinv_nn hMb_nn) hQ_nn)
      have ht2 : |chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| ≤
          Cinv * M_b * Q * jet1 := by
        calc |chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
                |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y|
            ≤ M_b * (Cinv * gd) * Q := by
              refine mul_le_mul (mul_le_mul (hMb2 k a) hC_bl (abs_nonneg _) hMb_nn)
                (hQ m a b) (abs_nonneg _) ?_
              exact mul_nonneg hMb_nn (mul_nonneg hCinv_nn hgd_nn)
          _ = Cinv * M_b * Q * gd := by ring
          _ ≤ Cinv * M_b * Q * jet1 :=
              mul_le_mul_of_nonneg_left hgd_le
                (mul_nonneg (mul_nonneg hCinv_nn hMb_nn) hQ_nn)
      have ht3 : |chartInvGramOnE (I := I) g₂ α k a y| *
            |chartInvGramOnE (I := I) g₂ α b l y| *
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y| ≤
          M_b ^ 2 * jet1 := by
        calc |chartInvGramOnE (I := I) g₂ α k a y| *
                |chartInvGramOnE (I := I) g₂ α b l y| *
                |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y|
            ≤ M_b * M_b * jet1 := by
              refine mul_le_mul (mul_le_mul (hMb2 k a) (hMb2 b l) (abs_nonneg _) hMb_nn)
                hP_ab' (abs_nonneg _) (mul_nonneg hMb_nn hMb_nn)
          _ = M_b ^ 2 * jet1 := by ring
      calc |chartInvGramOnE (I := I) g₁ α k a y - chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₁ α b l y| *
              |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| +
            |chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₁ α b l y - chartInvGramOnE (I := I) g₂ α b l y| *
              |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y| +
            |chartInvGramOnE (I := I) g₂ α k a y| *
              |chartInvGramOnE (I := I) g₂ α b l y| *
              |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b) y -
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b) y|
          ≤ Cinv * M_b * Q * jet1 + Cinv * M_b * Q * jet1 + M_b ^ 2 * jet1 :=
            add_le_add (add_le_add ht1 ht2) ht3
        _ = (2 * Cinv * M_b * Q + M_b ^ 2) * jet1 := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin (Module.finrank ℝ E) =>
    (Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1)) (fun a _ => hterm a)) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) * jet1 =
        (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * ((2 * Cinv * M_b * Q + M_b ^ 2) * jet1)) by ring]

omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    {M_b Q : ℝ} (hMb_nn : 0 ≤ M_b)
    (hMb : ∀ a c, |chartInvGramOnE (I := I) g α a c y| ≤ M_b)
    (hQ : ∀ m a c, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (chartGramOnE (I := I) g α a c) y| ≤ Q)
    (m p q : Fin (Module.finrank ℝ E)) :
    |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α p q) y| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q := by
  classical
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y m p q hy, abs_neg]
  calc
    |∑ a : Fin (Module.finrank ℝ E),
        ∑ c : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α p a y *
            chartInvGramOnE (I := I) g α c q y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y|
        ≤ ∑ a : Fin (Module.finrank ℝ E),
            |∑ c : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α p a y *
                chartInvGramOnE (I := I) g α c q y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin (Module.finrank ℝ E),
          ∑ _c : Fin (Module.finrank ℝ E), M_b * M_b * Q := by
        refine Finset.sum_le_sum fun a _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun c _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hMb p a) (hMb c q) (abs_nonneg _) hMb_nn)
          (hQ m a c) (abs_nonneg _) (mul_nonneg hMb_nn hMb_nn)
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
