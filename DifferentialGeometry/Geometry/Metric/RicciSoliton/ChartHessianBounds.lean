import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Mathlib.Analysis.Normed.Module.FiniteDimension


noncomputable section

open Set
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace DifferentialGeometry.Geometry

open Curvature Operator Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem gradientRicciSoliton_chartIteratedPartialDeriv
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (hsol : gradientRicciSoliton g f σ) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (i j : Fin (Module.finrank ℝ E)) :
    chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) =
      (σ / 2) * g.inner x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) -
        ricciTensor g x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) +
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel g α i j k (extChartAt I α x) *
            partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have h := hsol x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
  rw [hessFun_eq_abstract g f.contMDiff x,
    chartAlphaMatrixIdentity_holds g α f.contMDiff hx i j,
    chartHessianTensor_def] at h
  linarith

theorem gradientRicciSoliton_abs_chartIteratedPartialDeriv_le
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (hsol : gradientRicciSoliton g f σ) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (G Q C L : ℝ≥0)
    (hG : ∀ i j : Fin (Module.finrank ℝ E),
      |g.inner x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)| ≤ G)
    (hQ : ∀ i j : Fin (Module.finrank ℝ E),
      |ricciTensor g x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)| ≤ Q)
    (hC : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel g α i j k (extChartAt I α x)| ≤ C)
    (hL : ∀ k : Fin (Module.finrank ℝ E),
      |partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| ≤ L)
    (i j : Fin (Module.finrank ℝ E)) :
    |chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x)| ≤
      |σ / 2| * G + Q + (Module.finrank ℝ E : ℝ) * C * L := by
  rw [gradientRicciSoliton_chartIteratedPartialDeriv hsol α hx i j]
  have hsum : |∑ k : Fin (Module.finrank ℝ E),
      chartChristoffel g α i j k (extChartAt I α x) *
        partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| ≤
      (Module.finrank ℝ E : ℝ) * C * L := by
    calc
      _ ≤ ∑ k : Fin (Module.finrank ℝ E),
          |chartChristoffel g α i j k (extChartAt I α x) *
            partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (Module.finrank ℝ E), (C : ℝ) * L := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (hC i j k) (hL k) (abs_nonneg _) C.coe_nonneg
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  calc
    _ ≤ |(σ / 2) * g.inner x (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x) -
          ricciTensor g x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)| +
        |∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel g α i j k (extChartAt I α x) *
            partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| := abs_add_le _ _
    _ ≤ (|σ / 2| * G + Q) + (Module.finrank ℝ E : ℝ) * C * L := by
      apply add_le_add _ hsum
      exact (abs_sub _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG i j) (abs_nonneg _))
        (hQ i j))
    _ = _ := rfl

theorem gradientRicciSoliton_norm_fderiv_fderiv_scalarOnE_le
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (hsol : gradientRicciSoliton g f σ) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (G Q C L : ℝ≥0)
    (hG : ∀ i j : Fin (Module.finrank ℝ E),
      |g.inner x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)| ≤ G)
    (hQ : ∀ i j : Fin (Module.finrank ℝ E),
      |ricciTensor g x (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)| ≤ Q)
    (hC : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel g α i j k (extChartAt I α x)| ≤ C)
    (hL : ∀ k : Fin (Module.finrank ℝ E),
      |partialDeriv k (scalarOnE (I := I) α f) (extChartAt I α x)| ≤ L) :
    ‖fderiv ℝ (fderiv ℝ (scalarOnE (I := I) α f)) (extChartAt I α x)‖ ≤
      (|σ / 2| * G + Q + (Module.finrank ℝ E : ℝ) * C * L) *
        ((Module.finrank ℝ E : ℝ) *
          ‖(chartModelBasis E).equivFunL.toContinuousLinearMap‖) ^ 2 := by
  classical
  let B := chartModelBasis E
  let y := extChartAt I α x
  let D₂ := fderiv ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y
  let T : ℝ := |σ / 2| * G + Q + (Module.finrank ℝ E : ℝ) * C * L
  let K : ℝ := (Module.finrank ℝ E : ℝ) * ‖B.equivFunL.toContinuousLinearMap‖
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hy : y ∈ (extChartAt I α).target := by
    exact (extChartAt I α).map_source (by simpa only [extChartAt_source] using hx)
  have hcd : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) y :=
    (scalarOnE_contDiffOn α f.contMDiff).contDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hfd : DifferentiableAt ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y :=
    (hcd.fderiv_right (m := 1) (by decide)).differentiableAt_one
  have heval (i j : Fin (Module.finrank ℝ E)) :
      D₂ (B i) (B j) = chartIteratedPartialDeriv (I := I) α f i j y := by
    let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (B j)
    have hcomp : partialDeriv j (scalarOnE (I := I) α f) =
        ev ∘ fderiv ℝ (scalarOnE (I := I) α f) := rfl
    change D₂ (B i) (B j) = fderiv ℝ (partialDeriv j (scalarOnE (I := I) α f)) y (B i)
    rw [hcomp, fderiv_comp y ev.differentiableAt hfd, ev.fderiv]
    rfl
  have hcomponent (i j : Fin (Module.finrank ℝ E)) : ‖D₂ (B i) (B j)‖ ≤ T := by
    rw [Real.norm_eq_abs, heval i j]
    exact gradientRicciSoliton_abs_chartIteratedPartialDeriv_le hsol α hx G Q C L
      hG hQ hC hL i j
  have hinner (i : Fin (Module.finrank ℝ E)) : ‖D₂ (B i)‖ ≤ K * T := by
    simpa only [K, Fintype.card_fin, nsmul_eq_mul] using
      B.opNorm_le (u := D₂ (B i)) hT (hcomponent i)
  have htotal : ‖D₂‖ ≤ K * (K * T) := by
    simpa only [K, Fintype.card_fin, nsmul_eq_mul] using
      B.opNorm_le (u := D₂) (mul_nonneg hK hT) hinner
  change ‖D₂‖ ≤ T * K ^ 2
  nlinarith [htotal]

end DifferentialGeometry.Geometry
