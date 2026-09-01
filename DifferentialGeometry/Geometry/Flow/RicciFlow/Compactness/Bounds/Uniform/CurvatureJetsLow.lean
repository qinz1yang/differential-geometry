import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureSupremum

import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedCurvatureOperatorBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnectionDifferenceQuadraticBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gBase_le_scaled (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) (v : TangentSpace I x) :
    gBase.inner x v v ≤ Λ * g₀.inner x v v := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hz := mul_le_mul_of_nonneg_left (hcomp x v).1 hΛ0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz

theorem uniformRicSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v : TangentSpace I x),
        g₀.inner x (ricEndoRaisedFib (I := I) g₀ x v)
            (ricEndoRaisedFib (I := I) g₀ x v) ≤
          C ^ 2 * g₀.inner x v v := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  have hB0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hΛ1) (by linarith)
  obtain ⟨C, hC0, hC⟩ :=
    exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope (I := I) (M := M)
      gBase (δ₀ := Λ - 1) (by linarith : Λ - 1 < 1)
      ((Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ) hB0
  refine ⟨Λ * C, mul_nonneg hΛ0.le hC0, ?_⟩
  intro x v
  have hbase := hC g₀ (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) (δ := Λ - 1)
    (le_of_eq (max_eq_left hΛ1).symm)
    (metricDifference_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp)
    (fun y a b => metricDifference_tie (I := I) (M := M) gBase g₀ y a b) x
    (metricDifference_jetEnvelope (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x) v
  set R : TangentSpace I x := ricEndoRaisedFib (I := I) g₀ x v with hR
  have hout : g₀.inner x R R ≤ Λ * gBase.inner x R R := (hcomp x R).2
  have hin : gBase.inner x v v ≤ Λ * g₀.inner x v v :=
    gBase_le_scaled (I := I) (M := M) gBase g₀ hΛ hcomp x v
  calc g₀.inner x R R
      ≤ Λ * gBase.inner x R R := hout
    _ ≤ Λ * (C ^ 2 * gBase.inner x v v) := mul_le_mul_of_nonneg_left hbase hΛ0.le
    _ ≤ Λ * (C ^ 2 * (Λ * g₀.inner x v v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (sq_nonneg C)) hΛ0.le
    _ = (Λ * C) ^ 2 * g₀.inner x v v := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
noncomputable def connectionDifferenceZeroC (Λ : ℝ) : ℝ :=
  3 / 2 * Λ ^ 3 * Λ

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifferenceSup_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)) ≤
        connectionDifferenceZeroC Λ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  intro x v w
  have h := connectionDifference_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
  unfold DifferentialGeometry.PDE.DeTurck.connectionDifference
    DifferentialGeometry.Geometry.Connection.LeviCivita
  simpa [connectionDifferenceZeroC, mul_assoc, mul_left_comm, mul_comm] using h

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem uniformConnectionDifferenceSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x),
        Real.sqrt (gBase.inner x
            (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)
            (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)) ≤
          C * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by
  refine ⟨connectionDifferenceZeroC Λ, ?_, ?_⟩
  · dsimp [connectionDifferenceZeroC]
    positivity
  · exact connectionDifferenceSup_le (I := I) (M := M) gBase g₀ hΛ hcomp hjet1

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
noncomputable def connectionDifferenceOneC (Λ : ℝ) : ℝ :=
  3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2)

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covConnectionDifference_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (covDerivConnectionDifference (I := I) gBase g₀
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnectionDifference (I := I) gBase g₀
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)) ≤
        connectionDifferenceOneC Λ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) * Real.sqrt (gBase.inner x u u) := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  intro x v w u
  simpa [connectionDifferenceOneC] using
    covDerivConnectionDifference_gJet_le (I := I) hEq hjet1 hjet2
      (Set.mem_univ x) v w u

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem uniformCovConnectionDifferenceSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        Real.sqrt (gBase.inner x
            (covDerivConnectionDifference (I := I) gBase g₀
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w)
                (smoothExtensionTangent (I := I) x u) x)
            (covDerivConnectionDifference (I := I) gBase g₀
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w)
                (smoothExtensionTangent (I := I) x u) x)) ≤
          C * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) *
            Real.sqrt (gBase.inner x u u) := by
  refine ⟨connectionDifferenceOneC Λ, ?_, ?_⟩
  · dsimp [connectionDifferenceOneC]
    positivity
  · exact covConnectionDifference_le (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2


noncomputable def ricciZeroC (Λ Kb : ℝ) : ℝ :=
  (Module.finrank ℝ E : ℝ) *
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb))


omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciBilin_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      |ricciTensor (I := I) g₀ x v w| ≤
        ricciZeroC (E := E) Λ Kb * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
  classical
  let F : ℝ := Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb)
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  have hF0 : 0 ≤ F :=
    mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  have hF := uniformCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  intro x v w
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x
  have hB : ∀ i j : Fin (Module.finrank ℝ E),
      g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) g₀ x v w B hB]
  calc
    |∑ i, g₀.inner x
        (riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w) (B i)|
        ≤ ∑ i, |g₀.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w) (B i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
        F * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      set R : TangentSpace I x :=
        riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w with hR
      have hBii : g₀.inner x (B i) (B i) = 1 := by
        rw [hB i i]
        simp
      have hRR : g₀.inner x R R ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w := by
        have h := hF x (B i) v w
        rw [← hR, hBii] at h
        simpa only [mul_one] using h
      have hv0 : 0 ≤ g₀.inner x v v :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x v
      have hw0 : 0 ≤ g₀.inner x w w :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x w
      have hsqrt : Real.sqrt (g₀.inner x R R) ≤
          F * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by
        have heq : F ^ 2 * g₀.inner x v v * g₀.inner x w w =
            (F * Real.sqrt (g₀.inner x v v) *
              Real.sqrt (g₀.inner x w w)) ^ 2 := by
          calc
            F ^ 2 * g₀.inner x v v * g₀.inner x w w =
                F ^ 2 * Real.sqrt (g₀.inner x v v) ^ 2 *
                  Real.sqrt (g₀.inner x w w) ^ 2 := by
              rw [Real.sq_sqrt hv0, Real.sq_sqrt hw0]
            _ = (F * Real.sqrt (g₀.inner x v v) *
                Real.sqrt (g₀.inner x w w)) ^ 2 := by ring
        rw [heq] at hRR
        have h := Real.sqrt_le_sqrt hRR
        rwa [Real.sqrt_sq
          (mul_nonneg (mul_nonneg hF0 (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))] at h
      change |g₀.inner x R (B i)| ≤ _
      calc
        |g₀.inner x R (B i)| ≤
            Real.sqrt (g₀.inner x R R) *
              Real.sqrt (g₀.inner x (B i) (B i)) :=
          abs_metric_inner_le_sqrt_metric_quadratic
            (I := I) (M := M) g₀ x R (B i)
        _ = Real.sqrt (g₀.inner x R R) := by
          rw [hBii]
          simp
        _ ≤ _ := hsqrt
    _ = ricciZeroC (E := E) Λ Kb *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [ricciZeroC, F]
      ring


theorem uniformRicBilin
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x),
        |ricciTensor (I := I) g₀ x v w| ≤
          C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  refine ⟨ricciZeroC (E := E) Λ Kb, ?_, ?_⟩
  · dsimp [ricciZeroC]
    exact mul_nonneg (Nat.cast_nonneg _) <|
      mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  · exact ricciBilin_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2

end RicciFlow
end PDE
end DifferentialGeometry

end
