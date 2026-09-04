import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Algebra.CovariantSumCross

import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem iterCov_one_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    iterCov (I := I) g₁ r T 1 =
      iterCov (I := I) g₂ r T 1 + diffStep (I := I) g₁ g₂ r T := by
  rw [iterCov_telescoping (I := I) g₁ g₂ r T 1]
  congr 1
  change telescAccum (I := I) g₁ g₂ r T 1 = diffStep (I := I) g₁ g₂ r T
  simp only [telescAccum]
  rw [covStep_zero, zero_add]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem metric_self_norm
    (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) =
      (Module.finrank ℝ E : ℝ) := by
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro a b
    simpa [identityInvMetric, diagonalInvMetric] using h' a b
  have hcard := normSq0S_metricTensor0S_eq_card (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinv
  rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at hcard
  rw [show metricTensorField (I := I) g x = metricTensor0S (I := I) g x from by
    apply Tensor0SBundle.tensor0SSpace_ext (I := I) 2 x
    intro v
    rw [metricTensorField_apply, metricTensor0S_apply]]
  simpa only [Fintype.card_fin] using hcard

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem sqrt_normSq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s
      (0 : Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  rw [show (∑ slots : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]
    simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem metric_self_sum
    (g : SmoothRiemannianMetric I M) (x : M) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        Real.sqrt (normSq0S (I := I) g x (2 + k)
          (iterCov (I := I) g 2 (metricTensorField (I := I) g) k x)) =
      Real.sqrt (Module.finrank ℝ E : ℝ) := by
  classical
  rw [Finset.sum_eq_single 0]
  · change Real.sqrt
        (normSq0S (I := I) g x 2 (metricTensorField (I := I) g x)) =
      Real.sqrt (Module.finrank ℝ E : ℝ)
    rw [metric_self_norm (I := I) g x]
  · intro k hk hk0
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [iterCov_metric_zero (I := I) g a]
    exact sqrt_normSq_zero (I := I) g x _
  · simp

noncomputable def revJetOneC (Λ : ℝ) : ℝ :=
  2 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) *
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) *
    (Real.sqrt (Λ ^ 2) * Real.sqrt (Module.finrank ℝ E : ℝ))

noncomputable def revJetTwoC (Λ : ℝ) : ℝ :=
  let L₁ := max (revJetOneC (E := E) Λ) Λ
  let D := Dtower (Module.finrank ℝ E)
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁)) 2
    (fun m => if m = 1 then
      (2 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (2 + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ + Λ * L₁ ^ 2) +
          (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁))
    else 0) 2
  max 0 (Real.sqrt (Λ ^ 4) *
    (D * Real.sqrt (Module.finrank ℝ E : ℝ)))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
theorem reverseJetOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ) :
    MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀
      (revJetOneC (E := E) Λ) := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hEq.1
  intro x _
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₀ x
  have hinv : MetricInverseInBasisGen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 1 basis hinv]
  have htel := iterCov_one_eq (I := I) gBase g₀ 2
    (metricTensorField (I := I) gBase)
  have hself := iterCov_metric_zero (I := I) gBase 0
  rw [hself] at htel
  have hfield :
      iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 1 =
        -diffStep (I := I) gBase g₀ 2
          (metricTensorField (I := I) gBase) :=
    eq_neg_of_add_eq_zero_left htel.symm
  have hneg :
      iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 1 x =
        -(diffStep (I := I) gBase g₀ 2 (metricTensorField (I := I) gBase) x) := by
    exact congrArg (fun S => S x) hfield
  rw [hneg, Tensor0SBundle.normSq0S_neg]
  have hstep := diffStep_jet_one_le (I := I) gBase g₀ 2
    (metricTensorField (I := I) gBase) hEq hjet1 (Set.mem_univ x)
  have hmetric := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 2
    (metricTensorField (I := I) gBase x)
  rw [metric_self_norm (I := I) gBase x] at hmetric
  refine hstep.trans ?_
  dsimp [revJetOneC]
  exact mul_le_mul_of_nonneg_left hmetric (by positivity)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem reverseJetTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀
      (revJetTwoC (E := E) Λ) := by
  let C₁ : ℝ := revJetOneC (E := E) Λ
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  let L₁ : ℝ := max C₁ Λ
  have hrev1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ L₁ :=
    fun x hx => (hrev1 x hx).trans (le_max_left _ _)
  have hfwd1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase L₁ :=
    fun x hx => (hjet1 x hx).trans (le_max_right _ _)
  let D : ℝ :=
    Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁)) 2
      (fun m => if m = 1 then
        (2 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (2 + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ + Λ * L₁ ^ 2) +
            (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁))
        else 0) 2
  intro x _
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₀ x
  have hinv : MetricInverseInBasisGen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 2 basis hinv]
  have hcomp := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 4
    (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 2 x)
  have htwo := iterCovG1_two (I := I) g₀ gBase 2
    (metricTensorField (I := I) gBase) x
    (metricUniformEquivalentOn_symm (I := I) hEq)
    hrev1' hfwd1' hjet2 (Set.mem_univ x)
  rw [metric_self_sum (I := I) gBase x 2] at htwo
  have htwo' :
      Real.sqrt (normSq0S (I := I) gBase x 4
        (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 2 x)) ≤
        D * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    simpa [D, L₁] using htwo
  refine hcomp.trans ((mul_le_mul_of_nonneg_left htwo'
    (Real.sqrt_nonneg _)).trans ?_)
  exact le_max_right _ _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem reverseJetPack
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    let L₁ := max (revJetOneC (E := E) Λ) Λ
    let L₂ := revJetTwoC (E := E) Λ
    0 ≤ L₁ ∧ 0 ≤ L₂ ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase L₁ ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ L₁ ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ L₂ := by
  dsimp only
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  have hrev2 := reverseJetTwo (I := I) gBase g₀ hEq hjet1 hjet2
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL₁ : 0 ≤ max (revJetOneC (E := E) Λ) Λ :=
    hΛ0.trans (le_max_right _ _)
  have hL₂ : 0 ≤ revJetTwoC (E := E) Λ := by
    dsimp [revJetTwoC]
    exact le_max_left _ _
  refine ⟨hL₁, hL₂, ?_, ?_, hrev2⟩
  · intro x hx
    exact (hjet1 x hx).trans (le_max_right _ _)
  · intro x hx
    exact (hrev1 x hx).trans (le_max_left _ _)

end RicciFlow
end PDE
end DifferentialGeometry
