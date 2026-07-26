import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Core
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold

/-!
# Public smooth-field split of the zeroth-order DeTurck correction

The canonical fibre construction of `lieCorr0Field` has four algebraically
different pieces.  This file packages those fibres as smooth coefficient
fields and exports the exact decomposition needed by low-regularity estimates.
In the base-background split the insert piece is kept together with the
DeTurck endomorphism arm, where its leading derivative cancels.
-/

noncomputable section

-- Match `Tensor/RSTensor/Defs.lean`: the bundle instances (and the model-fibre
-- `NormedSpace (TensorRSModel …)` needed by the `Cₛ^∞⟮…⟯` section stack) were
-- elaborated under reduced def-eq transparency, so downstream section
-- constructions require the same option to synthesize the FiberBundle/VectorBundle
-- stack. Elaboration-config only; no statement or proof changes.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Smooth field associated with the two insertion terms in
`lieCorr0TotalFib`. -/
def lc0Insert (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorr0InsertFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Smooth field associated with the vector--bilinear term in
`lieCorr0TotalFib`. -/
def lc0VB (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorr0VBFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Smooth field associated with the mixed connection-difference term in
`lieCorr0TotalFib`. -/
def lc0AMix (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorr0AMixFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Smooth field associated with the fixed-curvature term in
`lieCorr0TotalFib`. -/
def lc0Riem (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorr0RiemFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- At the frozen base background, the insertion endomorphism is exactly the
negative of the DeTurck `W` endomorphism. -/
theorem nEndo_base (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorr0NEndo (I := I) g₀ g₁ g₀ x =
      -deTurckLieWEndo (I := I) g₁ g₀ x := by
  rw [lieCorr0NEndo, sub_self, zero_sub]

/-- After the base cancellation, the insertion endomorphism is a product of
the moving-to-frozen connection difference with the difference of the two
DeTurck vector fields.  In particular its first covariant derivative uses at
most the metric jet through order three. -/
theorem nEndo_diff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    lieCorr0NEndo (I := I) g₀ g₁ g_bg x -
        lieCorr0NEndo (I := I) g₀ g₁ g₀ x =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            ∀ b : M, TangentSpace I b) x) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            ∀ b : M, TangentSpace I b) x) := by
  rw [nEndo_base (I := I) (M := M) g₀ g₁ x, lieCorr0NEndo]
  abel

/-- The insertion part cancels the base-background DeTurck endomorphism arm.
Writing the result as a background difference prevents the highest derivative
of the metric perturbation from reappearing in a separate norm estimate. -/
theorem insert_base (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
        lc0Insert (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D) m +
      Tensor0SSpace.toModel
        (deTurckLieDLbFib (I := I) g₁ g₀ x D) m =
    Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D) m -
      Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ g₀ x D) m
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorr0InsertFib_toModel (I := I) g₀ g₁ g₀ x D m,
    deTurckLieDLbFib_toModel (I := I) g₁ g₀ x D m]
  have hN0 : ∀ v : TangentSpace I x,
      lieCorr0NEndo (I := I) g₀ g₁ g₀ x v =
        -(deTurckLieWEndo (I := I) g₁ g₀ x v) := by
    intro v
    simpa using congrArg
      (fun A : TangentSpace I x →L[ℝ] TangentSpace I x => A v)
      (nEndo_base (I := I) (M := M) g₀ g₁ x)
  have e0 : Tensor0SSpace.toModel D
      (Function.update m 0 (lieCorr0NEndo (I := I) g₀ g₁ g₀ x (m 0))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 0 (deTurckLieWEndo (I := I) g₁ g₀ x (m 0)))) := by
    rw [hN0 (m 0), show (-(deTurckLieWEndo (I := I) g₁ g₀ x (m 0))) =
        ((-1 : ℝ) • (deTurckLieWEndo (I := I) g₁ g₀ x (m 0))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  have e1 : Tensor0SSpace.toModel D
      (Function.update m 1 (lieCorr0NEndo (I := I) g₀ g₁ g₀ x (m 1))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 1 (deTurckLieWEndo (I := I) g₁ g₀ x (m 1)))) := by
    rw [hN0 (m 1), show (-(deTurckLieWEndo (I := I) g₁ g₀ x (m 1))) =
        ((-1 : ℝ) • (deTurckLieWEndo (I := I) g₁ g₀ x (m 1))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  rw [e0, e1]
  ring

/-- Exact four-piece smooth-field realization of `lieCorr0Field`. -/
theorem lc0_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg =
      ((lc0Insert (I := I) (M := M) g₀ g₁ g_bg +
          lc0VB (I := I) (M := M) g₀ g₁) +
        lc0AMix (I := I) (M := M) g₀ g₁ g_bg) +
      lc0Riem (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change TensorRSSpace.ofCLM
      (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x) = _
  rw [lieCorr0TotalFib]
  rfl

/-- In the base-background tail, keep the insertion field next to the
endomorphism arm.  This is the cancellation-preserving normal form consumed by
the low-regularity coefficient estimate. -/
theorem tail_base_split (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      (((lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
            lc0Insert (I := I) (M := M) g₀ g₁ g₀) +
          lc0VB (I := I) (M := M) g₀ g₁) +
        lc0AMix (I := I) (M := M) g₀ g₁ g_bg) +
      lc0Riem (I := I) (M := M) g₀ g₁ := by
  rw [lc0_decomp (I := I) (M := M) g₀ g₁ g_bg]
  rw [← insert_base (I := I) (M := M) g₀ g₁ g_bg]
  abel

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
