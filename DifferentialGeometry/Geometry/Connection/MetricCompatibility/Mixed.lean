import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Multilinear
import DifferentialGeometry.Geometry.Metric.BundleMixed

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

namespace CovariantDerivative

theorem IsMetricCompatible.mixed_mvfderiv_inner {cov : CovariantDerivative I F V}
    (hcov : cov.IsMetricCompatible) (r s : ℕ)
    (A C : ∀ y, Bundle.continuousMultilinearMap ℝ r F V y →L[ℝ]
      Bundle.continuousMultilinearMap ℝ s F V y) {x : M}
    (hA : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ))
      (fun y => (⟨y, A y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
        (fun y => Bundle.continuousMultilinearMap ℝ r F V y →L[ℝ]
          Bundle.continuousMultilinearMap ℝ s F V y))) x)
    (hC : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ))
      (fun y => (⟨y, C y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
        (fun y => Bundle.continuousMultilinearMap ℝ r F V y →L[ℝ]
          Bundle.continuousMultilinearMap ℝ s F V y))) x)
    (X : TangentSpace I x) :
    mvfderiv (I := I) (fun y =>
      (mixedRiemannianMetric (F := F) (V := V) r s).inner y (A y) (C y)) x X =
      (mixedRiemannianMetric (F := F) (V := V) r s).inner x
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
          I M (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ r F V)
          (ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ s F V)
          (cov.multilinear r) (cov.multilinear s) A x X) (C x) +
      (mixedRiemannianMetric (F := F) (V := V) r s).inner x (A x)
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
          I M (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ r F V)
          (ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ)
          (Bundle.continuousMultilinearMap ℝ s F V)
          (cov.multilinear r) (cov.multilinear s) C x X) := by
  let U := Bundle.continuousMultilinearMap ℝ r F V
  let W := Bundle.continuousMultilinearMap ℝ s F V
  let FU := ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ
  let FW := ContinuousMultilinearMap ℝ (fun _ : Fin s => F) ℝ
  let gr := multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V r
  let _ : RiemannianBundle U := ⟨gr.toRiemannianMetric⟩
  let nr : ∀ y, NormedAddCommGroup (U y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := U) y
  let _ : ∀ y, SeminormedAddCommGroup (U y) := fun y => (nr y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (U y) := fun y => Bundle.instInnerProductSpaceReal (E := U) y
  let _ : IsContMDiffRiemannianBundle I 1 FU U := ⟨gr.inner, gr.contMDiff, fun _ _ _ => rfl⟩
  have hr : (cov.multilinear r).IsMetricCompatible := hcov.multilinear r
  let gs := multilinearContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V s
  let _ : RiemannianBundle W := ⟨gs.toRiemannianMetric⟩
  let ns : ∀ y, NormedAddCommGroup (W y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := W) y
  let _ : ∀ y, SeminormedAddCommGroup (W y) := fun y => (ns y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (W y) := fun y => Bundle.instInnerProductSpaceReal (E := W) y
  let _ : IsContMDiffRiemannianBundle I 1 FW W := ⟨gs.inner, gs.contMDiff, fun _ _ _ => rfl⟩
  have hs : (cov.multilinear s).IsMetricCompatible := hcov.multilinear s
  have h := DifferentialGeometry.HomConnectionGen.mvfderiv_hilbertSchmidtInner
    (cov.multilinear r) hr (cov.multilinear s) hs hA hC X
  exact h

end CovariantDerivative
