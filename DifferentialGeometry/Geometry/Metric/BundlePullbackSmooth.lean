import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Geometry.Metric.BundlePullback
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {FV FW : Type*} [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  {V W : B → Type*} [TopologicalSpace (TotalSpace FV V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [TopologicalSpace (TotalSpace FW W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  {n : ℕ∞ω}

def pullbackFiberwiseContinuousLinearEquiv
    (g : ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x)))) :
    ContMDiffRiemannianMetric I n FV V where
  inner := (g.toRiemannianMetric.pullback id e).inner
  symm := (g.toRiemannianMetric.pullback id e).symm
  pos := (g.toRiemannianMetric.pullback id e).pos
  isVonNBounded := (g.toRiemannianMetric.pullback id e).isVonNBounded
  contMDiff := by
    let : RiemannianBundle W := ⟨g.toRiemannianMetric⟩
    let : RiemannianBundle V := ⟨g.toRiemannianMetric.pullback id e⟩
    have h := g.contMDiff.clm_bundle_bilinearComp he he
    exact h.congr fun x => by
      apply TotalSpace.mk_inj.mpr
      ext v w
      rfl

@[simp]
theorem pullbackFiberwiseContinuousLinearEquiv_inner
    (g : ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x))))
    (x : B) (v w : V x) :
    (g.pullbackFiberwiseContinuousLinearEquiv e he).inner x v w =
      g.inner x (e x v) (e x w) := rfl

@[simp]
theorem pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric
    (g : ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x)))) :
    (g.pullbackFiberwiseContinuousLinearEquiv e he).toRiemannianMetric =
      g.toRiemannianMetric.pullback id e := by
  apply RiemannianMetric.ext
  intro x v w
  rfl

end Bundle.ContMDiffRiemannianMetric
