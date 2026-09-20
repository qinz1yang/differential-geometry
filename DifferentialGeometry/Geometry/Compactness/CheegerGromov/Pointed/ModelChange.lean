import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Bundle.FiberBundleHausdorff


noncomputable section

universe u uE uF uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2

def PointedRiemannianManifold.transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    PointedRiemannianManifold.{u, uF, uH} (I := I.transContinuousLinearEquiv e) where
  M := P.M
  topology := P.topology
  charted := P.charted
  smooth := inferInstance
  sigmaCompact := P.sigmaCompact
  t2 := P.t2
  t2TangentBundle := inferInstance
  basepoint := P.basepoint
  metric := P.metric.transContinuousLinearEquiv e

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_carrier
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).M = P.M := rfl

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_basepoint
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).basepoint = P.basepoint := rfl

@[simp]
theorem PointedRiemannianManifold.transContinuousLinearEquiv_metric
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).metric = P.metric.transContinuousLinearEquiv e := rfl

def PointedRiemannianSeq.transContinuousLinearEquiv
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) :
    PointedRiemannianSeq.{u, uF, uH} (I := I.transContinuousLinearEquiv e) where
  obj k := (X.obj k).transContinuousLinearEquiv e

@[simp]
theorem PointedRiemannianSeq.transContinuousLinearEquiv_obj
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (e : E ≃L[ℝ] F) (k : ℕ) :
    (X.transContinuousLinearEquiv e).obj k = (X.obj k).transContinuousLinearEquiv e := rfl

def PointedRiemannianConvergenceMaps.transContinuousLinearEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) :
    PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) subseq where
  partialDiffeomorph k :=
    { toPartialEquiv := (Phi.partialDiffeomorph k).toPartialEquiv
      open_source := (Phi.partialDiffeomorph k).open_source
      open_target := (Phi.partialDiffeomorph k).open_target
      contMDiffOn_toFun :=
        (e.contMDiffOn_transContinuousLinearEquiv_left).mpr
          ((e.contMDiffOn_transContinuousLinearEquiv_right).mpr
            (Phi.partialDiffeomorph k).contMDiffOn_toFun)
      contMDiffOn_invFun :=
        (e.contMDiffOn_transContinuousLinearEquiv_left).mpr
          ((e.contMDiffOn_transContinuousLinearEquiv_right).mpr
            (Phi.partialDiffeomorph k).contMDiffOn_invFun) }
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_partialEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    ((Phi.transContinuousLinearEquiv e).partialDiffeomorph k).toPartialEquiv =
      (Phi.partialDiffeomorph k).toPartialEquiv := rfl

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).source k = Phi.source k := rfl

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).target k = Phi.target k := rfl

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).map k = Phi.map k := rfl

@[simp]
theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_symm
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P subseq) (e : E ≃L[ℝ] F) (k : ℕ) :
    (((Phi.transContinuousLinearEquiv e).partialDiffeomorph k).symm :
      (X.obj (subseq k)).M → P.M) = (Phi.partialDiffeomorph k).symm := rfl

end DifferentialGeometry.CheegerGromovCompactness
