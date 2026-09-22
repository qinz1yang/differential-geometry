import DifferentialGeometry.Topology.Manifold.ModelChangeRoundtrip
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.ModelChange


noncomputable section

universe u uE uF uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped _root_.Manifold ContDiff

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

section InverseManifold

variable [FiniteDimensional ℝ E]

def PointedRiemannianManifold.ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    PointedRiemannianManifold.{u, uE, uH} I := by
  let _ : IsManifold I ∞ P.M :=
    (ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff (I := I) (M := P.M) (n := ∞) e).mp P.smooth
  exact {
    M := P.M
    topology := P.topology
    charted := P.charted
    smooth := inferInstance
    t2 := P.t2
    sigmaCompact := P.sigmaCompact
    t2TangentBundle := inferInstance
    basepoint := P.basepoint
    metric := Diffeomorph.pullbackMetricCross P.metric
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I P.M e) }

theorem PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    (P.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  let _ : IsManifold I ∞ M :=
    (ContinuousLinearEquiv.isManifold_transContinuousLinearEquiv_iff (I := I) (M := M) (n := ∞) e).mp smooth
  have hg : (Diffeomorph.pullbackMetricCross g
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e)).transContinuousLinearEquiv e = g := by
    rw [SmoothRiemannianMetric.transContinuousLinearEquiv, Diffeomorph.pullbackMetricCross_trans]
    have heq : (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm.trans
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e) =
          _root_.Diffeomorph.refl (I.transContinuousLinearEquiv e) M ∞ := by ext x; rfl
    rw [heq, Diffeomorph.pullbackMetricCross_refl]
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1


theorem PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} I) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  have hg := g.pullback_transContinuousLinearEquiv e
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1

theorem PointedRiemannianManifold.transContinuousLinearEquiv_surjective
    (e : E ≃L[ℝ] F) :
    Function.Surjective (fun P : PointedRiemannianManifold.{u, uE, uH} I =>
      P.transContinuousLinearEquiv e) :=
  fun P => ⟨P.ofTransContinuousLinearEquiv e, P.transContinuousLinearEquiv_ofTransContinuousLinearEquiv e⟩


end InverseManifold

section InverseMaps

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}

def PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) : PointedRiemannianConvergenceMaps X P phi where
  partialDiffeomorph k := (Phi.partialDiffeomorph k).ofTransContinuousLinearEquiv e e
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

@[simp] theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) :
    (Phi.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = Phi := rfl

@[simp] theorem PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) :
    (Phi.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = Phi := rfl


end InverseMaps

end DifferentialGeometry.CheegerGromovCompactness
