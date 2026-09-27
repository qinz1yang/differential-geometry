import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Topology.StandardModel
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev C := Metric.sphere (0 : E3) 1 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cylinderReferenceCopy : DifferentialGeometry.Geometry.Topology.StandardModelCopy IC C E3 :=
  DifferentialGeometry.Geometry.Topology.standardModelCopy (I := IC) (M := C)
    (ContinuousLinearEquiv.ofFinrankEq (by simp))

def cylinderReferenceMetric : SmoothRiemannianMetric (𝓡 3) cylinderReferenceCopy.Q :=
  Diffeomorph.pullbackMetricCross (roundCylinderMetric (E := E3) (n := 2))
    cylinderReferenceCopy.equiv.symm

theorem cylinderReferenceMetric_inner (q : cylinderReferenceCopy.Q)
    (v w : TangentSpace (𝓡 3) q) :
    cylinderReferenceMetric.inner q v w =
      (roundCylinderMetric (E := E3) (n := 2)).inner
        (cylinderReferenceCopy.equiv.symm q)
        (mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q v)
        (mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q w) :=
  Diffeomorph.pullbackMetricCross_inner _ _ q v w

theorem pullback_cylinderReferenceMetric :
    Diffeomorph.pullbackMetricCross cylinderReferenceMetric cylinderReferenceCopy.equiv =
      roundCylinderMetric (E := E3) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let e := cylinderReferenceCopy.equiv
  have hd := (e.toOpenPartialHomeomorph_mdifferentiable
    (by decide : (∞ : ℕ∞ω) ≠ 0)).symm_comp_deriv
      (show x ∈ e.toHomeomorph.toOpenPartialHomeomorph.source from mem_univ x)
  have hv : mfderiv (𝓡 3) IC e.symm (e x) (mfderiv IC (𝓡 3) e x v) = v :=
    congrArg (fun D => D v) hd
  have hw : mfderiv (𝓡 3) IC e.symm (e x) (mfderiv IC (𝓡 3) e x w) = w :=
    congrArg (fun D => D w) hd
  change (Diffeomorph.pullbackMetricCross
    (Diffeomorph.pullbackMetricCross (roundCylinderMetric (E := E3) (n := 2)) e.symm)
      e).inner x v w = _
  rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    hv, hw, e.symm_apply_apply]

theorem cylinderReferenceMetric_edist (q r : cylinderReferenceCopy.Q) :
    riemannianEDistOf cylinderReferenceMetric q r =
      riemannianEDistOf (roundCylinderMetric (E := E3) (n := 2))
        (cylinderReferenceCopy.equiv.symm q) (cylinderReferenceCopy.equiv.symm r) :=
  edistOf_pullbackMetricCross _ _ q r

theorem cylinderReferenceMetric_edist_equiv (x y : C) :
    riemannianEDistOf cylinderReferenceMetric
      (cylinderReferenceCopy.equiv x) (cylinderReferenceCopy.equiv y) =
        riemannianEDistOf (roundCylinderMetric (E := E3) (n := 2)) x y := by
  simpa only [Diffeomorph.symm_apply_apply] using
    cylinderReferenceMetric_edist (cylinderReferenceCopy.equiv x) (cylinderReferenceCopy.equiv y)

def cylinderPointedReference : PointedRiemannianManifold (𝓡 3) where
  M := cylinderReferenceCopy.Q
  basepoint := cylinderReferenceCopy.equiv (spherePoint, 0)
  metric := cylinderReferenceMetric

theorem cylinderPointedReference_complete : MetricComplete cylinderPointedReference := by
  have h0 : RiemannianMetricComplete (roundCylinderMetric (E := E3) (n := 2)) := by
    simpa only [shrinkingCylinderMetric_zero] using
      (shrinkingCylinderMetric_complete (E := E3) 0)
  have hQ : RiemannianMetricComplete cylinderReferenceMetric :=
    DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      h0 cylinderReferenceCopy.equiv.symm
  exact hQ.complete

end DifferentialGeometry.PDE.RicciFlow

end
