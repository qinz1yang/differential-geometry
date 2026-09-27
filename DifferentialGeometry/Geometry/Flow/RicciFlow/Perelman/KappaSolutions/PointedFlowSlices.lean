import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps

open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}

def atTime (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) :
    PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) t) (L.atTime (I := I) t) phi where
  partialDiffeomorph := Phi.partialDiffeomorph
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

@[simp] theorem atTime_partialDiffeomorph
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).partialDiffeomorph k = Phi.partialDiffeomorph k := rfl


@[simp] theorem atTime_source
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).source k = Phi.source k := rfl


@[simp] theorem atTime_target
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).target k = Phi.target k := rfl


@[simp] theorem atTime_map
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (Phi.atTime (L := L) t).map k = Phi.map k := rfl

end DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps

end
