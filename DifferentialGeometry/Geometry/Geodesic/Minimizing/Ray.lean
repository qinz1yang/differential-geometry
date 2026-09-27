import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

section IsMinimizingRayDef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMinimizingRay
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (gamma : ℝ → M) : Prop :=
  gamma 0 = p ∧
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
      riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s)

end IsMinimizingRayDef

namespace IsMinimizingRay

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem start_eq
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    gamma 0 = p :=
  hgamma.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isGeodesicOn
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) :=
  hgamma.2.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem edist_eq
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma)
    ⦃s t : ℝ⦄ (hs : 0 ≤ s) (hst : s ≤ t) :
    riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s) :=
  hgamma.2.2 hs hst

end IsMinimizingRay

end Riemannian
end Geometry
end DifferentialGeometry

end
