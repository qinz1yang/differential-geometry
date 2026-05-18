import DifferentialGeometry.Geometry.Riemannian.Exp.Basic
import Mathlib.Analysis.Convex.Star

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A subset `U ⊆ M` is a **normal neighborhood** of a point `p : M`
for a smooth Riemannian metric `g` iff there exists an open star-convex
neighborhood `V` of `0 ∈ T_p M`, contained in `expDomain g p`, that the
exponential map `expMap g p` bijects onto `U`.

This formulation captures the topological/set-theoretic content of a
normal neighborhood: the existence of a star-shaped open chart on `U`
through the exponential. The geometric `expMap` is automatically smooth
on `expDomain g p` (whenever that statement is established downstream);
this predicate does **not** itself require smoothness, leaving it for a
separate refinement statement when needed. -/
def NormalNeighborhood
    (g : SmoothRiemannianMetric I M) (p : M) (U : Set M) : Prop :=
  ∃ V : Set (TangentSpace I p),
    IsOpen V ∧
    (0 : TangentSpace I p) ∈ V ∧
    StarConvex ℝ (0 : TangentSpace I p) V ∧
    V ⊆ expDomain (I := I) g p ∧
    Set.BijOn (fun v : TangentSpace I p => expMap (I := I) g p v) V U

/-- A normal neighborhood always contains the base point: the zero
vector belongs to the source set, and `expMap g p 0 = p`, so the
bijection forces `p ∈ U`. -/
theorem NormalNeighborhood.contains_basepoint
    [I.Boundaryless] [CompleteSpace E]
    {g : SmoothRiemannianMetric I M} {p : M} {U : Set M}
    (h : NormalNeighborhood (I := I) g p U) :
    p ∈ U := by
  obtain ⟨V, _hVopen, h0V, _hstar, _hsub, hbij⟩ := h
  -- `expMap g p 0 = p` (a basic identity of `expMap`).
  have hexp0 : expMap (I := I) g p (0 : TangentSpace I p) = p :=
    expMap_zero (I := I) g p
  have : expMap (I := I) g p (0 : TangentSpace I p) ∈ U := by
    have := hbij.1 h0V
    exact this
  rw [hexp0] at this
  exact this

end Exp
end Riemannian
end Geometry
end DifferentialGeometry

end
