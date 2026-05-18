import DifferentialGeometry.Integral.Connection.Ricci

/-!
# Einstein metrics

A smooth Riemannian metric `g` on a manifold `M` is **Einstein with constant `K`**
when its Ricci tensor is proportional to the metric:
$$
  \mathrm{Ric}(V, W) \;=\; K \cdot g(V, W)
$$
for every point `x : M` and every pair of tangent vectors `V, W : T_x M`.

This file ships:

* the predicate `IsEinstein g K`;
* a pointwise re-statement `IsEinstein.apply`;
* the Ricci-flat consequence at constant `0`;
* the symmetry `Ric(V, W) = Ric(W, V)` of the Einstein equation, which on the
  Levi-Civita connection follows from the symmetry of the Ricci tensor and the
  metric.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- A smooth Riemannian metric `g` on `M` is **Einstein with constant `K`**
iff at every point `x : M` and every pair of tangent vectors `V, W`, the
Ricci tensor satisfies `Ric(V, W) = K · g(V, W)`.

The Einstein condition is a classical curvature constraint expressing
proportionality of the Ricci tensor to the metric. Spaces of constant
sectional curvature satisfy it; the converse holds in dimension `2`
trivially and in dimension `3` non-trivially, but fails in dimension `≥ 4`. -/
def IsEinstein (g : SmoothRiemannianMetric I M) (K : ℝ) : Prop :=
  ∀ (x : M) (V W : TangentSpace I x),
    ricciTensor (I := I) g x V W = K * g.inner x V W

/-- The Einstein condition is preserved under taking `W = V`: a
specialised form of the predicate that is often more directly useful. -/
theorem IsEinstein.apply
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : IsEinstein (I := I) g K) (x : M) (V W : TangentSpace I x) :
    ricciTensor (I := I) g x V W = K * g.inner x V W :=
  h x V W

/-- An Einstein metric with constant zero is Ricci-flat: `Ric ≡ 0`. -/
theorem IsEinstein.ricci_eq_zero_of_K_eq_zero
    {g : SmoothRiemannianMetric I M}
    (h : IsEinstein (I := I) g 0) (x : M) (V W : TangentSpace I x) :
    ricciTensor (I := I) g x V W = 0 := by
  have := h x V W
  rw [this]
  ring

/-- Symmetry of the Einstein equation in `V, W`. For the Levi-Civita
connection both sides are symmetric in `V, W`: the Ricci tensor by
`ricciTensor_symm`, and the metric by `g.symm`. -/
theorem IsEinstein.symm
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : IsEinstein (I := I) g K) (x : M) (V W : TangentSpace I x) :
    ricciTensor (I := I) g x V W = ricciTensor (I := I) g x W V := by
  rw [h x V W, h x W V, g.symm x V W]

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
