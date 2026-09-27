import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


structure TransversePath (p z : M) (sphere : Set M) where
  curve : ℝ → M
  continuous : ContinuousOn curve (Set.Icc 0 1)
  start : curve 0 = p
  finish : curve 1 = z
  collar : PartialDiffeomorph IC I3 Cylinder M ∞
  collar_domain : Set.univ ×ˢ Set.Icc (-1) 1 ⊆ collar.source
  central_eq : sphere = collar '' (Set.univ ×ˢ ({0} : Set ℝ))
  crossings : Finset ℝ
  crossings_interior : ∀ s ∈ crossings, s ∈ Set.Ioo 0 1
  crossings_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, curve s ∈ sphere ↔ s ∈ crossings
  transverse : ∀ s ∈ crossings,
    deriv (fun t => (collar.symm (curve t)).2) s ≠ 0

def TransversePath.intersection {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : ℤ :=
  ∑ s ∈ c.crossings, if 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) s then 1 else -1


structure MinimizingArm (g : SmoothRiemannianMetric I3 M) (x : M) where
  length : ℝ
  length_pos : 0 < length
  point : ℝ → M
  start : point 0 = x
  minimizing : ∀ s ∈ Set.Icc 0 length, ∀ t ∈ Set.Icc 0 length,
    metricDistance g (point s) (point t) = |s - t|


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
