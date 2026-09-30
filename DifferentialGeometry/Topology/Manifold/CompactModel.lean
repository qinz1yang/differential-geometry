import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology
universe u

inductive ModelBoundaryKind
  | closed | withBoundary

abbrev ModelBoundaryKind.Space (k : ModelBoundaryKind) (n : ℕ) [NeZero n] : Type :=
  match k with
  | .closed => EuclideanSpace ℝ (Fin n)
  | .withBoundary => EuclideanHalfSpace n

instance (k : ModelBoundaryKind) (n : ℕ) [NeZero n] : TopologicalSpace (k.Space n) := by
  cases k
  · exact inferInstanceAs (TopologicalSpace (EuclideanSpace ℝ (Fin n)))
  · exact inferInstanceAs (TopologicalSpace (EuclideanHalfSpace n))

abbrev ModelBoundaryKind.model (k : ModelBoundaryKind) (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (k.Space n) := by
  cases k with
  | closed => exact 𝓡 n
  | withBoundary => exact 𝓡∂ n

structure CompactModelManifold (n : ℕ) [NeZero n] where
  kind : ModelBoundaryKind
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (kind.Space n) Carrier]
  [smooth : IsManifold (kind.model n) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  [secondCountable : SecondCountableTopology Carrier]

attribute [instance] CompactModelManifold.topology CompactModelManifold.charts CompactModelManifold.smooth
  CompactModelManifold.hausdorff CompactModelManifold.compact CompactModelManifold.secondCountable

end DifferentialGeometry.Topology
