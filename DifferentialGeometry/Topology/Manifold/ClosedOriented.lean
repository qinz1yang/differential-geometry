import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v w

structure ClosedOrientedManifold (n : ℕ) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) Carrier]
  [smooth : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  orientation : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Carrier n

attribute [instance] ClosedOrientedManifold.topology ClosedOrientedManifold.charts
  ClosedOrientedManifold.smooth ClosedOrientedManifold.hausdorff ClosedOrientedManifold.compact

namespace ClosedOrientedManifold

variable {n : ℕ}

def opposite (M : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{u} n where
  Carrier := M.Carrier
  orientation := M.orientation.opposite

@[simp] theorem opposite_carrier (M : ClosedOrientedManifold.{u} n) :
    M.opposite.Carrier = M.Carrier := rfl

@[simp] theorem opposite_orientation (M : ClosedOrientedManifold.{u} n) :
    M.opposite.orientation = M.orientation.opposite := rfl

@[simp] theorem opposite_opposite (M : ClosedOrientedManifold.{u} n) :
    M.opposite.opposite = M := by
  cases M
  dsimp only [opposite]
  congr 1
  exact ManifoldOrientation.opposite_opposite _

abbrev OrientedDiffeomorph (M : ClosedOrientedManifold.{u} n)
    (N : ClosedOrientedManifold.{v} n) :=
  {f : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier //
    f.preservesOrientation M.orientation N.orientation}

def OrientedDiffeomorph.refl (M : ClosedOrientedManifold.{u} n) :
    OrientedDiffeomorph M M :=
  ⟨Diffeomorph.refl _ _ ∞, Diffeomorph.preservesOrientation_refl M.orientation⟩

def OrientedDiffeomorph.symm {M : ClosedOrientedManifold.{u} n}
    {N : ClosedOrientedManifold.{v} n} (f : OrientedDiffeomorph M N) :
    OrientedDiffeomorph N M :=
  ⟨f.1.symm, Diffeomorph.preservesOrientation_symm f.2⟩

def OrientedDiffeomorph.trans {M : ClosedOrientedManifold.{u} n}
    {N : ClosedOrientedManifold.{v} n} {P : ClosedOrientedManifold.{w} n}
    (f : OrientedDiffeomorph M N) (g : OrientedDiffeomorph N P) :
    OrientedDiffeomorph M P :=
  ⟨f.1.trans g.1, Diffeomorph.preservesOrientation_trans f.2 g.2⟩

end ClosedOrientedManifold

structure ConnectedClosedOrientedManifold (n : ℕ) extends ClosedOrientedManifold.{u} n where
  [connected : ConnectedSpace Carrier]

attribute [instance] ConnectedClosedOrientedManifold.connected

namespace ConnectedClosedOrientedManifold

variable {n : ℕ}

def opposite (M : ConnectedClosedOrientedManifold.{u} n) :
    ConnectedClosedOrientedManifold.{u} n where
  toClosedOrientedManifold := M.toClosedOrientedManifold.opposite
  connected := M.connected

@[simp] theorem opposite_carrier (M : ConnectedClosedOrientedManifold.{u} n) :
    M.opposite.Carrier = M.Carrier := rfl

end ConnectedClosedOrientedManifold

end DifferentialGeometry.Topology
