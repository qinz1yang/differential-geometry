import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ZeroDomainsOfExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74Consumer

/-!
# Draft 74, Z2 kernel: consumer on the S³ outer zero ball (real inhabitant)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G28 (kernel consumer). `zeroDomainsOfExits74` run on the
outer zero ball of the S³ inhabitant (a one-element family): the selected core
`sphereOuterCore74` (G27), the identity ambient diffeomorphism, Z0's definer `3/5 − q₀`
(`sphereZeroRatio 1`, buffer `univ`), and the identity carrier diffeomorphism. The assembled
`ZeroDomains` has one piece, with the range of the tree's outer ball and the ball model.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The exits of the outer zero ball: `{3/5 − q₀ = 0}` is its frontier. -/
theorem sphereOuter_frontier74 :
    {x | sphereZeroRatio 1 x = 0} = frontier (range (cycleBallPiece true).map) := by
  have h := sphereOuterSolid74.boundary_eq
  rw [← h]
  exact (sphereZeroPiece_boundary 1).symm

/-- **The Z2 assembler on the S³ outer ball**: a one-piece `ZeroDomains` from the selected core. -/
def sphereOuterZeroDomains74 : ZeroDomains sphereW :=
  zeroDomainsOfExits74 (ι := Unit) (A := fun _ => range (cycleBallPiece true).map) sphereId74
    (closedCarrier_boundary_eq_empty _) (fun _ => sphereOuterCore74)
    (fun _ => Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) (fun _ => range (cycleBallPiece true).map)
    (fun _ => univ) (fun _ => sphereZeroRatio 1) (fun _ => Set.image_id _)
    (fun _ _ h => absurd (Subsingleton.elim _ _) h) (fun _ => isOpen_univ)
    (fun _ => sphereZeroRatio_smooth 1)
    (fun _ x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
    (fun _ => (sphereZeroPiece_range 1).symm) (fun _ => sphereOuter_frontier74)
    (fun _ _ _ => trivial)

theorem sphereOuterZeroDomains74_count : sphereOuterZeroDomains74.count = 1 :=
  rfl

/-- Its piece has the range of the tree's outer ball. -/
theorem sphereOuterZeroDomains74_range :
    range (sphereOuterZeroDomains74.piece (0 : Fin 1)).map = range (cycleBallPiece true).map := by
  refine (zeroDomainsOfExits74_range (ι := Unit) (A := fun _ => range (cycleBallPiece true).map)
    sphereId74 (closedCarrier_boundary_eq_empty _) (fun _ => sphereOuterCore74)
    (fun _ => Diffeomorph.refl (𝓡 3) sphereW.Carrier ∞) (fun _ => range (cycleBallPiece true).map)
    (fun _ => univ) (fun _ => sphereZeroRatio 1) (fun _ => Set.image_id _)
    (fun _ _ h => absurd (Subsingleton.elim _ _) h) (fun _ => isOpen_univ)
    (fun _ => sphereZeroRatio_smooth 1)
    (fun _ x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
    (fun _ => (sphereZeroPiece_range 1).symm) (fun _ => sphereOuter_frontier74)
    (fun _ _ _ => trivial) (0 : Fin 1)).trans ?_
  exact Set.image_id' _

/-- Its model is the ball model of the selected core (a non-closed branch). -/
theorem sphereOuterZeroDomains74_model :
    sphereOuterZeroDomains74.model (0 : Fin 1) = .inl sphereOuterModel74 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
