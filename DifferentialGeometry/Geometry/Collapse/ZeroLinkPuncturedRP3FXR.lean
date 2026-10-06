import DifferentialGeometry.Geometry.Collapse.ZeroLinkBranchesFXR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PuncturedRP3CoreFXR

/-!
# D78-5 (1), the fifth branch: the zero link on the actual punctured `ℝP³` core

Lane S-FIX-REG2 (suffix `_FXR`), G4 part 5. `ZeroLinkBranchesFXR` (accepted) ran the one-piece
zero link on the ball, solid torus and twisted I-bundle branches; the branch `puncturedRP3` had no
inhabitant. With `rp3Core74_FXR` (`PuncturedRP3CoreFXR`: the sublevel `{p₀² ≤ 16/25}` of
`ℝP³ = projectiveThreeSpaceLift.{0}`, chart `rp3Chart_FXR` with open unit-ball image
`{p₀² > 16/25}`) the same kernel gives:

* `rp3_zeroLink_FXR`: the table `oneCoreZero_FXR` (one piece, defining function
  `p₀² − 16/25`) satisfies `ZeroLink_LND74` for the identity carrier identification of `ℝP³`;
* `rp3_model_FXR`: the core is not the closed branch and the table's model is the
  `puncturedRP3` model with the chart, the inclusion and the range equation.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The identity carrier identification of `ℝP³` (model form `𝓡 3`). -/
def rp3Id74_FXR : projectiveThreeSpaceLift.{0}.Carrier ≃ₘ⟮𝓡 3,
    (NoCuts.carrier projectiveThreeSpaceLift.{0}).model⟯
    (NoCuts.carrier projectiveThreeSpaceLift.{0}).Carrier :=
  Diffeomorph.refl (NoCuts.carrier projectiveThreeSpaceLift.{0}).model
    projectiveThreeSpaceLift.{0}.Carrier ∞

/-- **Punctured `ℝP³` branch**: the zero link of the actual core `{p₀² ≤ 16/25} ⊂ ℝP³`
(`F = p₀² − 16/25`), for the identity carrier identification. -/
theorem rp3_zeroLink_FXR :
    ZeroLink_LND74 rp3Id74_FXR.toEquiv
      (oneCoreZero_FXR (W := NoCuts.carrier projectiveThreeSpaceLift.{0}) rp3Core74_FXR
        rp3Id74_FXR (closedCarrier_boundary_eq_empty _) rp3Defining_FXR
        contMDiff_rp3Defining_FXR rp3Defining_regular_FXR rfl rp3_frontier_FXR)
      (fun _ : Unit => rp3Set_FXR) (fun _ => interior rp3Set_FXR) (fun _ => rp3Set_FXR)
      (fun _ => rp3Defining_FXR) :=
  zeroLink_oneCore_FXR (W := NoCuts.carrier projectiveThreeSpaceLift.{0}) rp3Core74_FXR
    rp3Id74_FXR (closedCarrier_boundary_eq_empty _) rp3Defining_FXR contMDiff_rp3Defining_FXR
    rp3Defining_regular_FXR rfl rp3_frontier_FXR

/-- The punctured `ℝP³` core is not the closed branch, and the table's model is the
`puncturedRP3` model. -/
theorem rp3_model_FXR (j : Fin (oneCoreZero_FXR
        (W := NoCuts.carrier projectiveThreeSpaceLift.{0}) rp3Core74_FXR rp3Id74_FXR
        (closedCarrier_boundary_eq_empty _) rp3Defining_FXR contMDiff_rp3Defining_FXR
        rp3Defining_regular_FXR rfl rp3_frontier_FXR).count) :
    ¬ rp3Core74_FXR.IsClosed ∧
      (oneCoreZero_FXR (W := NoCuts.carrier projectiveThreeSpaceLift.{0}) rp3Core74_FXR
        rp3Id74_FXR (closedCarrier_boundary_eq_empty _) rp3Defining_FXR
        contMDiff_rp3Defining_FXR rp3Defining_regular_FXR rfl rp3_frontier_FXR).model j =
        .inl (.puncturedRP3 rp3Chart_FXR Subtype.val rp3Solid_FXR.embedding
          rp3Core_range_FXR) :=
  ⟨fun h => h, rfl⟩

end DifferentialGeometry.Geometry.Collapse
