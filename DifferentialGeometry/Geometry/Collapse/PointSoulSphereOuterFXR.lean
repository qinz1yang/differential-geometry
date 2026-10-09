import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfSublevel74
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74Consumer
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowPoint
import DifferentialGeometry.Geometry.Collapse.ZeroLinkBranchesFXR

/-!
# D78-5 (1), the bridge predicates: a concrete `PointSoulCoreSublevel` on the S³ outer ball

Lane S-FIX-REG2 (suffix `_FXR`), G6. `PointSoulCoreSublevel Nc A` (LPA05's `D³` clause) had no
concrete inhabitant in the tree. This file inhabits it for the actual S³ outer ball
`A = range (cycleBallPiece true).map` (`q₀ ≥ 3/5`, the zero ball of the compiled two-ball cycle),
with the model `Nc = ℝ³` and the point-soul bundle `V = Trivial (Fin 0 → ℝ) ℝ³` over the one-point
base `Fin 0 → ℝ`:

* carrier `D = trivialPointDiffeomorph` (total space `= ℝ³`);
* ambient partial diffeomorphism `Ψ = (cycleBallAmbient true).symm` (inverse stereographic chart),
  with `Ψ '' A = closedBall 0 1 = {‖(D⁻¹ y).2‖ ≤ 1}` (`T₀ = 1`);
* the closed-cell diffeomorphism `Φ` from the point row
  `exists_closedCell_diffeomorph_discCore_of_subsingleton`.

Consumers: `nonempty_selectedCore74_ofPointSoul` (the bridge to `SelectedSmoothCore74`) runs on it
(`nonempty_selectedCore74_sphereOuter_FXR`), and the one-piece zero link of `ZeroLinkBranchesFXR`
runs on the core the bridge produces (`sphereOuter_zeroLink_bridge_FXR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The S³ outer ball is the image of the closed unit ball under the stereographic chart. -/
theorem range_cycleBallPiece_true_FXR :
    range (cycleBallPiece true).map = cycleBallAmbient true '' closedBall (0 : E3) 1 := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, by simpa using x.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, by simpa using hy⟩, rfl⟩

/-- **A concrete point-soul sublevel**: the S³ outer ball `A` is a `PointSoulCoreSublevel` with the
model `ℝ³` (soul bundle `Trivial (Fin 0 → ℝ) ℝ³` over a point, `T₀ = 1`). -/
theorem pointSoulCoreSublevel_sphereOuter_FXR :
    PointSoulCoreSublevel (M := sphereW.Carrier) E3 (range (cycleBallPiece true).map) := by
  have hd : Module.finrank ℝ ((Fin 0 → ℝ) × E3) = 2 + 1 := by simp
  have h0 : Module.finrank ℝ (Fin 0 → ℝ) = 0 := by simp
  let b₀ : Fin 0 → ℝ := 0
  let D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, E3)) I3
      (TotalSpace E3 (Trivial (Fin 0 → ℝ) E3)) E3 ∞ :=
    ZeroModel.trivialPointDiffeomorph (IB := 𝓘(ℝ, Fin 0 → ℝ)) (B := Fin 0 → ℝ) (E := E3) b₀
  refine ⟨E3, inferInstance, inferInstance, inferInstance, Trivial (Fin 0 → ℝ) E3,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, D, hd, 1, one_pos, (cycleBallAmbient true).symm, ?_, ?_, ?_⟩
  · rw [range_cycleBallPiece_true_FXR]
    rintro _ ⟨y, -, rfl⟩
    exact (cycleBallAmbient true).map_source (by rw [cycleBallAmbient_source]; exact mem_univ _)
  · have hl : ∀ x : E3, (cycleBallAmbient true).symm (cycleBallAmbient true x) = x := fun x =>
      (cycleBallAmbient true).left_inv (by rw [cycleBallAmbient_source]; exact mem_univ x)
    rw [range_cycleBallPiece_true_FXR, image_image]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ‖((D.symm ((cycleBallAmbient true).symm (cycleBallAmbient true x))).snd)‖ ≤ 1
      rw [hl x]
      exact mem_closedBall_zero_iff.mp hx
    · intro hy
      refine ⟨y, mem_closedBall_zero_iff.mpr hy, ?_⟩
      exact hl y
  · exact ZeroModel.exists_closedCell_diffeomorph_discCore_of_subsingleton (m := 2) hd h0 D 1
      one_pos

/-- **The bridge runs on a non-closed input**: `nonempty_selectedCore74_ofPointSoul` applied to
the concrete point-soul sublevel gives a selected core of the S³ outer ball. -/
theorem nonempty_selectedCore74_sphereOuter_FXR :
    Nonempty (SelectedSmoothCore74.{0, 0} (range (cycleBallPiece true).map)) :=
  nonempty_selectedCore74_ofPointSoul (Nc := E3) pointSoulCoreSublevel_sphereOuter_FXR

/-- The selected core of the S³ outer ball produced by the bridge. -/
def sphereOuterBridgeCore_FXR : SelectedSmoothCore74.{0, 0} (range (cycleBallPiece true).map) :=
  Classical.choice nonempty_selectedCore74_sphereOuter_FXR

/-- **The zero link runs on the bridge's core**: the one-piece zero table of the core produced by
`nonempty_selectedCore74_ofPointSoul` from the point-soul sublevel satisfies `ZeroLink_LND74`
(the same table data as `sphereOuter_zeroLink_FXR`, with the core replaced by the bridge's). -/
theorem sphereOuter_zeroLink_bridge_FXR :
    ZeroLink_LND74 sphereId74.toEquiv
      (oneCoreZero_FXR (W := sphereW) sphereOuterBridgeCore_FXR sphereId74
        (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
        (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
        (sphereZeroPiece_range 1).symm sphereOuter_frontier74)
      (fun _ : Unit => range (cycleBallPiece true).map)
      (fun _ => interior (range (cycleBallPiece true).map))
      (fun _ => range (cycleBallPiece true).map) (fun _ => sphereZeroRatio 1) :=
  zeroLink_oneCore_FXR (W := sphereW) sphereOuterBridgeCore_FXR sphereId74
    (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
    (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
    (sphereZeroPiece_range 1).symm sphereOuter_frontier74

end DifferentialGeometry.Geometry.Collapse
