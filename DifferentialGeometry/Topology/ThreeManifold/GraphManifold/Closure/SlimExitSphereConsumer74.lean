import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlim

/-!
# Consumer of the slim adapter (arcs): the S³ slim piece as the exit of a sphere arc

Lane S-JUNCTIONS (suffix `_JN74`, group G4c). The `S² × [0, 1]` slim piece of the S³ inhabitant
(`FC39P0SphereSlim.lean`) is the exit of a sphere arc: the map `slimMap`, the end `0` shared with
the model face of `Z₋` and the end `1` new with `endFn = q₀ + 3/5` on `{q₀ > −15/17}`. The adapter
`slimPiecesOfExits74` applied to it gives a `SlimPiecesV2` with the same piece, the same model and
the same classification of the ends as `sphereSlimPieces` (a NON-VACUOUS arc inhabitant of
`SphereArcExit74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The S³ slim arc as the exit of a sphere arc.** -/
def sphereSlimArcExit74 : SphereArcExit74 sphereZeroDomains sphereCuspCores where
  F := slimMap
  smooth := contMDiff_slimMap
  injective := slimMap_injective
  fullRank p := (mfderiv_slimMap_bijective p).1
  ends :=
    { kind := fun b => bif b then none else some slimSharedNeighbour
      fn := fun _ x => sphereHeight x + 3 / 5
      near := fun _ => slimNear
      shared_eq := by
        intro b F hk
        cases b
        · have hF : slimSharedNeighbour = F := Option.some_injective _ hk
          subst hF
          rw [range_slimMap_end]
          change _ = pieceBoundary sphereInnerBall
          rw [pieceBoundary_innerBall]
          ext x
          simp only [slimEndHeight, Bool.cond_false, mem_ofPred_eq]
          constructor <;> intro hx <;> linarith
        · exact absurd hk.symm (Option.some_ne_none F)
      near_interior := fun _ _ _ hx => BoundarylessManifold.isInteriorPoint
      fn_smooth := fun _ _ => (contMDiff_sphereHeight.add contMDiff_const).contMDiffOn
      fn_regular := fun _ _ x _ h0 => slimEndFn_mfderiv x h0
      fn_level := by
        intro b hk
        cases b
        · exact absurd hk (Option.some_ne_none _)
        · rw [range_slimMap_end]
          ext x
          simp only [slimEndHeight, Bool.cond_true, mem_ofPred_eq]
          constructor
          · intro hx
            refine ⟨?_, by linarith⟩
            change -15 / 17 < sphereHeight x
            linarith
          · rintro ⟨-, hx⟩
            linarith
      fn_eq := by
        intro b hk
        rw [range_slimMap]
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩
          exact ⟨h3, by linarith⟩
        · rintro ⟨h3, h2⟩
          have h3' : -15 / 17 < sphereHeight x := h3
          exact ⟨⟨h3'.le, by linarith⟩, h3⟩ }

/-- The one-piece family of the S³ slim arc. -/
def sphereSlimExits74 : Fin 1 → SlimPieceExit74 sphereZeroDomains sphereCuspCores :=
  fun _ => .sphereArc sphereSlimArcExit74

/-- **The S³ slim pieces from the exit of the sphere arc** (the adapter on a real inhabitant). -/
def sphereSlimPiecesOfExits74 : SlimPiecesV2 sphereW sphereZeroDomains sphereCuspCores :=
  slimPiecesOfExits74 sphereSlimExits74 fun j j' h => absurd (Subsingleton.elim j j') h

theorem sphereSlimPiecesOfExits74_count : sphereSlimPiecesOfExits74.count = 1 :=
  rfl

/-- The assembled piece is the S³ slim piece. -/
theorem sphereSlimPiecesOfExits74_piece (j : Fin 1) :
    sphereSlimPiecesOfExits74.piece j = sphereSlimPiece :=
  rfl

/-- The assembled slim pieces classify the ends as `sphereSlimPieces` does: the end `0` is shared
with the model face of `Z₋`, the end `1` is new. -/
theorem sphereSlimPiecesOfExits74_endKind (b : Bool) :
    sphereSlimPiecesOfExits74.endKind ⟨((0 : Fin 1), b), trivial⟩ =
      sphereSlimPieces.endKind ⟨((0 : Fin 1), b), trivial⟩ := by
  cases b <;> rfl

/-- The shared end of the assembled pieces is the model face of `Z₋` (the generic
`slimPiecesOfExits74_shared_eq`). -/
theorem sphereSlimPiecesOfExits74_shared (e : sphereSlimPiecesOfExits74.End)
    (F : NeighbourFace sphereZeroDomains sphereCuspCores)
    (hk : sphereSlimPiecesOfExits74.endKind e = some F) :
    sphereSlimPiecesOfExits74.endSet e = neighbourSet F :=
  slimPiecesOfExits74_shared_eq sphereSlimExits74 _ e F hk

end GC.GraphManifold.Assembly.FC39P0
