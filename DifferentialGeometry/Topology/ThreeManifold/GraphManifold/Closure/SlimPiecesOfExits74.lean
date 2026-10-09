import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPieceExit74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, package S2, part 4: `SlimPiecesV2` from the exits of the slim pieces

Lane S-JUNCTIONS (suffix `_JN74`, group G4c). A finite family of slim piece exits
(`SlimPieceExit74`) with pairwise disjoint images is a `SlimPiecesV2 W Z C`: the pieces and models
of the exits, the model faces of the ends (`endFace`, exhausted by the two end slices of an
interval piece; a loop has no end), the classification `endKind`, and the defining function data of
the new ends. Over `D` (`StageCutChoice74`), the component bookkeeping makes the images disjoint
and gives `SlimCutPieces74` (`SlimExit74`, `slimCutPieces_of_exit74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
  {C : CuspCores W E}

/-- **`SlimPiecesV2` from a finite family of slim piece exits** with pairwise disjoint images. -/
def slimPiecesOfExits74 {m : ℕ} (X : Fin m → SlimPieceExit74 Z C)
    (hdisj : Pairwise fun j j' => Disjoint (range (X j).piece.map) (range (X j').piece.map)) :
    SlimPiecesV2 W Z C where
  count := m
  piece j := (X j).piece
  model j := (X j).model
  disjoint := hdisj
  endFace e := (X e.1.1).endFace e.1.2 e.2
  endFace_eq e := (X e.1.1).endFace_val e.1.2 e.2
  endFace_exhausted j Fc := (X j).endFace_exhausted Fc
  endKind e := (X e.1.1).endKind e.1.2 e.2
  endFn e := (X e.1.1.1).endFn e.1.1.2 e.1.2
  endNear e := (X e.1.1.1).endNear e.1.1.2 e.1.2
  endNear_interior e := (X e.1.1.1).endNear_interior e.1.1.2 e.1.2 e.2
  endFn_smooth e := (X e.1.1.1).endFn_smooth e.1.1.2 e.1.2 e.2
  endFn_regular e := (X e.1.1.1).endFn_regular e.1.1.2 e.1.2 e.2
  endFn_level e := ((X e.1.1.1).image_end_eq e.1.1.2 e.1.2).trans
    ((X e.1.1.1).endFn_level e.1.1.2 e.1.2 e.2)
  endFn_eq e := (X e.1.1.1).endFn_eq e.1.1.2 e.1.2 e.2

/-- The shared ends of the assembled slim pieces are the neighbour model faces. -/
theorem slimPiecesOfExits74_shared_eq {m : ℕ} (X : Fin m → SlimPieceExit74 Z C)
    (hdisj : Pairwise fun j j' => Disjoint (range (X j).piece.map) (range (X j').piece.map))
    (e : (slimPiecesOfExits74 X hdisj).End) (F : NeighbourFace Z C)
    (hk : (slimPiecesOfExits74 X hdisj).endKind e = some F) :
    (slimPiecesOfExits74 X hdisj).endSet e = neighbourSet F :=
  ((X e.1.1).image_end_eq e.1.2 e.2).trans ((X e.1.1).slice_eq_of_kind_some e.1.2 e.2 F hk)

/-! ## Over the cut choice: the exits indexed by the components of `D₃` -/

/-- **The slim exit of a cut choice** (S-ZSP04's arcs and loops over the components of `D₃`, in
`W`-form): finitely many piece exits in bijection with the ACTUAL components of `D₃`, each with
image the WHOLE `f₃`-preimage of its component. -/
structure SlimExit74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  count : ℕ
  exit : Fin count → SlimPieceExit74 A.zero A.cusp
  componentEquiv : Fin count ≃ ActualComponent D.D₃
  piece_range : ∀ j, range (exit j).piece.map =
    {x | ∃ h : x ∈ A.slim.parent, A.slim.proj ⟨x, h⟩ ∈ (componentEquiv j).1}

/-- The images of the exits of distinct components are disjoint. -/
theorem SlimExit74.disjoint {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    (X : SlimExit74 A D) :
    Pairwise fun j j' => Disjoint (range (X.exit j).piece.map) (range (X.exit j').piece.map) := by
  intro j j' hne
  rw [X.piece_range j, X.piece_range j']
  refine Set.disjoint_left.2 ?_
  rintro x ⟨h, hx⟩ ⟨h', hx'⟩
  have hc := ActualComponent.disjoint_of_ne (fun h0 => hne (X.componentEquiv.injective h0))
  exact Set.disjoint_left.1 hc hx hx'

/-- **`SlimCutPieces74` from the slim exit** (the adapter of S-ZSP04's slim bundle). -/
def slimCutPieces_of_exit74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    (X : SlimExit74 A D) : SlimCutPieces74 A D where
  pieces := slimPiecesOfExits74 X.exit X.disjoint
  componentEquiv := X.componentEquiv
  piece_range := X.piece_range
  shared_eq := slimPiecesOfExits74_shared_eq X.exit X.disjoint

end GC.GraphManifold.Assembly.FC39P0
