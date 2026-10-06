import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimLoopModel74

/-!
# Draft 74, package S2, part 3: the exit of one slim piece and its piece / model / end data

Lane S-JUNCTIONS (suffix `_JN74`, group G4c). The `W`-form of S-ZSP04's slim output
(`zsp04_full_row_ZSP35`, G18 / G19 / G20), after the closed identification `M.ψ`, over one
component of `D₃`:

* an ARC `S² × [0, 1] → W` (resp. `T² × [0, 1] → W`): a smooth injective map with injective
  differential (`SphereArcExit74`, `TorusArcExit74`); its two end slices carry the end data
  `ArcEnds74` (S-ZSP04 G20 in `W`-form: a shared end is a neighbour model face, a free end has a
  regular defining function on an open whole tube, the piece side `≤ 0`);
* a LOOP (`SphereLoopExit74`, `TorusLoopExit74` of `SlimLoopModel74.lean`).

`SlimPieceExit74` is the sum of the four kinds; for every exit the piece, its `SlimModel`, the model
faces of its ends and the end data are defined (`SlimPieceExit74.piece / model / endFace /
endKind / endFn / endNear`) together with the properties the fields of `SlimPiecesV2` ask for.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}

/-- **The end data of an arc** (S-ZSP04 G19 / G20 in `W`-form): for each end `b`, either a neighbour
model face the end slice equals (a zero-face end), or a free end with a regular defining function on
an open set of the interior containing the WHOLE end slice, `≤ 0` exactly on the piece. -/
structure ArcEnds74 (Z : ZeroDomains W) (C : CuspCores W E) (pieceSet : Set W.Carrier)
    (slice : Bool → Set W.Carrier) where
  kind : Bool → Option (NeighbourFace Z C)
  fn : Bool → W.Carrier → ℝ
  near : Bool → TopologicalSpace.Opens W.Carrier
  shared_eq : ∀ b F, kind b = some F → slice b = neighbourSet F
  near_interior : ∀ b, kind b = none → (near b : Set W.Carrier) ⊆ W.interior
  fn_smooth : ∀ b, kind b = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (fn b) (near b)
  fn_regular : ∀ b, kind b = none → ∀ x ∈ near b, fn b x = 0 →
    mfderiv W.model 𝓘(ℝ, ℝ) (fn b) x ≠ 0
  fn_level : ∀ b, kind b = none → slice b = {x | x ∈ near b ∧ fn b x = 0}
  fn_eq : ∀ b, kind b = none → pieceSet ∩ near b = {x | x ∈ near b ∧ fn b x ≤ 0}

/-- **The exit of a sphere arc**: a smooth injective map `S² × [0, 1] → W` with injective
differential (S0 / EFE G1 in `W`-form) and its end data. -/
structure SphereArcExit74 (Z : ZeroDomains W) (C : CuspCores W E) where
  F : ClosureSphere.{0} × Icc (0 : ℝ) 1 → W.Carrier
  smooth : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ F
  injective : Injective F
  fullRank : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model F z)
  ends : ArcEnds74 Z C (range F) fun b => range fun z => F (z, iccEnd b)

/-- **The exit of a torus arc**. -/
structure TorusArcExit74 (Z : ZeroDomains W) (C : CuspCores W E) where
  F : Torus × Icc (0 : ℝ) 1 → W.Carrier
  smooth : ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ F
  injective : Injective F
  fullRank : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model F z)
  ends : ArcEnds74 Z C (range F) fun b => range fun z => F (z, iccEnd b)

/-- A full-rank map from the three-dimensional product model into `W` has bijective differential
(dimensions `2 + 1 = 3` for the sphere interval). -/
theorem sphereArc_bijective74 {Z : ZeroDomains W} {C : CuspCores W E} (a : SphereArcExit74 Z C)
    (z : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model a.F z) :=
  ⟨a.fullRank z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp)).mp (a.fullRank z)⟩

theorem torusArc_bijective74 {Z : ZeroDomains W} {C : CuspCores W E} (a : TorusArcExit74 Z C)
    (z : Torus × Icc (0 : ℝ) 1) :
    Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model a.F z) :=
  ⟨a.fullRank z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    change Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp)).mp (a.fullRank z)⟩

/-- The sphere arc piece. -/
def SphereArcExit74.piece {Z : ZeroDomains W} {C : CuspCores W E} (a : SphereArcExit74 Z C) :
    PieceEmbedding W :=
  sphereIntervalPiece a.F a.smooth (sphereArc_bijective74 a) a.injective

/-- The torus arc piece. -/
def TorusArcExit74.piece {Z : ZeroDomains W} {C : CuspCores W E} (a : TorusArcExit74 Z C) :
    PieceEmbedding W :=
  torusIntervalPiece a.F a.smooth (torusArc_bijective74 a) a.injective

/-- **The exit of one slim piece**: a sphere or torus arc, or a sphere or torus loop. -/
inductive SlimPieceExit74 (Z : ZeroDomains W) (C : CuspCores W E) : Type
  | sphereArc (a : SphereArcExit74 Z C)
  | torusArc (a : TorusArcExit74 Z C)
  | sphereLoop (l : SphereLoopExit74 W)
  | torusLoop (l : TorusLoopExit74 W)

namespace SlimPieceExit74

variable {Z : ZeroDomains W} {C : CuspCores W E}

/-- The piece of an exit. -/
def piece : SlimPieceExit74 Z C → PieceEmbedding W
  | .sphereArc a => a.piece
  | .torusArc a => a.piece
  | .sphereLoop l => sphereLoopPiece74 l
  | .torusLoop l => torusLoopPiece74 l

/-- The slim model of the piece of an exit. -/
def model : (x : SlimPieceExit74 Z C) → SlimModel x.piece
  | .sphereArc a => SlimModel.sphereInterval (sphereIntervalPieceDiffeo a.F a.smooth
      (sphereArc_bijective74 a) a.injective)
  | .torusArc a => SlimModel.torusInterval (torusIntervalPieceDiffeo a.F a.smooth
      (torusArc_bijective74 a) a.injective)
  | .sphereLoop l => sphereLoopModel74 l
  | .torusLoop l => torusLoopModel74 l

/-- The model face of an end of an interval piece (a loop has none). -/
def endFace : (x : SlimPieceExit74 Z C) → Bool → slimModelIsInterval x.model →
    ModelBoundaryFace x.piece
  | .sphereArc a, b, _ => sphereIntervalFace74 a.F a.smooth (sphereArc_bijective74 a) a.injective b
  | .torusArc a, b, _ => torusIntervalFace74 a.F a.smooth (torusArc_bijective74 a) a.injective b
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

theorem endFace_val : ∀ (x : SlimPieceExit74 Z C) (b : Bool) (h : slimModelIsInterval x.model),
    (x.endFace b h).1 = slimModelEnd x.model b
  | .sphereArc _, _, _ => rfl
  | .torusArc _, _, _ => rfl
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

theorem endFace_exhausted : ∀ (x : SlimPieceExit74 Z C) (Fc : ModelBoundaryFace x.piece),
    ∃ (b : Bool) (h : slimModelIsInterval x.model), x.endFace b h = Fc
  | .sphereArc a, Fc => by
      obtain ⟨b, hb⟩ := sphereIntervalFace74_exhausted a.F a.smooth (sphereArc_bijective74 a)
        a.injective Fc
      exact ⟨b, trivial, hb⟩
  | .torusArc a, Fc => by
      obtain ⟨b, hb⟩ := torusIntervalFace74_exhausted a.F a.smooth (torusArc_bijective74 a)
        a.injective Fc
      exact ⟨b, trivial, hb⟩
  | .sphereLoop l, Fc => by
      obtain ⟨-, y, hy, -⟩ := Fc
      have := clopenPiece74_boundary_empty l.region.isClopen l.region.interior l.basePoint_mem
      rw [eq_empty_iff_forall_notMem] at this
      exact (this y hy).elim
  | .torusLoop l, Fc => by
      obtain ⟨-, y, hy, -⟩ := Fc
      have := clopenPiece74_boundary_empty l.region.isClopen l.region.interior l.basePoint_mem
      rw [eq_empty_iff_forall_notMem] at this
      exact (this y hy).elim

/-- The classification of an end: a neighbour model face (shared) or `none` (a new end). -/
def endKind : (x : SlimPieceExit74 Z C) → Bool → slimModelIsInterval x.model →
    Option (NeighbourFace Z C)
  | .sphereArc a, b, _ => a.ends.kind b
  | .torusArc a, b, _ => a.ends.kind b
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

/-- The defining function of an end. -/
def endFn : (x : SlimPieceExit74 Z C) → Bool → slimModelIsInterval x.model → W.Carrier → ℝ
  | .sphereArc a, b, _ => a.ends.fn b
  | .torusArc a, b, _ => a.ends.fn b
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

/-- The neighbourhood of an end. -/
def endNear : (x : SlimPieceExit74 Z C) → Bool → slimModelIsInterval x.model →
    TopologicalSpace.Opens W.Carrier
  | .sphereArc a, b, _ => a.ends.near b
  | .torusArc a, b, _ => a.ends.near b
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

/-- The end slice of an exit in `W` (empty for a loop). -/
def slice : SlimPieceExit74 Z C → Bool → Set W.Carrier
  | .sphereArc a, b => range fun z => a.F (z, iccEnd b)
  | .torusArc a, b => range fun z => a.F (z, iccEnd b)
  | .sphereLoop _, _ => ∅
  | .torusLoop _, _ => ∅

/-- The image of the model end slice of the piece of an exit is its end slice. -/
theorem image_end_eq : ∀ (x : SlimPieceExit74 Z C) (b : Bool) (_ : slimModelIsInterval x.model),
    x.piece.map '' slimModelEnd x.model b = x.slice b
  | .sphereArc a, b, _ =>
      image_sphereInterval_end74 a.F a.smooth (sphereArc_bijective74 a) a.injective b
  | .torusArc a, b, _ =>
      image_torusInterval_end74 a.F a.smooth (torusArc_bijective74 a) a.injective b
  | .sphereLoop _, _, h => h.elim
  | .torusLoop _, _, h => h.elim

/-- A shared end slice is the neighbour model face. -/
theorem slice_eq_of_kind_some : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model) (F : NeighbourFace Z C),
    x.endKind b h = some F → x.slice b = neighbourSet F
  | .sphereArc a, b, _, F, hk => a.ends.shared_eq b F hk
  | .torusArc a, b, _, F, hk => a.ends.shared_eq b F hk
  | .sphereLoop _, _, h, _, _ => h.elim
  | .torusLoop _, _, h, _, _ => h.elim

theorem endNear_interior : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model), x.endKind b h = none →
    (x.endNear b h : Set W.Carrier) ⊆ W.interior
  | .sphereArc a, b, _, hk => a.ends.near_interior b hk
  | .torusArc a, b, _, hk => a.ends.near_interior b hk
  | .sphereLoop _, _, h, _ => h.elim
  | .torusLoop _, _, h, _ => h.elim

theorem endFn_smooth : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model), x.endKind b h = none →
    ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (x.endFn b h) (x.endNear b h)
  | .sphereArc a, b, _, hk => a.ends.fn_smooth b hk
  | .torusArc a, b, _, hk => a.ends.fn_smooth b hk
  | .sphereLoop _, _, h, _ => h.elim
  | .torusLoop _, _, h, _ => h.elim

theorem endFn_regular : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model), x.endKind b h = none →
    ∀ y ∈ x.endNear b h, x.endFn b h y = 0 →
      mfderiv W.model 𝓘(ℝ, ℝ) (x.endFn b h) y ≠ 0
  | .sphereArc a, b, _, hk => a.ends.fn_regular b hk
  | .torusArc a, b, _, hk => a.ends.fn_regular b hk
  | .sphereLoop _, _, h, _ => h.elim
  | .torusLoop _, _, h, _ => h.elim

theorem endFn_level : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model), x.endKind b h = none →
    x.slice b = {y | y ∈ x.endNear b h ∧ x.endFn b h y = 0}
  | .sphereArc a, b, _, hk => a.ends.fn_level b hk
  | .torusArc a, b, _, hk => a.ends.fn_level b hk
  | .sphereLoop _, _, h, _ => h.elim
  | .torusLoop _, _, h, _ => h.elim

theorem endFn_eq : ∀ (x : SlimPieceExit74 Z C) (b : Bool)
    (h : slimModelIsInterval x.model), x.endKind b h = none →
    range x.piece.map ∩ x.endNear b h = {y | y ∈ x.endNear b h ∧ x.endFn b h y ≤ 0}
  | .sphereArc a, b, _, hk => a.ends.fn_eq b hk
  | .torusArc a, b, _, hk => a.ends.fn_eq b hk
  | .sphereLoop _, _, h, _ => h.elim
  | .torusLoop _, _, h, _ => h.elim

end SlimPieceExit74

end GC.GraphManifold.Assembly.FC39P0
