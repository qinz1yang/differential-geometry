import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminal
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusDecompositionPresentation

/-!
# Mixed stages of the relative normalisation

Lane BR, tier R4 (design `handoffs/20261004-design-br-relative-normalisation.md` §3.1–3.2). A
`MixedStage Q` is a torus presentation of `NoCuts.carrier Q` with a set `prot` of protected seams
and a set `frozen` of frozen pieces carrying an interior hyperbolic geometry; every other piece is
product fibred over a planar base `Pₖ`, `k ∈ {1, 2, 3}` (`ProductFibredPiece`, exact on the whole
half collars), and every side of a frozen piece is a protected seam. With `frozen = ∅` the data
is exactly an `ElementaryPresentation (NoCuts.carrier Q)` (`toElementary`, same torus presentation
by `rfl`).

The measure is the number of inner (unprotected) seams, `innerCount = |protᶜ|`; for an
elementary stage without protected seams it is `ElementaryPresentation.complexity`
(`innerCount_eq_complexity`). Seam pieces, host pieces and filling distances are those of
`Normalize.lean`, read on the torus presentation; the move preconditions `IsMergeSeam`,
`IsSplitSeam`, `IsAbsorbSeam` additionally require the seam to be inner, so no move ever acts at a
protected seam, and `IsTerminal` is the absence of all three. Closed-factor extraction: a terminal
stage without protected seams and without frozen pieces is a move-free elementary presentation,
hence a `TerminalPresentation` (`terminalPresentation`, through P0a's
`TerminalPresentation.ofMoveFree`), with raw witness `toRaw` of the same presentation.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

structure MixedStage (Q : ConnectedClosedOrientedManifold.{u} 3) where
  toTorus : TorusPresentation.{u} (NoCuts.carrier Q)
  prot : Finset (Fin toTorus.pairing.count)
  frozen : Finset (Fin toTorus.components.count)
  hyperbolic : ∀ i ∈ frozen,
    ∃ g : toTorus.cutCarrier.InteriorGeometry (toTorus.components.piece i),
      letI := Manifold.interiorChartedSpace toTorus.cutCarrier.model ∞
        (M := toTorus.cutCarrier.pieceInterior (toTorus.components.piece i))
      letI := Manifold.interiorIsManifold toTorus.cutCarrier.model ∞
        (M := toTorus.cutCarrier.pieceInterior (toTorus.components.piece i))
      g.model = .hyperbolic
  kind : Fin toTorus.components.count → ℕ
  kind_mem : ∀ i, i ∉ frozen → kind i ∈ ({1, 2, 3} : Finset ℕ)
  piece : ∀ i, i ∉ frozen → ProductFibredPiece toTorus i (kind i)
  left_prot : ∀ j, toTorus.leftPiece j ∈ frozen → j ∈ prot
  right_prot : ∀ j, toTorus.rightPiece j ∈ frozen → j ∈ prot

namespace MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

abbrev ProtSeam : Type := {j : Fin σ.toTorus.pairing.count // j ∈ σ.prot}

abbrev Frozen : Type := {i : Fin σ.toTorus.components.count // i ∈ σ.frozen}

def innerCount : ℕ := σ.protᶜ.card

def seamPiece (j : Fin σ.toTorus.pairing.count) : Bool → Fin σ.toTorus.components.count
  | true => σ.toTorus.leftPiece j
  | false => σ.toTorus.rightPiece j

def hostPiece (j : Fin σ.toTorus.pairing.count) (b : Bool) : Fin σ.toTorus.components.count :=
  σ.seamPiece j !b

def fillingDistance (j : Fin σ.toTorus.pairing.count) : Bool → ℕ
  | true =>
    PrimitiveSlope.delta (torusUnit (σ.toTorus.pairing.matching j) • meridianSlope) fiberSlope
  | false =>
    PrimitiveSlope.delta (torusUnit (σ.toTorus.pairing.matching j) • fiberSlope) meridianSlope

def IsMergeSeam (j : Fin σ.toTorus.pairing.count) (b : Bool) : Prop :=
  j ∉ σ.prot ∧ σ.kind (σ.seamPiece j b) = 1 ∧ 2 ≤ σ.kind (σ.hostPiece j b) ∧
    σ.fillingDistance j b = 1

def IsSplitSeam (j : Fin σ.toTorus.pairing.count) (b : Bool) : Prop :=
  j ∉ σ.prot ∧ σ.kind (σ.seamPiece j b) = 1 ∧ σ.kind (σ.hostPiece j b) = 3 ∧
    σ.fillingDistance j b = 0

def IsAbsorbSeam (j : Fin σ.toTorus.pairing.count) (b : Bool) : Prop :=
  j ∉ σ.prot ∧ σ.kind (σ.seamPiece j b) = 1 ∧ σ.kind (σ.hostPiece j b) = 2

def IsTerminal : Prop :=
  ∀ j b, ¬ σ.IsMergeSeam j b ∧ ¬ σ.IsSplitSeam j b ∧ ¬ σ.IsAbsorbSeam j b

theorem seamPiece_not_mem_frozen {j : Fin σ.toTorus.pairing.count} (hj : j ∉ σ.prot)
    (b : Bool) : σ.seamPiece j b ∉ σ.frozen := by
  cases b
  · exact fun h => hj (σ.right_prot j h)
  · exact fun h => hj (σ.left_prot j h)

theorem hostPiece_not_mem_frozen {j : Fin σ.toTorus.pairing.count} (hj : j ∉ σ.prot)
    (b : Bool) : σ.hostPiece j b ∉ σ.frozen :=
  σ.seamPiece_not_mem_frozen hj !b

theorem exists_move_of_not_isTerminal (h : ¬ σ.IsTerminal) :
    ∃ j b, σ.IsMergeSeam j b ∨ σ.IsSplitSeam j b ∨ σ.IsAbsorbSeam j b := by
  by_contra hn
  refine h fun j b => ⟨fun h1 => hn ⟨j, b, Or.inl h1⟩, fun h2 => hn ⟨j, b, Or.inr (Or.inl h2)⟩,
    fun h3 => hn ⟨j, b, Or.inr (Or.inr h3)⟩⟩

def toElementary (h : σ.frozen = ∅) : ElementaryPresentation (NoCuts.carrier Q) where
  toTorus := σ.toTorus
  kind := σ.kind
  kind_mem i := σ.kind_mem i (by simp [h])
  piece i := σ.piece i (by simp [h])

@[simp]
theorem toElementary_toTorus (h : σ.frozen = ∅) : (σ.toElementary h).toTorus = σ.toTorus := rfl

theorem innerCount_eq_complexity (h : σ.frozen = ∅) (hp : σ.prot = ∅) :
    σ.innerCount = (σ.toElementary h).complexity := by
  simp only [innerCount, hp, Finset.compl_empty, Finset.card_univ, Fintype.card_fin,
    ElementaryPresentation.complexity, toElementary_toTorus]

theorem isMoveFree_toElementary (h : σ.frozen = ∅) (hp : σ.prot = ∅) (ht : σ.IsTerminal) :
    (σ.toElementary h).IsMoveFree := by
  rw [ElementaryPresentation.isMoveFree_iff]
  intro j b
  have hj : j ∉ σ.prot := by rw [hp]; exact Finset.notMem_empty j
  obtain ⟨h1, h2, h3⟩ := ht j b
  refine ⟨fun hm => h1 ⟨hj, ?_⟩, fun hs => h2 ⟨hj, ?_⟩, fun ha => h3 ⟨hj, ?_⟩⟩
  · cases b <;> exact hm
  · cases b <;> exact hs
  · cases b <;> exact ha

def terminalPresentation (h : σ.frozen = ∅) (hp : σ.prot = ∅) (ht : σ.IsTerminal) :
    TerminalPresentation Q :=
  TerminalPresentation.ofMoveFree (σ.toElementary h) (σ.isMoveFree_toElementary h hp ht)

theorem terminalPresentation_raw (h : σ.frozen = ∅) (hp : σ.prot = ∅) (ht : σ.IsTerminal) :
    (σ.terminalPresentation h hp ht).raw = (σ.toElementary h).toRaw := rfl

theorem frozen_eq_empty_of_prot_eq_empty (hp : σ.prot = ∅) (hn : 0 < σ.toTorus.pairing.count) :
    σ.frozen = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  obtain ⟨s⟩ := TorusPresentation.nonempty_ownedSide_of_pairing_pos σ.toTorus hn i
  obtain ⟨side, hside⟩ := s
  rcases side with k | k | k
  · have hk : σ.toTorus.leftPiece k ∈ σ.frozen := by
      rw [show σ.toTorus.leftPiece k = i from hside]
      exact hi
    exact absurd (σ.left_prot k hk) (by simp [hp])
  · have hk : σ.toTorus.rightPiece k ∈ σ.frozen := by
      rw [show σ.toTorus.rightPiece k = i from hside]
      exact hi
    exact absurd (σ.right_prot k hk) (by simp [hp])
  · exact absurd k.2 (by simp [σ.toTorus.externalCount_eq_zero])

def ofElementary (E : ElementaryPresentation (NoCuts.carrier Q)) : MixedStage Q where
  toTorus := E.toTorus
  prot := ∅
  frozen := ∅
  hyperbolic i hi := absurd hi (Finset.notMem_empty i)
  kind := E.kind
  kind_mem i _ := E.kind_mem i
  piece i _ := E.piece i
  left_prot _ h := absurd h (Finset.notMem_empty _)
  right_prot _ h := absurd h (Finset.notMem_empty _)

theorem ofElementary_frozen (E : ElementaryPresentation (NoCuts.carrier Q)) :
    (ofElementary E).frozen = ∅ := rfl

theorem ofElementary_prot (E : ElementaryPresentation (NoCuts.carrier Q)) :
    (ofElementary E).prot = ∅ := rfl

theorem toElementary_ofElementary (E : ElementaryPresentation (NoCuts.carrier Q)) :
    (ofElementary E).toElementary (ofElementary_frozen E) = E := rfl

theorem innerCount_ofElementary (E : ElementaryPresentation (NoCuts.carrier Q)) :
    (ofElementary E).innerCount = E.complexity :=
  (ofElementary E).innerCount_eq_complexity (ofElementary_frozen E) (ofElementary_prot E)

end MixedStage

end GC.Seifert.RelativeNormalization
