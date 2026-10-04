import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Interfaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Elementary

/-!
# The induction skeleton of the (S⁺) normalization

Plan P3 of the design review (§6) and Step C of `20261003-skeleton-factor-inheritance.md`,
with the moves as named inputs. The measure of an `ElementaryPresentation` is its pairing count
(`complexity`); no secondary measure and no rank recursion are needed, since a split lowers the
count on both summands.

A seam `j` with side `b` (`true`: left, `false`: right) is a filling seam when the piece on side
`b` is a solid torus (`kind = 1`); `hostPiece` is the other piece, `seamPiece j !b`. The filling
distance compares the meridian `(1, 0)` of the solid torus with the fibre `(0, 1)` of the host,
in the host's port coordinates through `torusUnit` of the matching; for `b = true` this is the
convention of `SeifertBlock` (`delta_fiberSlope`), and `fillingDistance_false` reads the
`b = false` case in the left coordinates. The move preconditions are `IsMergeSeam` (host of kind
`≥ 2`, distance `1`), `IsSplitSeam` (host a pants, distance `0`) and `IsAbsorbSeam` (host an
annulus). `IsMoveFree` (no seam left to simplify) says that every solid torus hangs on a solid
torus or on a pants at distance `≥ 2`; `isMoveFree_iff` identifies it with the absence of all
three preconditions. `IsTerminalElementary` is `IsMoveFree ∧ SeifertFactor Q`: grouping a pants
with its cone solid tori into a `SeifertBlock` is the partial assembly of P2, so the block
marking is not yet expressible from `E` and the factor property is stated directly.

The moves act on elementary presentations of the oriented carrier `NoCuts.carrier Q` of a closed
`Q`, so the orientation is the carrier's and there are no external collars to preserve; seams
next to the modified pieces may be reparametrized. `MoveMerge` (M1) absorbs a solid torus at
distance `1` into its host, `P_k × S¹ ∪ D² × S¹ ≅ P_{k-1} × S¹`; the host has kind `≥ 2`, so the
result is elementary, and the zero-seam case (two solid tori) is move-free. `MoveAbsorb` (M3)
uses that an annulus piece with a solid torus is a solid torus. Both lower the count by exactly
one. `MoveSplit` (M2) fills a pants along its fibre, `(S¹ × D²) # (S¹ × D²)`, and outputs an
oriented splitting `A # B ≅ Q` whose summands are Seifert factors or carry elementary
presentations of smaller count (`ElementaryBelow`): `n′ + n″ = n - 1` for a separating sphere,
`Q ≅ Q′ # S² × S¹` with `n′ = n - 1` otherwise. `MoveTerminal` (M4) certifies a move-free
presentation. `Progress` is the single step: a non-terminal presentation shrinks or splits;
`progress_of_moves` derives it from the four moves.

The induction `seifertRefinement_of_elementarizeClosed_of_progress` elementarizes, recurses on the
count and concatenates the factor lists of the summands (`finiteConnectedSum_append`). Its input
`ElementarizeClosed` only asks for some elementary presentation of a closed carrier, with no
collar clause, so a germ-level collar contract plugs in without reopening the skeleton:
`ElementarizeOnSubCollar` is `Elementarize` with the external collars agreeing only for
`0 ≤ s < δ`, some `δ > 0` (the output shape of `exists_torusCollar_straightening`), and both it
and `Elementarize` imply `ElementarizeClosed`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def complexity (E : ElementaryPresentation W) : ℕ := E.toTorus.pairing.count

def seamPiece (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    Bool → Fin E.toTorus.components.count
  | true => E.toTorus.leftPiece j
  | false => E.toTorus.rightPiece j

def hostPiece (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Fin E.toTorus.components.count :=
  E.seamPiece j !b

def fillingDistance (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) : Bool → ℕ
  | true =>
    PrimitiveSlope.delta (torusUnit (E.toTorus.pairing.matching j) • meridianSlope) fiberSlope
  | false =>
    PrimitiveSlope.delta (torusUnit (E.toTorus.pairing.matching j) • fiberSlope) meridianSlope

theorem fillingDistance_false (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    E.fillingDistance j false = PrimitiveSlope.delta
      ((torusUnit (E.toTorus.pairing.matching j))⁻¹ • meridianSlope) fiberSlope := by
  rw [PrimitiveSlope.delta_comm,
    ← PrimitiveSlope.delta_smul (torusUnit (E.toTorus.pairing.matching j)), smul_inv_smul]
  rfl

def IsMergeSeam (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Prop :=
  E.kind (E.seamPiece j b) = 1 ∧ 2 ≤ E.kind (E.hostPiece j b) ∧ E.fillingDistance j b = 1

def IsSplitSeam (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Prop :=
  E.kind (E.seamPiece j b) = 1 ∧ E.kind (E.hostPiece j b) = 3 ∧ E.fillingDistance j b = 0

def IsAbsorbSeam (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Prop :=
  E.kind (E.seamPiece j b) = 1 ∧ E.kind (E.hostPiece j b) = 2

def IsMoveFree (E : ElementaryPresentation W) : Prop :=
  ∀ j b, E.kind (E.seamPiece j b) = 1 →
    E.kind (E.hostPiece j b) = 1 ∨ (E.kind (E.hostPiece j b) = 3 ∧ 2 ≤ E.fillingDistance j b)

theorem kind_eq_one_or_two_or_three (E : ElementaryPresentation W)
    (i : Fin E.toTorus.components.count) : E.kind i = 1 ∨ E.kind i = 2 ∨ E.kind i = 3 := by
  simpa using E.kind_mem i

theorem isMoveFree_iff (E : ElementaryPresentation W) :
    E.IsMoveFree ↔ ∀ j b, ¬ E.IsMergeSeam j b ∧ ¬ E.IsSplitSeam j b ∧ ¬ E.IsAbsorbSeam j b := by
  constructor
  · intro h j b
    refine ⟨fun ⟨hs, hk, hd⟩ => ?_, fun ⟨hs, hk, hd⟩ => ?_, fun ⟨hs, hk⟩ => ?_⟩
    · rcases h j b hs with h1 | ⟨-, h2⟩ <;> omega
    · rcases h j b hs with h1 | ⟨-, h2⟩ <;> omega
    · rcases h j b hs with h1 | ⟨h1, -⟩ <;> omega
  · intro h j b hs
    obtain ⟨hM, hS, hA⟩ := h j b
    rcases E.kind_eq_one_or_two_or_three (E.hostPiece j b) with hk | hk | hk
    · exact Or.inl hk
    · exact absurd ⟨hs, hk⟩ hA
    · refine Or.inr ⟨hk, ?_⟩
      by_contra hd
      rcases Nat.lt_or_ge (E.fillingDistance j b) 1 with h0 | h1
      · exact hS ⟨hs, hk, by omega⟩
      · exact hM ⟨hs, by omega, by omega⟩

end ElementaryPresentation

open ElementaryPresentation

def ElementaryBelow (n : ℕ) (A : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  SeifertFactor A ∨ ∃ E : ElementaryPresentation (NoCuts.carrier A), E.complexity < n

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

def IsTerminalElementary (E : ElementaryPresentation (NoCuts.carrier Q)) : Prop :=
  E.IsMoveFree ∧ SeifertFactor Q

def Shrinks (E : ElementaryPresentation (NoCuts.carrier Q)) : Prop :=
  ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity < E.complexity

def SplitsBelow (E : ElementaryPresentation (NoCuts.carrier Q)) : Prop :=
  ∃ A B : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum A B).toClosedOrientedManifold Q.toClosedOrientedManifold) ∧
    ElementaryBelow E.complexity A ∧ ElementaryBelow E.complexity B

end ElementaryPresentation

def MoveMerge : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool), E.IsMergeSeam j b →
      ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity + 1 = E.complexity

def MoveSplit : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool), E.IsSplitSeam j b → E.SplitsBelow

def MoveAbsorb : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool), E.IsAbsorbSeam j b →
      ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity + 1 = E.complexity

def MoveTerminal : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q)),
    E.IsMoveFree → SeifertFactor Q

def Progress : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q)),
    ¬ E.IsTerminalElementary → E.Shrinks ∨ E.SplitsBelow

theorem progress_of_moves (hM : MoveMerge.{u}) (hS : MoveSplit.{u}) (hA : MoveAbsorb.{u})
    (hT : MoveTerminal.{u}) : Progress.{u} := by
  intro Q E hE
  have hR : ¬ ∀ j b, ¬ E.IsMergeSeam j b ∧ ¬ E.IsSplitSeam j b ∧ ¬ E.IsAbsorbSeam j b :=
    fun h => hE ⟨E.isMoveFree_iff.2 h, hT Q E (E.isMoveFree_iff.2 h)⟩
  simp only [not_forall] at hR
  obtain ⟨j, b, h⟩ := hR
  by_cases h1 : E.IsMergeSeam j b
  · obtain ⟨E', hE'⟩ := hM Q E j b h1
    exact Or.inl ⟨E', by omega⟩
  by_cases h2 : E.IsSplitSeam j b
  · exact Or.inr (hS Q E j b h2)
  · obtain ⟨E', hE'⟩ := hA Q E j b (not_not.1 fun h3 => h ⟨h1, h2, h3⟩)
    exact Or.inl ⟨E', by omega⟩

private theorem exists_factors_of_elementaryBelow {n : ℕ}
    (ih : ∀ m < n, ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)), E.complexity = m →
        ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), (∀ R ∈ L, SeifertFactor R) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (finiteConnectedSum L).toClosedOrientedManifold Q.toClosedOrientedManifold))
    {A : ConnectedClosedOrientedManifold.{u} 3} (hA : ElementaryBelow n A) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), (∀ R ∈ L, SeifertFactor R) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold A.toClosedOrientedManifold) := by
  rcases hA with hA | ⟨E, hE⟩
  · refine ⟨[A], fun R hR => ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
    rw [List.mem_singleton.mp hR]
    exact hA
  · exact ih _ hE A E rfl

def ElementarizeClosed : Prop :=
  ∀ P : ConnectedClosedOrientedManifold.{u} 3, RawGraphPresentation (NoCuts.carrier P) →
    Nonempty (ElementaryPresentation (NoCuts.carrier P))

def ElementarizeOnSubCollar : Prop :=
  ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
    ∃ E : ElementaryPresentation W, ∃ h : E.toTorus.externalCount = G.externalCount,
      ∃ ψ : Fin G.externalCount →
          (GC.Endpoint.Torus ≃ₘ⟮torusModel, torusModel⟯ GC.Endpoint.Torus),
        ∃ δ > (0 : ℝ), ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
          E.toTorus.external.collar (Fin.cast h.symm i) p = G.external.collar i (ψ i p.1, p.2)

theorem elementarizeOnSubCollar_of_elementarize (h : Elementarize.{u}) :
    ElementarizeOnSubCollar.{u} := by
  intro W G
  obtain ⟨E, hc, ψ, hψ⟩ := h W G
  exact ⟨E, hc, ψ, 1, one_pos, fun i p hp _ => hψ i p hp⟩

theorem elementarizeClosed_of_elementarizeOnSubCollar (h : ElementarizeOnSubCollar.{u}) :
    ElementarizeClosed.{u} := by
  intro P G
  obtain ⟨E, -⟩ := h _ G
  exact ⟨E⟩

theorem elementarizeClosed_of_elementarize (h : Elementarize.{u}) : ElementarizeClosed.{u} :=
  elementarizeClosed_of_elementarizeOnSubCollar (elementarizeOnSubCollar_of_elementarize h)

theorem seifertRefinement_of_elementarizeClosed_of_progress (hE : ElementarizeClosed.{u})
    (hP : Progress.{u}) : SeifertRefinement.{u} := by
  suffices h : ∀ n, ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)), E.complexity = n →
        ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), (∀ R ∈ L, SeifertFactor R) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (finiteConnectedSum L).toClosedOrientedManifold Q.toClosedOrientedManifold) by
    intro P G
    obtain ⟨E⟩ := hE P G
    exact h _ P E rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q E hn
    subst hn
    by_cases hT : E.IsTerminalElementary
    · refine ⟨[Q], fun R hR => ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
      rw [List.mem_singleton.mp hR]
      exact hT.2
    rcases hP Q E hT with ⟨E', hE'⟩ | ⟨A, B, ⟨e⟩, hA, hB⟩
    · exact ih _ hE' Q E' rfl
    · obtain ⟨LA, hLA, ⟨eA⟩⟩ := exists_factors_of_elementaryBelow ih hA
      obtain ⟨LB, hLB, ⟨eB⟩⟩ := exists_factors_of_elementaryBelow ih hB
      obtain ⟨f⟩ := finiteConnectedSum_append LA LB
      obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph eA eB
      exact ⟨LA ++ LB, fun R hR => (List.mem_append.mp hR).elim (hLA R) (hLB R),
        ⟨(f.trans g).trans e⟩⟩

theorem seifertRefinement_of_elementarizeOnSubCollar_of_progress
    (hE : ElementarizeOnSubCollar.{u}) (hP : Progress.{u}) : SeifertRefinement.{u} :=
  seifertRefinement_of_elementarizeClosed_of_progress
    (elementarizeClosed_of_elementarizeOnSubCollar hE) hP

theorem seifertRefinement_of_elementarize_of_progress (hE : Elementarize.{u})
    (hP : Progress.{u}) : SeifertRefinement.{u} :=
  seifertRefinement_of_elementarizeClosed_of_progress (elementarizeClosed_of_elementarize hE) hP

theorem seifertRefinement_of_elementarizeClosed_of_moves (hE : ElementarizeClosed.{u})
    (hM : MoveMerge.{u}) (hS : MoveSplit.{u}) (hA : MoveAbsorb.{u}) (hT : MoveTerminal.{u}) :
    SeifertRefinement.{u} :=
  seifertRefinement_of_elementarizeClosed_of_progress hE (progress_of_moves hM hS hA hT)

end GC.Seifert
