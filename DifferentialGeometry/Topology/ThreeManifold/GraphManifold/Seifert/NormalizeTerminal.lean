import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalPrimeThreeCone
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorbProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalProof

/-!
# The normalization with terminal raw witnesses

Chapter 5 plan P0 (survey X31 §4, review 19 §6–7). The skeleton of `Normalize.lean` keeps only
`SeifertFactor` at a terminal leaf (`ElementaryBelow`, `IsTerminalElementary`), which forgets the
raw presentation. Here every terminal leaf carries a `TerminalPresentation`: a raw presentation
and a factor proof of the same manifold. `TerminalBelow n A` strengthens `ElementaryBelow n A`:
`A` has a terminal presentation, or an elementary presentation of count `< n`.

`MoveSplitTerminalRaw` is the strengthened split move M2 of review 19 §6.2, without its `hT`
since `TorusMappingClassLinear` is proved: at a split seam `Q` is orientedly `A # B`, and each
summand has a terminal presentation or an elementary presentation of smaller count. It enters
only as a hypothesis; it implies `MoveSplit` (`moveSplit_of_moveSplitTerminalRaw`).

A move-free presentation `E` is terminal, with raw witness `E.toRaw` and factor proof from M4
`moveTerminal'` (`TerminalPresentation.ofMoveFree`). Otherwise M1 (`moveMerge'` applied to
`torusMappingClassLinear_holds`, the term of `moveMerge_unconditional`) or M3 `moveAbsorb`
lowers the count, or `MoveSplitTerminalRaw` splits; immediate terminal summands need no descent.
Strong induction on the count (`exists_terminals_of_elementary`) and concatenation of the lists
(`finiteConnectedSum_append`) give `normalize_of_moves`: a closed `M` with a raw presentation is
orientedly the connected sum of a list of manifolds with terminal presentations. Only the closed
form `ElementarizeClosed` of `hE` is used (`normalize_of_moves_of_elementarizeClosed`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.Seifert

open ElementaryPresentation

def MoveSplitTerminalRaw : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool), E.IsSplitSeam j b →
      ∃ A B : ConnectedClosedOrientedManifold.{u} 3,
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (connectedSum A B).toClosedOrientedManifold Q.toClosedOrientedManifold) ∧
        (Nonempty (TerminalPresentation A) ∨
          ∃ EA : ElementaryPresentation (NoCuts.carrier A), EA.complexity < E.complexity) ∧
        (Nonempty (TerminalPresentation B) ∨
          ∃ EB : ElementaryPresentation (NoCuts.carrier B), EB.complexity < E.complexity)

def TerminalBelow (n : ℕ) (A : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (TerminalPresentation A) ∨
    ∃ E : ElementaryPresentation (NoCuts.carrier A), E.complexity < n

theorem TerminalBelow.elementaryBelow {n : ℕ} {A : ConnectedClosedOrientedManifold.{u} 3}
    (h : TerminalBelow n A) : ElementaryBelow n A :=
  h.imp (fun ⟨T⟩ => T.factor) id

theorem moveSplit_of_moveSplitTerminalRaw (h : MoveSplitTerminalRaw.{u}) : MoveSplit.{u} := by
  intro Q E j b hs
  obtain ⟨A, B, e, hA, hB⟩ := h Q E j b hs
  exact ⟨A, B, e, TerminalBelow.elementaryBelow hA, TerminalBelow.elementaryBelow hB⟩

namespace TerminalPresentation

def ofMoveFree {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (h : E.IsMoveFree) :
    TerminalPresentation Q where
  raw := E.toRaw
  factor := moveTerminal' Q E h

@[simp]
theorem ofMoveFree_raw {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (h : E.IsMoveFree) :
    (ofMoveFree E h).raw = E.toRaw := rfl

end TerminalPresentation

private theorem exists_terminals_of_terminalBelow {n : ℕ}
    (ih : ∀ m < n, ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)), E.complexity = m →
        ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
          (∀ R ∈ L, Nonempty (TerminalPresentation R)) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (finiteConnectedSum L).toClosedOrientedManifold Q.toClosedOrientedManifold))
    {A : ConnectedClosedOrientedManifold.{u} 3} (hA : TerminalBelow n A) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ R ∈ L, Nonempty (TerminalPresentation R)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold A.toClosedOrientedManifold) := by
  rcases hA with hA | ⟨E, hE⟩
  · refine ⟨[A], fun R hR => ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
    rw [List.mem_singleton.mp hR]
    exact hA
  · exact ih _ hE A E rfl

theorem exists_terminals_of_elementary (hM2 : MoveSplitTerminalRaw.{u})
    (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q)) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ R ∈ L, Nonempty (TerminalPresentation R)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold Q.toClosedOrientedManifold) := by
  suffices h : ∀ n, ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (E : ElementaryPresentation (NoCuts.carrier Q)), E.complexity = n →
        ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
          (∀ R ∈ L, Nonempty (TerminalPresentation R)) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (finiteConnectedSum L).toClosedOrientedManifold Q.toClosedOrientedManifold) from
    h _ Q E rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q E hn
    subst hn
    by_cases hF : E.IsMoveFree
    · refine ⟨[Q], fun R hR => ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
      rw [List.mem_singleton.mp hR]
      exact ⟨TerminalPresentation.ofMoveFree E hF⟩
    have hR : ¬ ∀ j b, ¬ E.IsMergeSeam j b ∧ ¬ E.IsSplitSeam j b ∧ ¬ E.IsAbsorbSeam j b :=
      fun h => hF (E.isMoveFree_iff.2 h)
    simp only [not_forall] at hR
    obtain ⟨j, b, h⟩ := hR
    by_cases h1 : E.IsMergeSeam j b
    · obtain ⟨E', hE'⟩ := moveMerge' torusMappingClassLinear_holds Q E j b h1
      exact ih _ (by omega) Q E' rfl
    by_cases h2 : E.IsSplitSeam j b
    · obtain ⟨A, B, ⟨e⟩, hA, hB⟩ := hM2 Q E j b h2
      obtain ⟨LA, hLA, ⟨eA⟩⟩ := exists_terminals_of_terminalBelow ih hA
      obtain ⟨LB, hLB, ⟨eB⟩⟩ := exists_terminals_of_terminalBelow ih hB
      obtain ⟨f⟩ := finiteConnectedSum_append LA LB
      obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph eA eB
      exact ⟨LA ++ LB, fun R hR => (List.mem_append.mp hR).elim (hLA R) (hLB R),
        ⟨(f.trans g).trans e⟩⟩
    · obtain ⟨E', hE'⟩ := moveAbsorb Q E j b (not_not.1 fun h3 => h ⟨h1, h2, h3⟩)
      exact ih _ (by omega) Q E' rfl

theorem normalize_of_moves_of_elementarizeClosed (hM2 : MoveSplitTerminalRaw.{u})
    (hE : ElementarizeClosed.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ Q ∈ L, Nonempty (TerminalPresentation Q)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold) := by
  obtain ⟨E⟩ := hE M G
  exact exists_terminals_of_elementary hM2 M E

theorem normalize_of_moves (hM2 : MoveSplitTerminalRaw.{u}) (hE : ElementarizeOnSubCollar.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ Q ∈ L, Nonempty (TerminalPresentation Q)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold) :=
  normalize_of_moves_of_elementarizeClosed hM2
    (elementarizeClosed_of_elementarizeOnSubCollar hE) M G

end GC.Seifert
