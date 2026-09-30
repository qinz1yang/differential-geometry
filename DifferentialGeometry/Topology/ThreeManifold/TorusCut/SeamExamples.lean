import DifferentialGeometry.Topology.ThreeManifold.TorusCut.MarkedSeams
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
namespace GC.Topology
noncomputable section
open scoped ContinuousMap

abbrev ExampleSide := Fin 2 × Bool

def twoLoopSides : PairedSides ExampleSide where
  mate s := (s.1, !s.2)
  involutive s := by simp
  no_fixed s := by
    intro h
    have hb := congrArg Prod.snd h
    cases s.2 <;> simp at hb

theorem two_descriptions_one_seam (i : Fin 2) :
    twoLoopSides.seam (i, false) = twoLoopSides.seam (i, true) :=
  (twoLoopSides.seam_eq_iff _ _).2 (Or.inr rfl)

theorem repeated_torus_types_keep_labels :
    twoLoopSides.seam (0, false) ≠ twoLoopSides.seam (1, false) := by
  intro h
  rcases (twoLoopSides.seam_eq_iff _ _).1 h with h | h
  · exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)
  · exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)

def oneCarrier (_ : ExampleSide) : Unit := ()

theorem loops_are_not_fixed_sides (s : ExampleSide) :
    oneCarrier (twoLoopSides.mate s) = oneCarrier s ∧ twoLoopSides.mate s ≠ s :=
  ⟨rfl, twoLoopSides.no_fixed s⟩

def swapTorus : Torus ≃ₜ Torus := Homeomorph.prodComm Circle Circle

def exampleSideMap (s : ExampleSide) : C(Torus, TorusCylinder) :=
  if s.2 then (torusAt (s.1.val : ℝ)).comp (⟨swapTorus, swapTorus.continuous⟩ : C(Torus, Torus))
  else torusAt (s.1.val : ℝ)

def examplePairing (_ : ExampleSide) : Torus ≃ Torus := swapTorus.toEquiv

theorem example_pairing_commutes (s : ExampleSide) (x : Torus) :
    exampleSideMap (twoLoopSides.mate s) (examplePairing s x) = exampleSideMap s x := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

def actualSeamImage := twoLoopSides.seamImage
  (fun s => exampleSideMap s) examplePairing example_pairing_commutes

theorem actual_seam_image (i : Fin 2) :
    actualSeamImage (twoLoopSides.seam (i, false)) = Set.range (torusAt (i.val : ℝ)) := rfl

theorem actual_seams_disjoint :
    Disjoint (actualSeamImage (twoLoopSides.seam (0, false)))
      (actualSeamImage (twoLoopSides.seam (1, false))) := by
  rw [actual_seam_image, actual_seam_image]
  simpa using torus_two_sides_disjoint 0 1 zero_ne_one

theorem both_side_maps_piOne_injective (s : ExampleSide) (p : Torus) :
    Function.Injective (FundamentalGroup.map (exampleSideMap s) p) := by
  apply DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse
    (exampleSideMap s)
    (if s.2 then (⟨swapTorus.symm, swapTorus.symm.continuous⟩ : C(Torus, Torus)).comp ContinuousMap.fst else ContinuousMap.fst)
  intro x
  rcases s with ⟨i, b⟩
  cases b <;> rfl

theorem tagged_torus_maps_transport (x : Σ _ : Fin 2, Fin 1) :
    (fun z : (Σ _ : Fin 2, Fin 1) => torusAt (z.1.val : ℝ))
      ((reindex (J := fun _ : Fin 2 => Fin 1) (J' := fun _ : Fin 2 => Fin 1) (Equiv.swap (0 : Fin 2) 1) (fun _ => Equiv.refl (Fin 1))).symm
        (reindex (J := fun _ : Fin 2 => Fin 1) (J' := fun _ : Fin 2 => Fin 1) (Equiv.swap (0 : Fin 2) 1) (fun _ => Equiv.refl (Fin 1)) x)) =
      torusAt (x.1.val : ℝ) :=
  reindex_payload (J := fun _ : Fin 2 => Fin 1) (J' := fun _ : Fin 2 => Fin 1) _ _ (fun z => torusAt (z.1.val : ℝ)) x

end
end GC.Topology
