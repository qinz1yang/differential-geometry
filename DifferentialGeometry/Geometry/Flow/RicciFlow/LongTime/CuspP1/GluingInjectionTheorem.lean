import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.GluingInjectionMain

/-!
# CP1-C: finite collared gluing injection (pieces into the glued manifold)

Blueprint `master207B.tex` B:11098-11186 (finite collared gluing lemma). For a closed torus
presentation `G` (no external ports) whose port maps are `π₁`-injective into their pieces
(`pieceBoundaryTori … incompressible`), every path component of `cutOpen ∅` (the interior of a
piece, i.e. the blueprint's shrunken core) includes `π₁`-injectively into `W`
(`injective_pieceComponent_CPC`), and so does `cutOpen ∅` itself at every basepoint
(`injective_pieceInterior_incl_CPC`).

Route: the `π₁`-injective van Kampen induction over the seams of `MultiSeamInjective.lean`
(`SeamLevelsInj`), with the general-loop one-seam step `step_CPC` in place of the torus-only
`injInto_insert`. The amalgam/HNN algebra is the tree's own (`Monoid.PushoutI.of_injective`,
`HNNExtension.of_injective` inside `Gluing`/`GluingHNN`); no new algebraic input.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.LongTime.CuspP1
open GC.Seifert

attribute [local instance] TorusPresentation.locallyPathConnectedSpace_carrier

section Final
variable {W : CompactCarrier.{u}} {G : TorusPresentation W}

theorem seamLevelsInj_all_CPC (h0 : G.SeamLevelsInj ∅) (K : Finset (Fin G.pairing.count)) :
    G.SeamLevelsInj K := by
  induction K using Finset.induction_on with
  | empty => exact h0
  | insert j K hj ih =>
    exact fun k => ⟨TorusPresentation.injInto_insert hj ih _ (ih k).1,
      TorusPresentation.injInto_insert hj ih _ (ih k).2⟩

theorem cutOpen_empty_subset_CPC (K : Finset (Fin G.pairing.count)) :
    G.cutOpen ∅ ⊆ G.cutOpen K := fun _ hy =>
  G.mem_cutOpen.mpr fun k _ => G.mem_cutOpen.mp hy k (Finset.notMem_empty k)

theorem injective_component_inclusion_CPC {M : Type u} [TopologicalSpace M]
    [LocallyPathConnectedSpace M] {O : Set M} (hO : IsOpen O) (x : M) (hx : x ∈ O)
    (h : pathComponentIn O x ⊆ O) :
    Function.Injective (FundamentalGroup.map (inclusionMap h) ⟨x, mem_pathComponentIn_self hx⟩) := by
  refine injective_inclusion_of_isClopen h ?_ _
  refine isClopen_preimage_of_cover (D := O \ pathComponentIn O x) (hO.pathComponentIn x)
    (isOpen_diff_pathComponentIn hO x) (fun y hy => ?_) ?_
  · by_cases hm : y ∈ pathComponentIn O x
    · exact Or.inl hm
    · exact Or.inr ⟨hy, hm⟩
  · rw [Set.disjoint_left]
    exact fun y hy hy' => hy'.2 hy

theorem injective_pieceComponent_aux_CPC (h0 : G.SeamLevelsInj ∅) (x : W.Carrier)
    (hx : x ∈ G.cutOpen ∅) (K : Finset (Fin G.pairing.count))
    (h : pathComponentIn (G.cutOpen ∅) x ⊆ G.cutOpen K) :
    Function.Injective (FundamentalGroup.map (inclusionMap h)
      ⟨x, mem_pathComponentIn_self hx⟩) := by
  induction K using Finset.induction_on with
  | empty => exact injective_component_inclusion_CPC (G.isOpen_cutOpen ∅) x hx h
  | insert j K hj ih =>
    have hKx : x ∈ G.cutOpen K := cutOpen_empty_subset_CPC K hx
    have hD0 : pathComponentIn (G.cutOpen ∅) x ⊆ pathComponentIn (G.cutOpen K) x :=
      (isPathConnected_pathComponentIn hx).subset_pathComponentIn (mem_pathComponentIn_self hx)
        ((pathComponentIn_subset).trans (cutOpen_empty_subset_CPC K))
    have hD0K : pathComponentIn (G.cutOpen ∅) x ⊆ G.cutOpen K :=
      hD0.trans pathComponentIn_subset
    have h1 := injective_inner_inclusion_CPC hD0 (pathComponentIn_subset : pathComponentIn
      (G.cutOpen K) x ⊆ G.cutOpen K) ⟨x, mem_pathComponentIn_self hx⟩ (ih hD0K)
    have h2 := step_CPC hj (seamLevelsInj_all_CPC h0 K) x hKx
    exact injective_inclusion_trans_CPC hD0 _ ⟨x, mem_pathComponentIn_self hx⟩ h1 h2

theorem injective_subsetToAmbient_of_eq_univ_CPC {M : Type u} [TopologicalSpace M] {S S' : Set M}
    (hS : S ⊆ S') (hu : S' = Set.univ) (x : S)
    (h : Function.Injective (FundamentalGroup.map (inclusionMap hS) x)) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient S) x) := by
  subst hu
  have hr : Function.Injective (FundamentalGroup.map
      (subsetToAmbient (Set.univ : Set M)) (inclusionMap hS x)) :=
    injective_fundamentalGroup_map_of_leftInverse (subsetToAmbient (Set.univ : Set M))
      (⟨fun y => ⟨y, trivial⟩, continuous_id.subtype_mk _⟩ : C(M, (Set.univ : Set M)))
      (fun z => Subtype.ext rfl) _
  have := hr.comp h
  rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at this
  exact this

/-- Finite collared gluing injection, component form: each path component of
`cutOpen ∅` (a piece interior) is `π₁`-injective into `W`. -/
theorem injective_pieceComponent_CPC (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (x : G.cutOpen ∅) :
    Function.Injective (FundamentalGroup.map
      (subsetToAmbient (pathComponentIn (G.cutOpen ∅) (x : W.Carrier)))
      ⟨x, mem_pathComponentIn_self x.2⟩) := by
  have h0 := G.seamLevelsInj_empty hext hports
  have h := injective_pieceComponent_aux_CPC h0 (x : W.Carrier) x.2 Finset.univ
    (pathComponentIn_subset.trans (cutOpen_empty_subset_CPC Finset.univ))
  exact injective_subsetToAmbient_of_eq_univ_CPC _ G.cutOpen_univ _ h

/-- Finite collared gluing injection (blueprint B:11098-11186), frozen form: the interior of
the cut pieces, `cutOpen ∅ = W ∖ ⋃ seams`, is `π₁`-injective into `W` at every basepoint,
provided every port map is `π₁`-injective into its piece. -/
theorem injective_pieceInterior_incl_CPC (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (x : G.cutOpen ∅) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient (G.cutOpen ∅)) x) := by
  have hcomp := injective_pieceComponent_CPC hext hports x
  have hcl : IsClopen (Subtype.val ⁻¹' pathComponentIn (G.cutOpen ∅) (x : W.Carrier) :
      Set (G.cutOpen ∅)) := by
    refine isClopen_preimage_of_cover (D := G.cutOpen ∅ \ pathComponentIn (G.cutOpen ∅) x)
      ((G.isOpen_cutOpen ∅).pathComponentIn _)
      (isOpen_diff_pathComponentIn (G.isOpen_cutOpen ∅) _) (fun y hy => ?_) ?_
    · by_cases hm : y ∈ pathComponentIn (G.cutOpen ∅) (x : W.Carrier)
      · exact Or.inl hm
      · exact Or.inr ⟨hy, hm⟩
    · rw [Set.disjoint_left]
      exact fun y hy hy' => hy'.2 hy
  set x' : pathComponentIn (G.cutOpen ∅) (x : W.Carrier) := ⟨x, mem_pathComponentIn_self x.2⟩
  have hsurj : Function.Surjective (FundamentalGroup.map
      (inclusionMap (pathComponentIn_subset : pathComponentIn (G.cutOpen ∅) (x : W.Carrier) ⊆
        G.cutOpen ∅)) x') := by
    refine surjective_fundamentalGroup_map_of_clopen _
      (clopenRetraction _ _ hcl x') (fun z => Subtype.ext
        (clopenRetraction_apply_of_mem _ _ hcl x' _ z.2)) _ hcl
      (fun y hy => Subtype.ext (clopenRetraction_apply_of_mem _ _ hcl x' _ hy)) x' x'.2
  have := injective_fundamentalGroup_map_of_comp _ (subsetToAmbient (G.cutOpen ∅)) x' hsurj
    hcomp
  exact this

end Final

end GC.LongTime.CuspP1
