import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStage
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalSelfSeam

/-!
# The actual two-piece restriction of an inner mixed seam

An inner seam has two non-frozen endpoint pieces. Restricting their cut carrier and gluing only
that seam gives an actual elementary local presentation without assigning product structures
to any unrelated frozen piece. Omitted seams remain actual external boundary sides, including
the two sides of a host self seam. Product certificates are transferred by the real selected
local piece diffeomorphisms and their full half-collar equations.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization
namespace MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

theorem sidePiece_pairSide (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    σ.toTorus.sidePiece (σ.toTorus.pairSide j b) = σ.seamPiece j b := by
  cases b <;> rfl

theorem mem_seamPair_iff (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (i : Fin σ.toTorus.components.count) :
    i ∈ σ.toTorus.seamPair j ↔ i = σ.seamPiece j b ∨ i = σ.hostPiece j b := by
  simp only [TorusPresentation.seamPair, Finset.mem_insert, Finset.mem_singleton]
  cases b
  · simp only [hostPiece, seamPiece, Bool.not_false]
    tauto
  · simp only [hostPiece, seamPiece, Bool.not_true]

theorem card_ownedSide_eq_kind (i : Fin σ.toTorus.components.count) (hi : i ∉ σ.frozen) :
    Fintype.card (σ.toTorus.OwnedSide i) = σ.kind i := (σ.piece i hi).card_ownedSide

theorem not_mem_frozen_of_mem_seamPair {j : Fin σ.toTorus.pairing.count}
    (hj : j ∉ σ.prot) {i : Fin σ.toTorus.components.count} (hi : i ∈ σ.toTorus.seamPair j) :
    i ∉ σ.frozen := by
  rcases σ.toTorus.eq_or_eq_of_mem_seamPair hi with rfl | rfl
  · exact σ.seamPiece_not_mem_frozen hj true
  · exact σ.seamPiece_not_mem_frozen hj false

theorem selectedInternal (j : Fin σ.toTorus.pairing.count) :
    ∀ k ∈ ({j} : Finset (Fin σ.toTorus.pairing.count)),
      σ.toTorus.leftPiece k ∈ σ.toTorus.seamPair j ∧
        σ.toTorus.rightPiece k ∈ σ.toTorus.seamPair j := by
  intro k hk
  have hk' : k = j := Finset.mem_singleton.mp hk
  subst k
  exact ⟨σ.toTorus.left_mem_seamPair j, σ.toTorus.right_mem_seamPair j⟩

abbrev selectedCarrier (j : Fin σ.toTorus.pairing.count) : CompactCarrier.{u} :=
  σ.toTorus.restrictAlongCarrier (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)

instance selectedCarrier_charts (j : Fin σ.toTorus.pairing.count) :
    ChartedSpace (EuclideanHalfSpace 3) (σ.selectedCarrier j).Carrier :=
  (σ.selectedCarrier j).charts

instance selectedCarrier_smooth (j : Fin σ.toTorus.pairing.count) :
    IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞ (σ.selectedCarrier j).Carrier :=
  (σ.selectedCarrier j).smooth

abbrev selectedTorus (j : Fin σ.toTorus.pairing.count) :
    TorusPresentation (σ.selectedCarrier j) :=
  σ.toTorus.selectedLocal_presentation (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    ⟨σ.toTorus.leftPiece j, σ.toTorus.left_mem_seamPair j⟩

def selectedElementary (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot) :
    ElementaryPresentation (σ.selectedCarrier j) where
  toTorus := σ.selectedTorus j
  kind i := σ.kind (σ.toTorus.subIndex (σ.toTorus.seamPair j) i)
  kind_mem i := σ.kind_mem _ (σ.not_mem_frozen_of_mem_seamPair hj
    (σ.toTorus.subIndex_mem (σ.toTorus.seamPair j) i))
  piece i := ((σ.piece (σ.toTorus.subIndex (σ.toTorus.seamPair j) i)
    (σ.not_mem_frozen_of_mem_seamPair hj
      (σ.toTorus.subIndex_mem (σ.toTorus.seamPair j) i))).transfer
        (σ.toTorus.selectedLocal_transfer (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)
          ⟨σ.toTorus.leftPiece j, σ.toTorus.left_mem_seamPair j⟩
          (σ.toTorus.subIndex_mem (σ.toTorus.seamPair j) i))).congrIndex
            (σ.toTorus.subIndexOf_subIndex (σ.toTorus.seamPair j) i)

@[simp]
theorem selectedElementary_toTorus (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot) :
    (σ.selectedElementary j hj).toTorus = σ.selectedTorus j := rfl

theorem selectedElementary_pairing_count (j : Fin σ.toTorus.pairing.count)
    (hj : j ∉ σ.prot) :
    (σ.selectedElementary j hj).toTorus.pairing.count = 1 := by
  change ({j} : Finset (Fin σ.toTorus.pairing.count)).card = 1
  exact Finset.card_singleton j

abbrev selectedIndex (j : Fin σ.toTorus.pairing.count) :
    Fin ({j} : Finset (Fin σ.toTorus.pairing.count)).card := ⟨0, by simp⟩

theorem selectedTorus_leftPiece (j : Fin σ.toTorus.pairing.count) :
    (σ.selectedTorus j).leftPiece (σ.selectedIndex j) =
      σ.toTorus.subIndexOf (σ.toTorus.seamPair j) (σ.toTorus.left_mem_seamPair j) := by
  have hj : (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).val = j :=
    Finset.mem_singleton.mp (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).property
  change σ.toTorus.restrictLeftPiece (σ.toTorus.seamPair j)
    (σ.toTorus.alongKeptIndex _ {j} (σ.selectedInternal j) (σ.selectedIndex j)) = _
  unfold TorusPresentation.restrictLeftPiece
  apply (σ.toTorus.subIndexOf_eq_iff _ _).mpr
  rw [σ.toTorus.keptSeam_alongKeptIndex, hj]

theorem selectedTorus_rightPiece (j : Fin σ.toTorus.pairing.count) :
    (σ.selectedTorus j).rightPiece (σ.selectedIndex j) =
      σ.toTorus.subIndexOf (σ.toTorus.seamPair j) (σ.toTorus.right_mem_seamPair j) := by
  have hj : (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).val = j :=
    Finset.mem_singleton.mp (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).property
  change σ.toTorus.restrictRightPiece (σ.toTorus.seamPair j)
    (σ.toTorus.alongKeptIndex _ {j} (σ.selectedInternal j) (σ.selectedIndex j)) = _
  unfold TorusPresentation.restrictRightPiece
  apply (σ.toTorus.subIndexOf_eq_iff _ _).mpr
  rw [σ.toTorus.keptSeam_alongKeptIndex, hj]

theorem selectedTorus_matching (j : Fin σ.toTorus.pairing.count) :
    (σ.selectedTorus j).pairing.matching (σ.selectedIndex j) =
      σ.toTorus.pairing.matching j := by
  have hj : (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).val = j :=
    Finset.mem_singleton.mp (σ.toTorus.alongSeam {j} (σ.selectedIndex j)).property
  change σ.toTorus.pairing.matching (σ.toTorus.keptSeam (σ.toTorus.seamPair j)
    (σ.toTorus.alongKeptIndex _ {j} (σ.selectedInternal j) (σ.selectedIndex j))).val = _
  rw [σ.toTorus.keptSeam_alongKeptIndex, hj]

theorem selectedElementary_seamPiece_kind (j : Fin σ.toTorus.pairing.count)
    (hj : j ∉ σ.prot) (b : Bool) :
    (σ.selectedElementary j hj).kind
      ((σ.selectedElementary j hj).seamPiece (σ.selectedIndex j) b) =
        σ.kind (σ.seamPiece j b) := by
  cases b
  · change σ.kind (σ.toTorus.subIndex (σ.toTorus.seamPair j)
      ((σ.selectedTorus j).rightPiece (σ.selectedIndex j))) = _
    rw [σ.selectedTorus_rightPiece, σ.toTorus.subIndex_subIndexOf]
    rfl
  · change σ.kind (σ.toTorus.subIndex (σ.toTorus.seamPair j)
      ((σ.selectedTorus j).leftPiece (σ.selectedIndex j))) = _
    rw [σ.selectedTorus_leftPiece, σ.toTorus.subIndex_subIndexOf]
    rfl

theorem selectedElementary_hostPiece_kind (j : Fin σ.toTorus.pairing.count)
    (hj : j ∉ σ.prot) (b : Bool) :
    (σ.selectedElementary j hj).kind
      ((σ.selectedElementary j hj).hostPiece (σ.selectedIndex j) b) =
        σ.kind (σ.hostPiece j b) := σ.selectedElementary_seamPiece_kind j hj !b

theorem selectedElementary_fillingDistance (j : Fin σ.toTorus.pairing.count)
    (hj : j ∉ σ.prot) (b : Bool) :
    (σ.selectedElementary j hj).fillingDistance (σ.selectedIndex j) b =
      σ.fillingDistance j b := by
  cases b <;> simp only [ElementaryPresentation.fillingDistance, fillingDistance,
    selectedElementary_toTorus, selectedTorus_matching]

theorem selectedElementary_isMergeSeam (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsMergeSeam j b) :
    (σ.selectedElementary j h.1).IsMergeSeam (σ.selectedIndex j) b := by
  simpa only [ElementaryPresentation.IsMergeSeam, selectedElementary_seamPiece_kind,
    selectedElementary_hostPiece_kind, selectedElementary_fillingDistance] using h.2

theorem selectedElementary_isAbsorbSeam (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsAbsorbSeam j b) :
    (σ.selectedElementary j h.1).IsAbsorbSeam (σ.selectedIndex j) b := by
  simpa only [ElementaryPresentation.IsAbsorbSeam, selectedElementary_seamPiece_kind,
    selectedElementary_hostPiece_kind] using h.2

def selectedRestrictDiffeomorph (j : Fin σ.toTorus.pairing.count)
    (hint : ∀ k, σ.toTorus.leftPiece k ∈ σ.toTorus.seamPair j →
      σ.toTorus.rightPiece k ∈ σ.toTorus.seamPair j → k = j) :
    (σ.selectedCarrier j).Carrier ≃ₘ⟮(σ.selectedCarrier j).model,
      (σ.toTorus.restrictCarrier (σ.toTorus.seamPair j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).model⟯
      (σ.toTorus.restrictCarrier (σ.toTorus.seamPair j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).Carrier := by
  let T := σ.toTorus
  let S := T.seamPair j
  let hext := TorusPresentation.externalPiece_not_mem_of_closed T S
  let : ChartedSpace (EuclideanHalfSpace 3) (T.restrictCarrier S hext).Carrier :=
    (T.restrictCarrier S hext).charts
  have hAll : ∀ k, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S →
      k ∈ ({j} : Finset (Fin T.pairing.count)) :=
    fun k hk => Finset.mem_singleton.mpr (hint k hk.1 hk.2)
  let e := T.restrictAlongHomeomorph_of_all S {j} (σ.selectedInternal j) hAll
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (T.contMDiff_restrictCarrier_iff S hext e).mpr
    exact T.contMDiff_restrictAlongMap S {j} (σ.selectedInternal j) hext
  · let : ChartedSpace (EuclideanHalfSpace 3) (Set.range (T.restrictMap S)) :=
      (T.restrictAtlas S hext).toChartedSpace
    have heq : T.restrictAlongMap S {j} (σ.selectedInternal j) ∘ e.symm = Subtype.val := by
      funext x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    have hs : ContMDiffOn (𝓡∂ 3) (NoCuts.carrier Q).model ∞
        (T.restrictAlongMap S {j} (σ.selectedInternal j) ∘ e.symm) Set.univ := by
      rw [heq]
      exact (T.contMDiff_restrictCarrier_val S hext).contMDiffOn
    exact contMDiffOn_univ.mp
      (T.contMDiffOn_restrictAlong_of_comp S {j} (σ.selectedInternal j) hext (𝓡∂ 3)
        (N := (T.restrictCarrier S hext).Carrier) e.symm Set.univ
        e.symm.continuous.continuousOn hs)

def selectedRegionDiffeomorph (j : Fin σ.toTorus.pairing.count)
    (hint : ∀ k, σ.toTorus.leftPiece k ∈ σ.toTorus.seamPair j →
      σ.toTorus.rightPiece k ∈ σ.toTorus.seamPair j → k = j) :
    (σ.toTorus.contractRegion (σ.toTorus.seamPair j)
      (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos j.pos)).Carrier
    ≃ₘ⟮σ.toTorus.cutCarrier.model, (σ.selectedCarrier j).model⟯
      (σ.selectedCarrier j).Carrier := by
  let T := σ.toTorus
  let S := T.seamPair j
  let hext := TorusPresentation.externalPiece_not_mem_of_closed T S
  let hk := T.cutCarrier_kind_of_pos j.pos
  let e := σ.selectedRestrictDiffeomorph j hint
  let d : (σ.selectedCarrier j).Carrier ≃ₘ⟮(σ.selectedCarrier j).model,
      T.cutCarrier.model⟯ (T.contractRegion S hext hk).Carrier :=
    { e.toHomeomorph with
      contMDiff_toFun := (recast_contMDiff_iff_right (T.restrictCarrier S hext)
        T.cutCarrier.kind hk.symm e).mpr e.contMDiff
      contMDiff_invFun := (recast_contMDiff_iff_left (T.restrictCarrier S hext)
        T.cutCarrier.kind hk.symm e.symm).mpr e.symm.contMDiff }
  exact d.symm

end MixedStage
end GC.Seifert.RelativeNormalization
