import DifferentialGeometry.Topology.Attachment.Union
import DifferentialGeometry.Topology.Handle.Basic
import DifferentialGeometry.Topology.Handle.Defs
import DifferentialGeometry.Topology.Homotopy.ClosedCell
import DifferentialGeometry.Topology.Homotopy.EquivUnder
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology.Handle

universe u

open DifferentialGeometry.Topology.Homotopy
open ContinuousMap
open unitInterval

def coreProjectionAttachingMap (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) : AttachingRegion k l → X :=
  fun p => psi p.1

@[simp]
theorem coreProjectionAttachingMap_apply (k l : ℕ) {X : Type u} (psi : CellBoundary k → X)
    (s : CellBoundary k) (y : ClosedCell l) : coreProjectionAttachingMap k l psi (s, y) = psi s := by
  rfl

theorem continuous_coreProjectionAttachingMap {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (hpsi : Continuous psi) : Continuous (coreProjectionAttachingMap k l psi) := by
  change Continuous (fun p : AttachingRegion k l => psi (p.1 : CellBoundary k))
  exact hpsi.comp continuous_fst

private def collapseMap (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) :
    StandardHandle k l ⊕ X → CellAdjunctionSpace k psi :=
  Sum.elim (fun p : StandardHandle k l =>
    DifferentialGeometry.Topology.adjunctionCell (cellBoundaryInclusion k) psi p.1)
    (DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi)

private theorem collapseMap_rel (k l : ℕ) {X : Type u} (psi : CellBoundary k → X)
    (a b : StandardHandle k l ⊕ X)
    (h : DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k l) (coreProjectionAttachingMap k l psi) a b) :
    collapseMap k l psi a = collapseMap k l psi b := by
  rcases h with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    rcases x with ⟨s, y⟩
    change DifferentialGeometry.Topology.adjunctionCell (cellBoundaryInclusion k) psi
        (cellBoundaryInclusion k s) =
      DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi (psi s)
    exact DifferentialGeometry.Topology.adjunction_coherence (cellBoundaryInclusion k) psi s
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    rcases x with ⟨s, y⟩
    change DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi (psi s) =
      DifferentialGeometry.Topology.adjunctionCell (cellBoundaryInclusion k) psi
        (cellBoundaryInclusion k s)
    exact (DifferentialGeometry.Topology.adjunction_coherence (cellBoundaryInclusion k) psi s).symm

private def thickenMap (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) :
    ClosedCell k ⊕ X → AdjunctionSpace k l (coreProjectionAttachingMap k l psi) :=
  Sum.elim (fun x : ClosedCell k =>
    DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) (coreProjectionAttachingMap k l psi)
      (x, closedCellCenter l))
    (DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi))

private theorem thickenMap_rel (k l : ℕ) {X : Type u} (psi : CellBoundary k → X)
    (a b : ClosedCell k ⊕ X)
    (h : DifferentialGeometry.Topology.adjunctionRel (cellBoundaryInclusion k) psi a b) :
    thickenMap k l psi a = thickenMap k l psi b := by
  rcases h with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    change DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) (coreProjectionAttachingMap k l psi)
        (cellBoundaryInclusion k x, closedCellCenter l) =
      DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi)
        (psi x)
    exact DifferentialGeometry.Topology.adjunction_coherence (attachingInclusion k l)
      (coreProjectionAttachingMap k l psi) (x, closedCellCenter l)
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    change DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi)
        (psi x) =
      DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) (coreProjectionAttachingMap k l psi)
        (cellBoundaryInclusion k x, closedCellCenter l)
    exact (DifferentialGeometry.Topology.adjunction_coherence (attachingInclusion k l)
      (coreProjectionAttachingMap k l psi) (x, closedCellCenter l)).symm

noncomputable def collapse (k l : ℕ) {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) : C(AdjunctionSpace k l (coreProjectionAttachingMap k l psi), CellAdjunctionSpace k psi) :=
  ⟨Quot.lift (collapseMap k l psi) (collapseMap_rel k l psi),
    continuous_adjunction_lift (attachingInclusion k l) (coreProjectionAttachingMap k l psi) (collapseMap_rel k l psi)
      (by
        dsimp [collapseMap]
        refine Continuous.sumElim ?_ ?_
        · exact (continuous_adjunctionCell (cellBoundaryInclusion k) psi).comp continuous_fst
        · exact continuous_adjunctionLower (i := cellBoundaryInclusion k) psi)⟩

noncomputable def thicken (k l : ℕ) {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) : C(CellAdjunctionSpace k psi, AdjunctionSpace k l (coreProjectionAttachingMap k l psi)) :=
  ⟨Quot.lift (thickenMap k l psi) (thickenMap_rel k l psi),
    continuous_adjunction_lift (cellBoundaryInclusion k) psi (thickenMap_rel k l psi)
      (by
        dsimp [thickenMap]
        refine Continuous.sumElim ?_ ?_
        · exact (continuous_adjunctionCell (attachingInclusion k l) (coreProjectionAttachingMap k l psi)).comp
            (continuous_id.prodMk continuous_const)
        · exact continuous_adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi))⟩

theorem collapse_lower {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (x : X) :
    collapse k l psi (lower (coreProjectionAttachingMap k l psi) x) =
      DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi x := by
  rfl

theorem collapse_cell {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (p : StandardHandle k l) :
    collapse k l psi (cell (coreProjectionAttachingMap k l psi) p) =
      DifferentialGeometry.Topology.adjunctionCell (cellBoundaryInclusion k) psi p.1 := by
  rfl

theorem thicken_lower {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (x : X) :
    thicken k l psi (DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi x) =
      lower (coreProjectionAttachingMap k l psi) x := by
  rfl

theorem thicken_cell {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (x : ClosedCell k) :
    thicken k l psi (DifferentialGeometry.Topology.adjunctionCell (cellBoundaryInclusion k) psi x) =
      cell (coreProjectionAttachingMap k l psi) (x, closedCellCenter l) := by
  rfl

theorem collapse_comp_thicken {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) :
    (collapse k l psi).comp (thicken k l psi) = ContinuousMap.id (CellAdjunctionSpace k psi) := by
  apply ContinuousMap.ext
  refine Quot.ind ?_
  intro z
  cases z with
  | inl x =>
    simp [collapse, thicken, collapseMap, thickenMap, adjunctionCell, adjunctionMk]
  | inr x =>
    simp [collapse, thicken, collapseMap, thickenMap, adjunctionCell, adjunctionLower,
      adjunctionMk]

private def homotopyCellMap (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) :
    I × StandardHandle k l → AdjunctionSpace k l (coreProjectionAttachingMap k l psi) :=
  fun p => DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l)
    (coreProjectionAttachingMap k l psi) (p.2.1, radialStep l p.1 p.2.2)

private def homotopyLowerMap (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) :
    I × X → AdjunctionSpace k l (coreProjectionAttachingMap k l psi) :=
  fun p => DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l)
    (coreProjectionAttachingMap k l psi) p.2

private def homotopyRep (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) (t : I) :
    StandardHandle k l ⊕ X → AdjunctionSpace k l (coreProjectionAttachingMap k l psi) :=
  Sum.elim (fun q : StandardHandle k l => homotopyCellMap k l psi (t, q))
    (fun x : X => homotopyLowerMap k l psi (t, x))

private theorem homotopyRep_rel (k l : ℕ) {X : Type u} (psi : CellBoundary k → X) (t : I)
    (a b : StandardHandle k l ⊕ X)
    (h : DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k l)
      (coreProjectionAttachingMap k l psi) a b) :
    homotopyRep k l psi t a = homotopyRep k l psi t b := by
  rcases h with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    rcases x with ⟨s, y⟩
    simpa [homotopyRep, homotopyCellMap, homotopyLowerMap] using
      (DifferentialGeometry.Topology.adjunction_coherence (attachingInclusion k l)
        (coreProjectionAttachingMap k l psi) (s, radialStep l t y))
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    rcases x with ⟨s, y⟩
    simpa [homotopyRep, homotopyCellMap, homotopyLowerMap] using
      (DifferentialGeometry.Topology.adjunction_coherence (attachingInclusion k l)
        (coreProjectionAttachingMap k l psi) (s, radialStep l t y)).symm

noncomputable def thickenCollapseHomotopy (k l : ℕ) {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (AdjunctionSpace k l (coreProjectionAttachingMap k l psi)))
      ((thicken k l psi).comp (collapse k l psi))
      (Set.range (lower (coreProjectionAttachingMap k l psi))) where
  toHomotopy := {
    toContinuousMap := ⟨fun p : I × AdjunctionSpace k l (coreProjectionAttachingMap k l psi) =>
      Quot.lift (fun z : StandardHandle k l ⊕ X => homotopyRep k l psi p.1 z)
        (homotopyRep_rel k l psi p.1) p.2, by
          have hCell : Continuous (homotopyCellMap k l psi) := by
            dsimp [homotopyCellMap]
            exact (continuous_adjunctionCell (attachingInclusion k l) (coreProjectionAttachingMap k l psi)).comp
              ((continuous_fst.comp continuous_snd).prodMk
                ((continuous_radialStep l).comp (continuous_fst.prodMk
                  (continuous_snd.comp continuous_snd))))
          have hLower : Continuous (homotopyLowerMap k l psi) := by
            dsimp [homotopyLowerMap]
            exact (continuous_adjunctionLower (i := attachingInclusion k l)
              (coreProjectionAttachingMap k l psi)).comp continuous_snd
          have hf_eq : (fun p : I × (StandardHandle k l ⊕ X) => homotopyRep k l psi p.1 p.2) =
              (Sum.elim (homotopyCellMap k l psi) (homotopyLowerMap k l psi)) ∘
                (Homeomorph.prodSumDistrib (X := I) (Y := StandardHandle k l) (Z := X)) := by
            funext p
            rcases p with ⟨t, z⟩
            cases z with
            | inl q =>
              simp [homotopyRep, Homeomorph.prodSumDistrib, Homeomorph.sumProdDistrib,
                Homeomorph.prodComm, Homeomorph.sumCongr]
            | inr x =>
              simp [homotopyRep, Homeomorph.prodSumDistrib, Homeomorph.sumProdDistrib,
                Homeomorph.prodComm, Homeomorph.sumCongr]
          have hcont_f : Continuous
              (fun p : I × (StandardHandle k l ⊕ X) => homotopyRep k l psi p.1 p.2) := by
            rw [hf_eq]
            exact (Continuous.sumElim hCell hLower).comp
              (Homeomorph.prodSumDistrib (X := I) (Y := StandardHandle k l) (Z := X)).continuous
          exact (Topology.IsQuotientMap.continuous_lift_prod_right
            (isQuotientMap_quot_mk (r := DifferentialGeometry.Topology.adjunctionRel
              (attachingInclusion k l) (coreProjectionAttachingMap k l psi))) (Y := I)
            (g := fun p : I × AdjunctionSpace k l (coreProjectionAttachingMap k l psi) =>
              Quot.lift (fun z : StandardHandle k l ⊕ X => homotopyRep k l psi p.1 z)
                (homotopyRep_rel k l psi p.1) p.2) hcont_f)⟩
    map_zero_left := by
      apply Quot.ind
      intro z
      cases z with
      | inl p =>
        simp [homotopyRep, homotopyCellMap, radialStep_zero, adjunctionCell, adjunctionMk]
      | inr x =>
        simp [homotopyRep, homotopyLowerMap, adjunctionLower, adjunctionMk]
    map_one_left := by
      apply Quot.ind
      intro z
      cases z with
      | inl p =>
        simp [homotopyRep, homotopyCellMap, radialStep_one, collapse, thicken, collapseMap,
          thickenMap, adjunctionCell, adjunctionMk]
      | inr x =>
        simp [homotopyRep, homotopyLowerMap, collapse, thicken, collapseMap, thickenMap,
          adjunctionLower, adjunctionMk]
  }
  prop' := by
    intro t q hq
    rcases hq with ⟨x, rfl⟩
    change Quot.lift (fun z : StandardHandle k l ⊕ X => homotopyRep k l psi t z)
        (homotopyRep_rel k l psi t) (lower (coreProjectionAttachingMap k l psi) x) =
      lower (coreProjectionAttachingMap k l psi) x
    simp [homotopyRep, homotopyLowerMap, lower, adjunctionLower, adjunctionMk]

theorem thickenCollapseHomotopy_apply_cell {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (t : I) (p : StandardHandle k l) :
    thickenCollapseHomotopy k l psi (t, cell (coreProjectionAttachingMap k l psi) p) =
      cell (coreProjectionAttachingMap k l psi) (p.1, radialStep l t p.2) := by
  rfl

theorem thickenCollapseHomotopy_apply_lower {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) (t : I) (x : X) :
    thickenCollapseHomotopy k l psi (t, lower (coreProjectionAttachingMap k l psi) x) =
      lower (coreProjectionAttachingMap k l psi) x := by
  rfl

theorem collapse_comp_lower {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) :
    (collapse k l psi).comp ⟨lower (coreProjectionAttachingMap k l psi),
        continuous_adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi)⟩ =
      ⟨DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi,
        continuous_adjunctionLower (i := cellBoundaryInclusion k) psi⟩ := by
  apply ContinuousMap.ext
  intro x
  exact collapse_lower (k := k) (l := l) psi x

theorem thicken_comp_lower {k l : ℕ} {X : Type u} [TopologicalSpace X]
    (psi : CellBoundary k → X) :
    (thicken k l psi).comp
        ⟨DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi,
          continuous_adjunctionLower (i := cellBoundaryInclusion k) psi⟩ =
      ⟨lower (coreProjectionAttachingMap k l psi),
        continuous_adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi)⟩ := by
  apply ContinuousMap.ext
  intro x
  exact thicken_lower (k := k) (l := l) psi x

noncomputable def handleCellAdjunctionHomotopyEquivUnder (k l : ℕ) {X : Type u}
    [TopologicalSpace X] (psi : CellBoundary k → X) :
    HomotopyEquivUnder
      ⟨lower (coreProjectionAttachingMap k l psi),
        continuous_adjunctionLower (i := attachingInclusion k l) (coreProjectionAttachingMap k l psi)⟩
      ⟨DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k) psi,
        continuous_adjunctionLower (i := cellBoundaryInclusion k) psi⟩ where
  toFun := collapse k l psi
  invFun := thicken k l psi
  map_toBase := collapse_comp_lower psi
  map_fromBase := thicken_comp_lower psi
  left_inv := (thickenCollapseHomotopy k l psi).symm
  right_inv := by
    have h := collapse_comp_thicken (k := k) (l := l) psi
    exact (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (CellAdjunctionSpace k psi))
      (Set.range (DifferentialGeometry.Topology.adjunctionLower (i := cellBoundaryInclusion k)
        psi))).cast h.symm rfl

@[simp]
theorem handleCellAdjunctionHomotopyEquivUnder_toFun (k l : ℕ) {X : Type u}
    [TopologicalSpace X] (psi : CellBoundary k → X) :
    (handleCellAdjunctionHomotopyEquivUnder k l psi).toFun = collapse k l psi := rfl

@[simp]
theorem handleCellAdjunctionHomotopyEquivUnder_invFun (k l : ℕ) {X : Type u}
    [TopologicalSpace X] (psi : CellBoundary k → X) :
    (handleCellAdjunctionHomotopyEquivUnder k l psi).invFun = thicken k l psi := rfl

@[simp]
theorem handleCellAdjunctionHomotopyEquivUnder_left_inv (k l : ℕ) {X : Type u}
    [TopologicalSpace X] (psi : CellBoundary k → X) :
    (handleCellAdjunctionHomotopyEquivUnder k l psi).left_inv =
      (thickenCollapseHomotopy k l psi).symm := rfl

end DifferentialGeometry.Topology.Handle
