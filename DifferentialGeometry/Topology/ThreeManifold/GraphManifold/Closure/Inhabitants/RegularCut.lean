import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierProductModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem

/-!
The actual two hemispheres of the sphere-circle product give a regular cut with one equator seam.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def standardRegularSystem :
    EmbeddedCutSystem (NoCuts.carrier sphereTwoTimesCircleLift) .withBoundary :=
  productCarrierEmbeddedPieces.toCutSystem

def standardRegularPiece (j : Fin standardRegularSystem.count) :
    PieceFold (NoCuts.carrier sphereTwoTimesCircleLift) where
  Piece := standardRegularSystem.Piece j
  topology := standardRegularSystem.topology j
  charts := standardRegularSystem.charts j
  manifold := standardRegularSystem.manifold j
  compact := standardRegularSystem.compact j
  hausdorff := standardRegularSystem.hausdorff j
  secondCountable := standardRegularSystem.secondCountable j
  connected := standardRegularSystem.connected j
  map := standardRegularSystem.map j
  smooth := standardRegularSystem.smooth j
  mfderiv_bijective := standardRegularSystem.mfderiv_bijective j

def standardRegularLift (c : Fin standardRegularSystem.seamCount) (b : Bool) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (standardRegularPiece (standardRegularSystem.side c b).1).Piece ∞ :=
  match b with
  | true => standardRegularSystem.collar _ (standardRegularSystem.side c true).2
  | false =>
    ((standardRegularSystem.matching c).prodCongr
      (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
        (standardRegularSystem.collar _ (standardRegularSystem.side c false).2)

theorem standardRegularLift_source (c : Fin standardRegularSystem.seamCount) (b : Bool) :
    (standardRegularLift c b).source = halfCollarSource := by
  cases b
  · ext p
    change (p ∈ univ ∧
      (standardRegularSystem.matching c p.1, p.2) ∈
        (standardRegularSystem.collar _ (standardRegularSystem.side c false).2).source) ↔ _
    rw [standardRegularSystem.collar_source]
    simp only [mem_univ, true_and]
    rfl
  · exact standardRegularSystem.collar_source _ _

theorem standardRegularLift_apply (c : Fin standardRegularSystem.seamCount) (b : Bool)
    (p : Torus × EuclideanHalfSpace 1) :
    standardRegularLift c b p = standardRegularSystem.collar _
      (standardRegularSystem.side c b).2
        (if b then p else (standardRegularSystem.matching c p.1, p.2)) := by
  cases b <;> rfl

def standardRegularCut :
    RegularCutData (NoCuts.carrier sphereTwoTimesCircleLift)
      (BoundaryTori.empty (NoCuts.carrier sphereTwoTimesCircleLift)) where
  count := standardRegularSystem.count
  count_pos := standardRegularSystem.count_pos
  piece := standardRegularPiece
  covers := standardRegularSystem.covers
  seamCount := standardRegularSystem.seamCount
  seam c := ⟨standardRegularSystem.seam c, standardRegularSystem.seam_source c,
    standardRegularSystem.seam_interior c⟩
  seam_disjoint := by
    intro c d hcd
    have h : c = d := by
      apply Fin.ext
      have hc : c.val < 1 := c.isLt
      have hd : d.val < 1 := d.isLt
      omega
    exact (hcd h).elim
  side c b := (standardRegularSystem.side c b).1
  lift := standardRegularLift
  lift_source := standardRegularLift_source
  lift_eq := by
    intro c b t s hs h1
    rw [standardRegularLift_apply]
    cases b
    · exact (standardRegularSystem.seam_pos c t s hs h1).symm
    · change standardRegularSystem.map _
        (standardRegularSystem.collar _ _ (t, halfPoint s hs)) =
          standardRegularSystem.seam c (t, -s)
      convert (standardRegularSystem.seam_neg c t (-s)
        (neg_nonpos.mpr hs) (by linarith )).symm using 1
      simp only [GC.Endpoint.halfPoint, neg_neg]
  externalOwner := Fin.elim0
  externalLift i := i.elim0
  externalLift_source i := i.elim0
  externalLift_eq i p hp := i.elim0
  boundary_exhausted := by
    intro j
    let instCharts : ChartedSpace CarrierModel.withBoundary.Space
        (standardRegularSystem.Piece j) := standardRegularSystem.charts j
    change CarrierModel.withBoundary.model.boundary (standardRegularSystem.Piece j) = _
    rw [standardRegularSystem.boundary_exhausted]
    ext q
    constructor
    · intro hq
      obtain ⟨l, t, rfl⟩ := mem_iUnion.mp hq
      obtain ⟨p, hp⟩ := standardRegularSystem.sides_bijective.2 ⟨j, l⟩
      rcases p with ⟨c, b⟩ | i
      · change standardRegularSystem.side c b = ⟨j, l⟩ at hp
        have hj : (standardRegularSystem.side c b).1 = j := congrArg Sigma.fst hp
        subst j
        have hl : (standardRegularSystem.side c b).2 = l := by
          exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2
        refine Or.inl ⟨c, b, if b then t else (standardRegularSystem.matching c).symm t,
          rfl, ?_⟩
        rw [standardRegularLift_apply, hl]
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
          Diffeomorph.apply_symm_apply] <;> rfl
      · exact i.elim0
    · rintro (⟨c, b, t, rfl, rfl⟩ | ⟨i, hrest⟩)
      · rw [standardRegularLift_apply]
        refine mem_iUnion.mpr ⟨(standardRegularSystem.side c b).2, ?_⟩
        cases b
        · exact mem_range_self (standardRegularSystem.matching c t)
        · exact mem_range_self t
      · exact i.elim0
  overlap := standardRegularSystem.overlap
  external_exhausted := by
    rw [BoundaryTori.empty_image]
    exact closedCarrier_boundary_eq_empty _
  external_seam_disjoint i c := i.elim0

theorem standardRegularCut_counts :
    standardRegularCut.count = 2 ∧ standardRegularCut.seamCount = 1 := ⟨rfl, rfl⟩

end GC.GraphManifold.Assembly
