import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.VertexGroupInjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledGoodness
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Pushing closed pieces into their interiors

Finite disjoint boundary collars provide a jointly continuous inward deformation.
The compact half-height strips control its support and the basepoint track stays interior.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology.Manifold Set Topology
open scoped ContinuousMap unitInterval

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

def pieceInteriorToPiece (i : Fin G.components.count) :
    C(G.cutCarrier.pieceInterior (G.components.piece i), G.components.piece i) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk (fun x => x.2.1)⟩

private def collarHeightPush (t : unitInterval) (s : EuclideanHalfSpace 1) :
    EuclideanHalfSpace 1 :=
  halfSpaceOneHomeomorph.symm
    ⟨max (s.val 0) ((t : ℝ) / 4), s.property.trans (le_max_left _ _)⟩

private theorem collarHeightPush_coordinate (t : unitInterval) (s : EuclideanHalfSpace 1) :
    (collarHeightPush t s).val 0 = max (s.val 0) ((t : ℝ) / 4) := by
  exact congrArg Subtype.val
    (halfSpaceOneHomeomorph.apply_symm_apply
      ⟨max (s.val 0) ((t : ℝ) / 4), s.property.trans (le_max_left _ _)⟩)

private theorem continuous_collarHeightPush :
    Continuous (fun p : unitInterval × EuclideanHalfSpace 1 => collarHeightPush p.1 p.2) := by
  apply halfSpaceOneHomeomorph.symm.continuous.comp
  apply Continuous.subtype_mk
  exact (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd).sup
    ((continuous_subtype_val.comp continuous_fst).div_const 4)

private theorem collarHeightPush_fixed (t : unitInterval) (s : EuclideanHalfSpace 1)
    (hs : 1 / 2 ≤ s.val 0) : collarHeightPush t s = s := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change (collarHeightPush t s).val 0 = s.val 0
  rw [collarHeightPush_coordinate]
  apply max_eq_left
  have ht := t.property.2
  linarith

private theorem collarHeightPush_source (t : unitInterval)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    (p.1, collarHeightPush t p.2) ∈ halfCollarSource := by
  change (collarHeightPush t p.2).val 0 < 1
  rw [collarHeightPush_coordinate]
  apply max_lt hp
  have ht := t.property.2
  linarith

private def collarPush {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)
    (t : unitInterval) (x : C.Carrier) : C.Carrier := by
  classical
  exact if h : ∃ j, x ∈ (T.collar j).target then
    let j := h.choose
    let p := (T.collar j).symm x
    T.collar j (p.1, collarHeightPush t p.2)
  else x

private theorem collarPush_formula {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) (t : unitInterval) (j : Fin n) (x : C.Carrier)
    (hx : x ∈ (T.collar j).target) :
    collarPush T t x = T.collar j
      (((T.collar j).symm x).1, collarHeightPush t ((T.collar j).symm x).2) := by
  classical
  have hex : ∃ k, x ∈ (T.collar k).target := ⟨j, hx⟩
  have hj : hex.choose = j := by
    by_contra hne
    exact (T.disjoint hne).le_bot ⟨hex.choose_spec, hx⟩
  simp only [collarPush, dite_eq_left hex, hj]

private theorem continuous_collarPush {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) :
    Continuous (fun p : unitInterval × C.Carrier => collarPush T p.1 p.2) := by
  classical
  let K : Set C.Carrier := ⋃ j, T.collar j ''
    {q : Torus × EuclideanHalfSpace 1 | q.2.val 0 ≤ 1 / 2}
  have hs (j : Fin n) :
      {q : Torus × EuclideanHalfSpace 1 | q.2.val 0 ≤ 1 / 2} ⊆
        (T.collar j).source := by
    intro q hq
    rw [T.source_eq j]
    change q.2.val 0 < 1
    change q.2.val 0 ≤ 1 / 2 at hq
    linarith
  have hK : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro j
    exact (isCompact_halfCollar_half.image_of_continuousOn
      ((T.collar j).toOpenPartialHomeomorph.continuousOn.mono (hs j))).isClosed
  have hfix (t : unitInterval) (x : C.Carrier) (hx : x ∉ K) : collarPush T t x = x := by
    by_cases hex : ∃ j, x ∈ (T.collar j).target
    · obtain ⟨j, hj⟩ := hex
      rw [collarPush_formula T t j x hj]
      have hp : 1 / 2 ≤ ((T.collar j).symm x).2.val 0 := by
        by_contra h
        apply hx
        exact mem_iUnion.mpr ⟨j, (T.collar j).symm x,
          (lt_of_not_ge h).le, (T.collar j).right_inv hj⟩
      rw [collarHeightPush_fixed t _ hp]
      exact (T.collar j).right_inv hj
    · simp only [collarPush, dite_eq_right hex]
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2 ∈ K
  · obtain ⟨j, q, hq, heq⟩ := mem_iUnion.mp hp
    have hx : p.2 ∈ (T.collar j).target := heq ▸ (T.collar j).map_source' (hs j hq)
    let U : Set (unitInterval × C.Carrier) := Prod.snd ⁻¹' (T.collar j).target
    have hU : IsOpen U := (T.collar j).open_target.preimage continuous_snd
    have hinv : ContinuousOn (fun z : unitInterval × C.Carrier =>
        (T.collar j).symm z.2) U :=
      (T.collar j).toOpenPartialHomeomorph.continuousOn_symm.comp continuous_snd.continuousOn
        (fun z hz => hz)
    let F : unitInterval × C.Carrier → C.Carrier := fun z =>
      T.collar j (((T.collar j).symm z.2).1,
        collarHeightPush z.1 ((T.collar j).symm z.2).2)
    have hF : ContinuousOn F U := by
      apply (T.collar j).toOpenPartialHomeomorph.continuousOn.comp
        (hinv.fst.prodMk (continuous_collarHeightPush.continuousOn.comp
          (continuous_fst.continuousOn.prodMk hinv.snd) (fun z hz => mem_univ _)))
      intro z hz
      change (((T.collar j).symm z.2).1,
        collarHeightPush z.1 ((T.collar j).symm z.2).2) ∈ (T.collar j).source
      rw [T.source_eq j]
      apply collarHeightPush_source
      rw [← T.source_eq j]
      exact (T.collar j).map_target' hz
    apply ((hF p hx).continuousAt (hU.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with z hz
    exact collarPush_formula T z.1 j z.2 hz
  · apply continuous_snd.continuousAt.congr_of_eventuallyEq
    filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hp] with z hz
    exact hfix z.1 z.2 hz

private theorem collarHeightPush_zero (s : EuclideanHalfSpace 1) :
    collarHeightPush 0 s = s := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change (collarHeightPush 0 s).val 0 = s.val 0
  rw [collarHeightPush_coordinate]
  simpa using max_eq_left s.property

private theorem collarPush_zero {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) (x : C.Carrier) : collarPush T 0 x = x := by
  classical
  by_cases hex : ∃ j, x ∈ (T.collar j).target
  · obtain ⟨j, hj⟩ := hex
    rw [collarPush_formula T 0 j x hj, collarHeightPush_zero]
    exact (T.collar j).right_inv hj
  · simp only [collarPush, dite_eq_right hex]

private theorem collarPush_interior {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) (hb : C.model.boundary C.Carrier = T.image)
    (t : unitInterval) (x : C.Carrier)
    (h : C.model.IsInteriorPoint x ∨ 0 < (t : ℝ)) :
    C.model.IsInteriorPoint (collarPush T t x) := by
  classical
  apply (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mpr
  intro hboundary
  have himage : collarPush T t x ∈ T.image := hb ▸ hboundary
  obtain ⟨k, a, heq⟩ := mem_iUnion.mp himage
  have hk : (a, halfZero) ∈ (T.collar k).source := by
    rw [T.source_eq k]
    exact zero_mem_halfCollarSource a
  have hkt : collarPush T t x ∈ (T.collar k).target :=
    heq ▸ (T.collar k).map_source' hk
  by_cases hex : ∃ j, x ∈ (T.collar j).target
  · obtain ⟨j, hj⟩ := hex
    let p := (T.collar j).symm x
    have hp : p ∈ (T.collar j).source := (T.collar j).map_target' hj
    have hp' : (p.1, collarHeightPush t p.2) ∈ (T.collar j).source := by
      rw [T.source_eq j] at hp ⊢
      exact collarHeightPush_source t p hp
    have hformula := collarPush_formula T t j x hj
    have hjt : collarPush T t x ∈ (T.collar j).target :=
      hformula ▸ (T.collar j).map_source' hp'
    have hkj : k = j := by
      by_contra hne
      exact (T.disjoint hne).le_bot ⟨hkt, hjt⟩
    subst k
    have he : (a, halfZero) = (p.1, collarHeightPush t p.2) :=
      (T.collar j).toOpenPartialHomeomorph.injOn hk hp' (heq.trans hformula)
    have hz : max (p.2.val 0) ((t : ℝ) / 4) = 0 := by
      have heh := congrArg (fun q : Torus × EuclideanHalfSpace 1 => q.2.val 0) he
      simpa only [collarHeightPush_coordinate, halfZero, GC.Endpoint.halfPoint] using heh.symm
    rcases h with hx | ht
    · have hle : p.2.val 0 ≤ 0 := by
        have hm := le_max_left (p.2.val 0) ((t : ℝ) / 4)
        rw [hz] at hm
        exact hm
      have hpz : p.2.val 0 = 0 := le_antisymm hle p.2.property
      have hpzero : p.2 = halfZero := (halfPoint_eq p.2 0 le_rfl hpz.symm).symm
      have hxb : C.model.IsBoundaryPoint x := by
        have hzboundary := T.boundary_zero j p.1
        rw [← hpzero] at hzboundary
        exact (T.collar j).right_inv hj ▸ hzboundary
      exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hxb
    · have hle : (t : ℝ) / 4 ≤ 0 := by
        have hm := le_max_right (p.2.val 0) ((t : ℝ) / 4)
        rw [hz] at hm
        exact hm
      linarith
  · have hfixed : collarPush T t x = x := by
      simp only [collarPush, dite_eq_right hex]
    have hx : x ∈ (T.collar k).target := hfixed ▸ hkt
    exact hex ⟨k, hx⟩

def pieceInwardPush (i : Fin G.components.count) :
    C(unitInterval × G.components.piece i, G.components.piece i) :=
  ⟨fun p => collarPush (G.pieceBoundaryTori i) p.1 p.2,
    continuous_collarPush (G.pieceBoundaryTori i)⟩

theorem pieceInwardPush_zero (i : Fin G.components.count) (x : G.components.piece i) :
    G.pieceInwardPush i (0, x) = x :=
  collarPush_zero (G.pieceBoundaryTori i) x

theorem pieceInwardPush_interior (i : Fin G.components.count) (t : unitInterval)
    (x : G.components.piece i)
    (h : G.cutCarrier.model.IsInteriorPoint x.val ∨ 0 < (t : ℝ)) :
    G.cutCarrier.model.IsInteriorPoint (G.pieceInwardPush i (t, x)).val := by
  apply (G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val (u := G.components.piece i)).mp
  apply collarPush_interior (G.pieceBoundaryTori i) (G.pieceBoundaryTori_image i)
  rcases h with hx | ht
  · exact Or.inl ((G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val
      (u := G.components.piece i)).mpr hx)
  · exact Or.inr ht

def pieceInwardEndpoint (i : Fin G.components.count) :
    C(G.components.piece i, G.cutCarrier.pieceInterior (G.components.piece i)) :=
  ⟨fun x => ⟨(G.pieceInwardPush i (1, x)).val,
    (G.pieceInwardPush i (1, x)).property,
    G.pieceInwardPush_interior i 1 x (Or.inr zero_lt_one)⟩,
    (continuous_subtype_val.comp ((G.pieceInwardPush i).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk
        (fun x => ⟨(G.pieceInwardPush i (1, x)).property,
          G.pieceInwardPush_interior i 1 x (Or.inr zero_lt_one)⟩)⟩

def pieceInwardHomotopy (i : Fin G.components.count) :
    (ContinuousMap.id (G.components.piece i)).Homotopy
      ((G.pieceInteriorToPiece i).comp (G.pieceInwardEndpoint i)) where
  toContinuousMap := G.pieceInwardPush i
  map_zero_left := G.pieceInwardPush_zero i
  map_one_left x := Subtype.ext (rfl : (G.pieceInwardPush i (1, x)).val =
    ((G.pieceInteriorToPiece i).comp (G.pieceInwardEndpoint i) x).val)

def pieceInwardInteriorHomotopy (i : Fin G.components.count) :
    (ContinuousMap.id (G.cutCarrier.pieceInterior (G.components.piece i))).Homotopy
      ((G.pieceInwardEndpoint i).comp (G.pieceInteriorToPiece i)) where
  toContinuousMap :=
    ⟨fun p => ⟨(G.pieceInwardPush i (p.1, G.pieceInteriorToPiece i p.2)).val,
      (G.pieceInwardPush i (p.1, G.pieceInteriorToPiece i p.2)).property,
      G.pieceInwardPush_interior i p.1 (G.pieceInteriorToPiece i p.2) (Or.inl p.2.property.2)⟩,
      (continuous_subtype_val.comp ((G.pieceInwardPush i).continuous.comp
        (continuous_fst.prodMk ((G.pieceInteriorToPiece i).continuous.comp
          continuous_snd)))).subtype_mk (fun p =>
            ⟨(G.pieceInwardPush i (p.1, G.pieceInteriorToPiece i p.2)).property,
              G.pieceInwardPush_interior i p.1 (G.pieceInteriorToPiece i p.2)
                (Or.inl p.2.property.2)⟩)⟩
  map_zero_left x := by
    apply Subtype.ext
    change (G.pieceInwardPush i (0, G.pieceInteriorToPiece i x)).val = x.val
    exact congrArg Subtype.val (G.pieceInwardPush_zero i (G.pieceInteriorToPiece i x))
  map_one_left x := rfl

def pieceInteriorHomotopyEquiv (i : Fin G.components.count) :
    G.cutCarrier.pieceInterior (G.components.piece i) ≃ₕ G.components.piece i where
  toFun := G.pieceInteriorToPiece i
  invFun := G.pieceInwardEndpoint i
  left_inv := ⟨(G.pieceInwardInteriorHomotopy i).symm⟩
  right_inv := ⟨(G.pieceInwardHomotopy i).symm⟩

theorem surjective_pieceInteriorToPiece (i : Fin G.components.count)
    (y : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Surjective (FundamentalGroup.map (G.pieceInteriorToPiece i) y) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv (G.pieceInteriorHomotopyEquiv i)
  change Function.Surjective (E.functor.map :
    (FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk y) →
      (E.functor.obj (FundamentalGroupoid.mk y) ⟶
        E.functor.obj (FundamentalGroupoid.mk y)))
  exact (E.fullyFaithfulFunctor.map_bijective _ _).surjective

end GC.Seifert.TorusPresentation
