import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Interfaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MultiSeamInjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryFlat

/-!
# Geometric decompositions from good Seifert blocks

Boundary incompressibility is reindexed through the ports. Interior geometries transport through
component and unfilled-block diffeomorphisms, without metric matching along seam tori.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

namespace BlockedPresentation

variable {W : CompactCarrier.{u}}

theorem pieceBoundaryTori_incompressible_of_isGood (B : BlockedPresentation W)
    (hB : B.IsGood) (i : Fin B.base.components.count) :
    (B.base.pieceBoundaryTori i).incompressible := by
  intro j x
  let r := (B.port i).symm ((Fintype.equivFin (B.base.OwnedSide i)).symm j)
  have he : Fintype.equivFin (B.base.OwnedSide i) (B.port i r) = j := by
    simp [r]
  have hm := B.torusMap_eq i r
  rw [he] at hm
  have hb : (B.block i).presentation.external.boundaryMap r =
      (B.base.pieceBoundaryTori i).boundaryMap j := ContinuousMap.ext (congrFun hm)
  rw [← hb]
  exact hB i r x

theorem incompressible_of_isGood {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood) :
    B.base.toTorusDecomposition.reconstructionAtlas.Incompressible
      B.base.toTorusDecomposition.reconstruction :=
  B.base.incompressible_toTorusDecomposition_of_ports
    (B.pieceBoundaryTori_incompressible_of_isGood hB)

end BlockedPresentation

def componentInteriorDiffeomorph (C : CompactCarrier.{u}) (D : C.Components)
    (i : Fin D.count) :
    (componentCarrier C D i).pieceInterior ⊤ ≃ₘ⟮(componentCarrier C D i).model, C.model⟯
      C.pieceInterior (D.piece i) :=
  pieceInteriorCongr (topOpensDiffeomorph (I := C.model) (D.piece i))

def transportInteriorGeometry {C : CompactCarrier.{u}} {D : CompactCarrier.{v}}
    {U : TopologicalSpace.Opens C.Carrier} {V : TopologicalSpace.Opens D.Carrier}
    (e : C.pieceInterior U ≃ₘ⟮C.model, D.model⟯ D.pieceInterior V)
    (g : D.InteriorGeometry V) : C.InteriorGeometry U := by
  letI := Manifold.interiorChartedSpace D.model ∞ (M := D.pieceInterior V)
  letI := Manifold.interiorIsManifold D.model ∞ (M := D.pieceInterior V)
  exact interiorGeometryOfDiffeomorph g C U
    (e.trans (Manifold.interiorAtlasDiffeomorph D.model ∞))

def geometricDecomposition_of_blockGeometry {Q : ConnectedClosedOrientedManifold.{u} 3}
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (G : ∀ i, (componentCarrier B.base.cutCarrier B.base.components i).InteriorGeometry ⊤) :
    GeometricDecomposition Q :=
  B.base.toTorusDecomposition.toGeometricDecomposition (B.incompressible_of_isGood hB)
    (fun i => transportInteriorGeometry
      (componentInteriorDiffeomorph B.base.cutCarrier B.base.components i).symm (G i))

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

theorem interiorImage_eq_interior_of_pairing_count_zero (T : TorusPresentation W)
    (h : T.pairing.count = 0) : T.interiorImage = W.interior := by
  ext y
  constructor
  · intro hy
    let x := T.interiorDiffeomorph.symm ⟨y, hy⟩
    have hx : T.cutCarrier.model.IsInteriorPoint x :=
      ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property
    have hi := ((T.interiorDiffeomorph.isLocalDiffeomorph x).isInteriorPoint_iff
      (by simp)).mp hx
    have he : T.interiorDiffeomorph x = ⟨y, hy⟩ :=
      T.interiorDiffeomorph.apply_symm_apply ⟨y, hy⟩
    rw [he] at hi
    exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp hi
  · intro hy
    obtain ⟨x, rfl⟩ := T.cutMap_surjective y
    have hx : T.cutCarrier.model.IsInteriorPoint x := by
      rcases T.cutCarrier.model.isInteriorPoint_or_isBoundaryPoint x with hx | hx
      · exact hx
      · change x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier at hx
        rw [T.cut_boundary_exhausted] at hx
        rcases hx with hx | hx
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact (Fin.elim0 (h ▸ j))
        · obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
          have he := T.marked_collar j (t, halfZero) (zero_mem_halfCollarSource t)
          change T.cutMap (T.cutExternal.torusMap j t) = T.external.torusMap j t at he
          rw [he] at hy
          exact False.elim ((W.model.isInteriorPoint_iff_not_isBoundaryPoint
            (T.external.torusMap j t)).mp hy (T.external.boundary_zero j t))
    have hi := (T.interiorDiffeomorph ⟨x, hx⟩).property
    rw [T.interior_map ⟨x, hx⟩] at hi
    exact hi

end TorusPresentation

private theorem unionGeometry_piece_eq_top_of_count_one (C : CompactCarrier.{u})
    (D : C.Components) (h : D.count = 1) (i : Fin D.count) : D.piece i = ⊤ := by
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ j, (D.piece j : Set C.Carrier) := by rw [D.covers]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have he : j = i := Fin.ext (by have hj := j.isLt; have hi := i.isLt; omega)
  rwa [he] at hj

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

def unfilledInteriorDiffeomorph (B : SeifertBlock W d) (h : d.fillingCount = 0) :
    B.presentation.cutCarrier.pieceInterior (B.presentation.components.piece (B.piece none))
      ≃ₘ⟮B.presentation.cutCarrier.model, W.model⟯ W.pieceInterior ⊤ := by
  have hc : B.presentation.components.count = 1 := by rw [B.components_count, h]
  have hp := unionGeometry_piece_eq_top_of_count_one B.presentation.cutCarrier
    B.presentation.components hc (B.piece none)
  have hs : B.presentation.pairing.count = 0 := B.pairing_count.trans h
  change ↥(B.presentation.components.piece (B.piece none) ⊓ B.presentation.cutCarrier.interior)
    ≃ₘ⟮B.presentation.cutCarrier.model, W.model⟯
      ↥((⊤ : TopologicalSpace.Opens W.Carrier) ⊓ W.interior)
  rw [hp, top_inf_eq, top_inf_eq,
    ← B.presentation.interiorImage_eq_interior_of_pairing_count_zero hs]
  exact B.presentation.interiorDiffeomorph

def unfilledInteriorGeometry (B : SeifertBlock W d) (h : d.fillingCount = 0)
    (g : B.presentation.cutCarrier.InteriorGeometry
      (B.presentation.components.piece (B.piece none))) : W.InteriorGeometry ⊤ :=
  transportInteriorGeometry (B.unfilledInteriorDiffeomorph h).symm g

end SeifertBlock

def T2Interval.carrierInteriorGeometry {W : CompactCarrier.{u}} (B : T2Interval W) :
    W.InteriorGeometry ⊤ :=
  B.unfilledInteriorGeometry rfl B.interiorGeometry

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

private theorem unionGeometry_no_ownedSide (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    (s : B.base.OwnedSide i) : False := by
  have hc : (B.block i).presentation.externalCount = 0 :=
    (B.block i).externalCount_eq.trans h
  exact Fin.elim0 (hc ▸ (B.port i).symm s)

private theorem unionGeometry_no_block (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    {x : B.base.cutCarrier.Carrier} (hx : x ∈ B.base.components.piece i)
    (j : Fin B.base.pairing.count) : x ∉ B.base.pairing.gluing.block j := by
  intro hb
  rcases hb with hb | hb
  · have he : B.base.leftPiece j = i := by
      by_contra hn
      exact (B.base.components.disjoint hn).le_bot ⟨B.base.left_owned j hb, hx⟩
    exact unionGeometry_no_ownedSide B i h ⟨.inl j, he⟩
  · have he : B.base.rightPiece j = i := by
      by_contra hn
      exact (B.base.components.disjoint hn).le_bot ⟨B.base.right_owned j hb, hx⟩
    exact unionGeometry_no_ownedSide B i h ⟨.inr (.inl j), he⟩

private theorem unionGeometry_saturated_piece (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0)
    {x y : B.base.cutCarrier.Carrier} (hx : x ∈ B.base.components.piece i)
    (he : B.base.cutMap x = B.base.cutMap y) : y ∈ B.base.components.piece i := by
  rcases Quotient.exact (B.base.reconstruction.injective he) with he | ⟨j, hj, hf⟩
  · exact he ▸ hx
  · exact False.elim (unionGeometry_no_block B i h hx j hj)

theorem unique_block_of_ports_eq_zero (B : BlockedPresentation (NoCuts.carrier Q))
    (i : Fin B.base.components.count) (h : (B.data i).ports = 0) :
    B.base.components.count = 1 ∧ B.base.pairing.count = 0 := by
  let S : Set B.base.cutCarrier.Carrier := B.base.components.piece i
  let K := B.base.cutMap '' S
  have hc : Continuous B.base.cutMap := B.base.quotient_smooth.continuous
  have hk : IsClosed K := ((B.base.components.piece_compact i).image hc).isClosed
  have he : Kᶜ = B.base.cutMap '' Sᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := B.base.cutMap_surjective y
      exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
      exact hx (unionGeometry_saturated_piece B i h hz he)
  have ho : IsOpen K := by
    apply isClosed_compl_iff.mp
    rw [he]
    exact ((B.base.components.piece i).isOpen.isClosed_compl.isCompact.image hc).isClosed
  have hn : K.Nonempty := by
    let := B.base.components.connected i
    obtain ⟨x⟩ := (inferInstance : Nonempty (B.base.components.piece i))
    exact ⟨B.base.cutMap x, x, x.property, rfl⟩
  have hu : K = Set.univ := (IsClopen.eq_univ ⟨hk, ho⟩ hn)
  have hj : ∀ j : Fin B.base.components.count, j = i := by
    intro j
    let := B.base.components.connected j
    obtain ⟨x⟩ := (inferInstance : Nonempty (B.base.components.piece j))
    have hm : B.base.cutMap x ∈ K := by rw [hu]; trivial
    obtain ⟨z, hz, he⟩ := hm
    have hxi := unionGeometry_saturated_piece B i h hz he
    by_contra hji
    exact (B.base.components.disjoint hji).le_bot ⟨x.property, hxi⟩
  have hn : B.base.components.count = 1 := by
    have hp := B.base.components.count_pos
    by_contra hne
    have ht : 1 < B.base.components.count := by omega
    have he := (hj ⟨0, by omega⟩).trans (hj ⟨1, ht⟩).symm
    have hv : (0 : ℕ) = 1 := congrArg Fin.val he
    omega
  refine ⟨hn, ?_⟩
  by_contra hs
  let j : Fin B.base.pairing.count := ⟨0, Nat.pos_of_ne_zero hs⟩
  exact unionGeometry_no_ownedSide B i h ⟨.inl j, hj (B.base.leftPiece j)⟩

end BlockedPresentation

end GC.Seifert
