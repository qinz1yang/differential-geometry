import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutAssemblyReal_S31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false

/-!
# CH12-S59 (G1, base): a non-core piece point far from `∂` is not in a core image

Generic pieces of the point sub-leaf `hNC` (O17 G3 / S47 G2):

* `mem_pieceInterior_of_dist_S59` -- `ofReal 10 < distanceToBoundary` puts the point in the
  interior of the block (`mem_interior_of_edist_lt_distanceToBoundary`);
* `isOpen_image_cutInterior_S59` -- for a `TorusDecomposition`, `reconstruction ∘ quotientMap`
  maps open subsets of the cut interior to open subsets (the `TorusDecomposition` analogue of
  `isOpen_image_reconstruction_of_subset_interior`);
* `not_mem_open_of_disjoint_dense_S59` -- open set disjoint from the image of a dense set is
  disjoint from the whole image of a continuous map;
* `noncore_point_stage_S59` -- the stage-level statement (generic stage `Q`, `subst`).
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- A block point at boundary distance `> 10` lies in the interior of the block. -/
theorem mem_pieceInterior_of_dist_S59 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (p : (D.component i).Carrier)
    (hp : ENNReal.ofReal 10 < distanceToBoundary (D.component i) h p) :
    p.val ∈ (D.carrier.pieceInterior (D.components.piece i) : Set D.carrier.Carrier) := by
  have hint : p ∈ (D.component i).model.interior (D.component i).Carrier :=
    mem_interior_of_edist_lt_distanceToBoundary h p p
      (by rw [riemannianEDistOf_self]; exact lt_trans (by simp) hp)
  exact ⟨p.2, (D.carrier.model.isInteriorPoint_iff_isInteriorPoint_val).mp hint⟩

/-- On the cut interior, `reconstruction ∘ quotientMap` is an open embedding. -/
theorem isOpen_image_cutInterior_S59 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) {O : Set D.carrier.Carrier} (hO : IsOpen O)
    (hOI : O ⊆ D.carrier.interior) :
    IsOpen ((fun x => D.reconstruction.val (D.boundary.quotientMap x)) '' O) := by
  let := D.reconstructionAtlas.charts
  let := D.reconstructionAtlas.smooth
  have heq : (fun x => D.reconstruction.val (D.boundary.quotientMap x)) '' O =
      D.reconstruction.val '' (Subtype.val '' (D.reconstructionAtlas.interiorDiffeomorph ''
        (Subtype.val ⁻¹' O))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨_, ⟨D.reconstructionAtlas.interiorDiffeomorph ⟨x, hOI hx⟩,
        ⟨⟨x, hOI hx⟩, hx, rfl⟩, rfl⟩, ?_⟩
      exact congrArg D.reconstruction.val (D.reconstructionAtlas.interior_map ⟨x, hOI hx⟩)
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x.val, hx, (congrArg D.reconstruction.val (D.reconstructionAtlas.interior_map x)).symm⟩
  rw [heq]
  exact D.reconstruction.val.toHomeomorph.isOpenMap _
    (D.reconstructionAtlas.interiorImage.isOpen.isOpenMap_subtype_val _
      (D.reconstructionAtlas.interiorDiffeomorph.toHomeomorph.isOpenMap _
        (hO.preimage continuous_subtype_val)))

/-- An open set disjoint from the image of a dense set misses the whole image of a continuous
map. -/
theorem not_mem_open_of_disjoint_dense_S59 {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
    {S : Set A} (hS : Dense S) {f : A → Z} (hf : Continuous f) {U : Set Z} (hU : IsOpen U)
    (hd : Disjoint U (f '' S)) (a : A) : f a ∉ U := by
  intro ha
  obtain ⟨x, hxU, hxS⟩ := hS.inter_open_nonempty (f ⁻¹' U) (hU.preimage hf) ⟨a, ha⟩
  exact Set.disjoint_left.mp hd hxU ⟨x, hxS, rfl⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- **Stage-level `hNC` (S59).**  On a generic stage `Q` equal to the post stage at `t`: a point
`p` of a block of any decomposition `dec` of a component of `Q`, at boundary distance `> 10`, is not
in the (transported) image of any core `range (D.truncation c).inclusion`, provided the block image
is disjoint from every core-interior image. -/
theorem noncore_point_stage_S59 {K : ℕ} {cores : PersistentHyperbolicCores F K} {t : ℝ}
    (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)
    (hdom : ∀ i, range (D.truncation i).inclusion ⊆
      (cores.domain i t : Set (cores.model i).Carrier))
    {Q : OrientedThreeStage.{u}} (h : postStage F.observation t = Q)
    (C : ConnectedComponents Q.Carrier)
    (dec : TorusDecomposition (Q.toClosedOrientedManifold.component C))
    (i : Fin dec.components.count)
    (hnc : ∀ c : Fin cores.count,
      Disjoint
        ((fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val : Q.Carrier)) ''
          (dec.carrier.pieceInterior (dec.components.piece i) : Set _))
        ((fun x => cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h)
            (cores.map c t ht ((D.truncation c).inclusion x))) ''
          ((D.truncation c).core.interior : Set _)))
    (g' : SmoothRiemannianMetric (dec.component i).model (dec.component i).Carrier)
    (p : (dec.component i).Carrier)
    (hp : ENNReal.ofReal 10 < distanceToBoundary (dec.component i) g' p) :
    ((cutPieceMap dec i p).val : Q.Carrier) ∉
      cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h) '' ⋃ c : Fin cores.count,
        cores.map c t ht '' Set.range (D.truncation c).inclusion := by
  subst h
  rintro ⟨z, hz, hzy⟩
  obtain ⟨c, hc⟩ := mem_iUnion.mp hz
  obtain ⟨w, ⟨x, rfl⟩, rfl⟩ := hc
  have hU : IsOpen ((fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val :
      (postStage F.observation t).Carrier)) ''
        (dec.carrier.pieceInterior (dec.components.piece i) : Set _)) := by
    have himg : (fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val :
        (postStage F.observation t).Carrier)) ''
          (dec.carrier.pieceInterior (dec.components.piece i) : Set _) =
        Subtype.val '' ((fun x => dec.reconstruction.val (dec.boundary.quotientMap x)) ''
          (dec.carrier.pieceInterior (dec.components.piece i) : Set _)) :=
      (Set.image_image Subtype.val (fun x => dec.reconstruction.val (dec.boundary.quotientMap x))
        _).symm
    rw [himg]
    exact ((postStage F.observation t).toClosedOrientedManifold.componentOpen C).isOpen.isOpenMap_subtype_val _
      (isOpen_image_cutInterior_S59 dec (dec.carrier.pieceInterior _).isOpen (fun x hx => hx.2))
  have hy : ((cutPieceMap dec i p).val : (postStage F.observation t).Carrier) ∈
      (fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val :
        (postStage F.observation t).Carrier)) ''
        (dec.carrier.pieceInterior (dec.components.piece i) : Set _) :=
    ⟨p.val, mem_pieceInterior_of_dist_S59 dec i g' p hp, rfl⟩
  have hd : Disjoint ((fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val :
      (postStage F.observation t).Carrier)) ''
        (dec.carrier.pieceInterior (dec.components.piece i) : Set _))
      (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) := hnc c
  have key := not_mem_open_of_disjoint_dense_S59
    (S := ((D.truncation c).core.interior : Set _))
    (ModelWithCorners.dense_interior (I := (D.truncation c).core.model)
      (M := (D.truncation c).core.Carrier))
    (corePhi_continuous_S28 D ht hdom c) hU hd x
  apply key
  have hzy' : corePhi_S28 D ht c x = (cutPieceMap dec i p).val := hzy
  rw [hzy']
  exact hy

end GC.LongTime.Ch12
