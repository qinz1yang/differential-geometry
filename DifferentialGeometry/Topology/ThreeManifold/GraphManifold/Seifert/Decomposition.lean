import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

/-!
# Closed torus presentations as torus decompositions

Chapter 6, K04. A torus presentation `T` of a closed manifold `P` (of `NoCuts.carrier P`) has no
external tori (`externalCount_eq_zero`, from `external_exhausted` and the empty boundary of `P`),
so its pairing glues all of the boundary of the cut carrier: `toTorusGluing` is the `TorusGluing`
with one gluing torus per pairing torus, the same blocks, parameters, matchings and collars, and
`boundary_exhausted` read off `cut_boundary_exhausted`. The one field a pairing does not carry,
`torusOrientation`, is the product orientation of the circle orientation transported from the
unit sphere of `ℝ²` (`productTorusOrientation`); it is the same for every torus and no consumer
reads it.

The assembled space is the quotient of the pairing, charted by pulling back the charts of `P`
along `T.reconstruction` (`quotientManifold`), so `T.reconstruction` becomes an oriented
diffeomorphism (`reconstructionDiffeomorph`), as in the zero-torus template
`NoCuts.assembly`. Smoothness, orientation, the interior diffeomorphism and the seams of the
`SmoothAssembly` are those of `T` composed with its inverse; the boundary reversal is the
pairing's. `toTorusDecomposition` keeps the cut carrier, the pieces and their ownership;
its pieces are `T`'s pieces, its tori `T`'s pairing tori, and its tori and seams in `P` are
`T`'s seams (`toTorusDecomposition_torusInPrime`, `toTorusDecomposition_primeSeam`).
`RawGraphPresentation.toTorusDecomposition` goes through the forgetful map.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def circleOrientation : ManifoldOrientation (𝓡 1) Circle 1 :=
  (Manifold.exists_manifoldOrientation_diffeomorph_map sphereOneDiffeomorphCircle
    (sphereOrientation 1 le_rfl)).choose

def productTorusOrientation : ManifoldOrientation torusModel Torus 2 :=
  productOrientation (𝓡 1) (𝓡 1) le_rfl le_rfl circleOrientation circleOrientation

private def imageOpensDiffeomorph {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (e : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (U : TopologicalSpace.Opens M) :
    U ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (⟨e '' U, e.toHomeomorph.isOpenMap _ U.isOpen⟩ : TopologicalSpace.Opens N) where
  toFun x := ⟨e x, Set.mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨x, hx, he⟩ := y.property
    rw [← he, e.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.symm.contMDiff.comp contMDiff_subtype_val)

namespace TorusPresentation

section Gluing
variable {W : CompactCarrier.{u}}

theorem cutExternal_image_eq_empty (T : TorusPresentation W) (hT : T.externalCount = 0) :
    T.cutExternal.image = ∅ := by
  have : IsEmpty (Fin T.externalCount) := by
    rw [hT]
    infer_instance
  exact Set.iUnion_of_empty _

def toTorusGluing (T : TorusPresentation W) (hT : T.externalCount = 0) :
    TorusGluing T.cutCarrier where
  count := T.pairing.count
  gluing := T.pairing.gluing
  leftParam := T.pairing.leftParam
  rightParam := T.pairing.rightParam
  matching := T.pairing.matching
  matching_eq := T.pairing.matching_eq
  torusOrientation _ := productTorusOrientation
  leftCollar := T.pairing.leftCollar
  rightCollar := T.pairing.rightCollar
  left_source := T.pairing.left_source
  right_source := T.pairing.right_source
  left_zero := T.pairing.left_zero
  right_zero := T.pairing.right_zero
  boundary_exhausted := by
    rw [T.cut_boundary_exhausted, T.cutExternal_image_eq_empty hT, Set.union_empty]

variable (T : TorusPresentation W) (hT : T.externalCount = 0)

@[simp] theorem toTorusGluing_count : (T.toTorusGluing hT).count = T.pairing.count := rfl

@[simp] theorem toTorusGluing_quotientMap (x : T.cutCarrier.Carrier) :
    (T.toTorusGluing hT).quotientMap x = T.pairing.quotientMap x := rfl

theorem toTorusGluing_torusMap (i : Fin T.pairing.count) (t : Torus) :
    (T.toTorusGluing hT).torusMap i t = T.pairing.quotientMap (T.pairing.leftParam i t) := rfl

end Gluing

section Closed
variable {P : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier P))

theorem externalCount_eq_zero : T.externalCount = 0 := by
  by_contra h
  have hx : T.external.torusMap ⟨0, Nat.pos_of_ne_zero h⟩ 1 ∈ T.external.image :=
    Set.mem_iUnion.mpr ⟨_, 1, rfl⟩
  rw [← T.external_exhausted, closedCarrier_boundary_eq_empty] at hx
  exact hx

def gluing : TorusGluing T.cutCarrier := T.toTorusGluing T.externalCount_eq_zero

@[simp] theorem gluing_count : T.gluing.count = T.pairing.count := rfl

def assembledHomeomorph : T.gluing.Assembled ≃ₜ P.Carrier := T.reconstruction

def quotientManifold : ConnectedClosedOrientedManifold.{u} 3 :=
  P.pullback T.assembledHomeomorph

def reconstructionDiffeomorph : ClosedOrientedManifold.OrientedDiffeomorph
    T.quotientManifold.toClosedOrientedManifold P.toClosedOrientedManifold :=
  P.pullbackOrientedDiffeomorph T.assembledHomeomorph

def assembly : SmoothAssembly T.gluing := by
  let Q := T.quotientManifold
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) T.gluing.Assembled := Q.charts
  let : IsManifold (𝓡 3) ∞ T.gluing.Assembled := Q.smooth
  let d := T.reconstructionDiffeomorph
  let e : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ T.gluing.Assembled := d.val.symm
  have he : ∀ y, e y = T.reconstruction.symm y := fun _ => rfl
  have hq : (T.gluing.quotientMap : T.cutCarrier.Carrier → T.gluing.Assembled) =
      e ∘ (T.reconstruction ∘ T.pairing.quotientMap) :=
    funext fun x => (T.reconstruction.symm_apply_apply (T.pairing.quotientMap x)).symm
  refine {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    quotient_smooth := ?_
    quotient_oriented := ?_
    boundary_reversing := T.pairing.reversing
    interiorImage := ⟨e '' T.interiorImage, e.toHomeomorph.isOpenMap _ T.interiorImage.isOpen⟩
    interiorDiffeomorph := T.interiorDiffeomorph.trans (imageOpensDiffeomorph e T.interiorImage)
    interior_map := ?_
    seam := fun i => (T.seam i).trans e.toPartialDiffeomorph
    seam_source := ?_
    seam_zero := ?_
    seam_positive := ?_
    seam_negative := ?_ }
  · rw [hq]
    exact e.contMDiff.comp T.quotient_smooth
  · intro x
    rw [hq]
    obtain ⟨L, hL, ho⟩ := T.quotient_oriented x
    let R := (e.mfderivToContinuousLinearEquiv (by simp)
      (T.reconstruction (T.pairing.quotientMap x))).toLinearEquiv
    refine ⟨L.trans R, ?_, ?_⟩
    · intro v
      change R (L v) = mfderiv T.cutCarrier.model (𝓡 3)
        (e ∘ (T.reconstruction ∘ T.pairing.quotientMap)) x v
      rw [mfderiv_comp (I' := 𝓡 3) x (e.mdifferentiable (by simp) _)
        (T.quotient_smooth.mdifferentiable (by simp) x), hL]
      rfl
    · have hmap : Orientation.map (Fin 3) (L.trans R) (T.cutCarrier.orientation.orientation x) =
          Orientation.map (Fin 3) R
            (Orientation.map (Fin 3) L (T.cutCarrier.orientation.orientation x)) := by
        generalize T.cutCarrier.orientation.orientation x = o
        induction o using Module.Ray.ind with
        | h v hv => rfl
      exact hmap.trans ((congrArg (fun o => Orientation.map (Fin 3) R o) ho).trans
        (d.symm.property _))
  · intro x
    change e (T.interiorDiffeomorph x).val = _
    rw [T.interior_map x, he]
    exact T.reconstruction.symm_apply_apply _
  · intro i
    change (T.seam i).source ∩ (T.seam i) ⁻¹' Set.univ = signedCollarSource
    simpa using T.seam_source i
  · intro i t
    change e (T.seam i (t, 0)) = _
    rw [T.seam_zero i t, he]
    exact T.reconstruction.symm_apply_apply _
  · intro i t s hs h
    change e (T.seam i (t, s)) = _
    rw [T.seam_positive i t s hs h, he]
    exact T.reconstruction.symm_apply_apply _
  · intro i t s hs h
    change e (T.seam i (t, s)) = _
    rw [T.seam_negative i t s hs h, he]
    exact T.reconstruction.symm_apply_apply _

def assemblyReconstruction : T.assembly.Reconstruction P := T.reconstructionDiffeomorph

def toTorusDecomposition : TorusDecomposition P where
  carrier := T.cutCarrier
  components := T.components
  boundary := T.gluing
  reconstructionAtlas := T.assembly
  reconstruction := T.assemblyReconstruction
  leftPiece := T.leftPiece
  rightPiece := T.rightPiece
  left_owned := T.left_owned
  right_owned := T.right_owned

@[simp] theorem toTorusDecomposition_carrier : T.toTorusDecomposition.carrier = T.cutCarrier :=
  rfl

@[simp] theorem toTorusDecomposition_components_count :
    T.toTorusDecomposition.components.count = T.components.count := rfl

@[simp] theorem toTorusDecomposition_boundary_count :
    T.toTorusDecomposition.boundary.count = T.pairing.count := rfl

theorem toTorusDecomposition_component (i : Fin T.toTorusDecomposition.components.count) :
    T.toTorusDecomposition.component i = componentCarrier T.cutCarrier T.components i := rfl

theorem toTorusDecomposition_leftPiece (i : Fin T.toTorusDecomposition.boundary.count) :
    T.toTorusDecomposition.leftPiece i = T.leftPiece i := rfl

theorem toTorusDecomposition_rightPiece (i : Fin T.toTorusDecomposition.boundary.count) :
    T.toTorusDecomposition.rightPiece i = T.rightPiece i := rfl

theorem toTorusDecomposition_reconstruction_quotientMap (x : T.cutCarrier.Carrier) :
    T.toTorusDecomposition.reconstruction.val (T.toTorusDecomposition.boundary.quotientMap x) =
      T.cutMap x := rfl

theorem toTorusDecomposition_torusInPrime (i : Fin T.toTorusDecomposition.boundary.count)
    (t : Torus) :
    T.toTorusDecomposition.reconstructionAtlas.torusInPrime
      T.toTorusDecomposition.reconstruction i t = T.seam i (t, 0) :=
  (T.seam_zero i t).symm

theorem toTorusDecomposition_primeSeam (i : Fin T.toTorusDecomposition.boundary.count)
    (p : Torus × ℝ) :
    T.toTorusDecomposition.reconstructionAtlas.primeSeam
      T.toTorusDecomposition.reconstruction i p = T.seam i p :=
  T.reconstruction.apply_symm_apply (T.seam i p)

end Closed

end TorusPresentation

end GC.Seifert

namespace GC.GraphManifold.RawGraphPresentation
open GC.Seifert
variable {P : ConnectedClosedOrientedManifold.{u} 3}

def toTorusDecomposition (G : RawGraphPresentation (NoCuts.carrier P)) : TorusDecomposition P :=
  G.toTorusPresentation.toTorusDecomposition

variable (G : RawGraphPresentation (NoCuts.carrier P))

@[simp] theorem toTorusDecomposition_components_count :
    G.toTorusDecomposition.components.count = G.components.count := rfl

@[simp] theorem toTorusDecomposition_boundary_count :
    G.toTorusDecomposition.boundary.count = G.pairing.count := rfl

theorem toTorusDecomposition_torusInPrime (i : Fin G.toTorusDecomposition.boundary.count)
    (t : Torus) :
    G.toTorusDecomposition.reconstructionAtlas.torusInPrime
      G.toTorusDecomposition.reconstruction i t = G.seam i (t, 0) :=
  G.toTorusPresentation.toTorusDecomposition_torusInPrime i t

end GC.GraphManifold.RawGraphPresentation
