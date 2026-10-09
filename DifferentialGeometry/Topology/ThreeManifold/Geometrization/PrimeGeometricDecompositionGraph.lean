import DifferentialGeometry.Geometry.Thurston.ZeroCutHyperbolic
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Interfaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereInstances
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.FactorInheritance
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Admission (b), graph branch without tori

Lane K17b (chapter 6 design v2, §1 (b), "Zero tori": `.graph`: transport, then
`GM/Refinement.lean:41`). With `D.boundary.count = 0` K17's carrier diffeomorphism onto `M`
preserves orientation (`carrierDiffeomorphOfCountEqZero_preservesOrientation`, K17's open item):
its value is `D.reconstruction` after the quotient map (`carrierDiffeomorphOfCountEqZero_apply`),
so its differential is that of `D.reconstruction ∘ D.boundary.quotientMap`, which carries the
carrier orientation to the orientation of `M` (`quotient_oriented` of the assembly, then the
oriented reconstruction). The only piece of `D` is the whole carrier, and the inclusion of the
piece followed by that diffeomorphism is an orientation-preserving diffeomorphism of the
component carrier onto `M` (`componentDiffeomorphOfCountEqZero`, by the same computation through
`mfderiv_restrict_open`). A raw presentation of the piece is therefore a raw presentation of
`NoCuts.carrier M` (`rawGraphPresentationOfCountEqZero`).

From there the branch is exactly the closed case of the frozen interface: `M` geometrizes as soon
as every closed oriented manifold with a raw presentation does
(`geometrizes_of_zeroCut_graph`), which holds under the existing named inputs of chapters 5 and 6:
`GraphPrimeStructure` (the interface (S)) and K07's `SeifertRefinement`,
`ClosedTriangleBlockGeometry`, `GoodBlockUnionGeometry`
(`geometrizes_of_rawGraphPresentation_of_inputs`), or with (S) replaced by its reduction
`RawPresentationFactorInheritance`
(`geometrizes_of_rawGraphPresentation_of_factorInheritance_of_inputs`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Topology.TorusDecomposition

universe u

private def opensDiffeomorphOfForall {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (U : TopologicalSpace.Opens X) (h : ∀ x : X, x ∈ U) :
    U ≃ₘ⟮I, I⟯ X where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv := Function.leftInverse_iff_comp.mpr rfl
  right_inv := Function.rightInverse_iff_comp.mpr rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

variable {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)

theorem mem_piece_of_count_eq_zero (h : D.boundary.count = 0) (i : Fin D.components.count)
    (x : D.carrier.Carrier) : x ∈ D.components.piece i := by
  rw [D.piece_eq_top_of_count_eq_zero h i]
  trivial

theorem carrierDiffeomorphOfCountEqZero_apply (h : D.boundary.count = 0)
    (x : D.carrier.Carrier) :
    D.carrierDiffeomorphOfCountEqZero h x = D.reconstruction.val (D.boundary.quotientMap x) := by
  change D.reconstruction.val (D.reconstructionAtlas.interiorDiffeomorph
    ⟨x, D.mem_interior_of_count_eq_zero h x⟩).val = _
  rw [D.reconstructionAtlas.interior_map]

theorem carrierDiffeomorphOfCountEqZero_preservesOrientation (h : D.boundary.count = 0) :
    (D.carrierDiffeomorphOfCountEqZero h).preservesOrientation D.carrier.orientation
      M.orientation := by
  intro x
  obtain ⟨L, hL, ho⟩ := D.reconstructionAtlas.quotient_oriented x
  let q : D.carrier.Carrier → D.reconstructionAtlas.assembled.Carrier := D.boundary.quotientMap
  have hq : MDifferentiableAt D.carrier.model (𝓡 3) q x := by
    let := D.reconstructionAtlas.charts
    let := D.reconstructionAtlas.smooth
    exact D.reconstructionAtlas.quotient_smooth.mdifferentiable (by simp) _
  let R := (D.reconstruction.val.mfderivToContinuousLinearEquiv (by simp) (q x)).toLinearEquiv
  have hf : (⇑(D.carrierDiffeomorphOfCountEqZero h) : D.carrier.Carrier → M.Carrier) =
      D.reconstruction.val ∘ q :=
    funext (D.carrierDiffeomorphOfCountEqZero_apply h)
  have hlin : ((D.carrierDiffeomorphOfCountEqZero h).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv = L.trans R := by
    apply LinearEquiv.ext
    intro v
    change mfderiv D.carrier.model (𝓡 3) (D.carrierDiffeomorphOfCountEqZero h) x v =
      mfderiv (𝓡 3) (𝓡 3) D.reconstruction.val (q x) (L v)
    rw [hf, mfderiv_comp x (D.reconstruction.val.mdifferentiable (by simp) _) hq]
    exact congrArg (mfderiv (𝓡 3) (𝓡 3) D.reconstruction.val (q x)) (hL v).symm
  have hmap : ∀ o, Orientation.map (Fin 3) (L.trans R) o =
      Orientation.map (Fin 3) R (Orientation.map (Fin 3) L o) := by
    intro o
    induction o using Module.Ray.ind with
    | h v hv => rfl
  rw [hlin]
  refine (hmap _).trans ?_
  rw [ho, D.carrierDiffeomorphOfCountEqZero_apply]
  exact D.reconstruction.property (q x)

def componentDiffeomorphOfCountEqZero (h : D.boundary.count = 0) (i : Fin D.components.count) :
    D.components.piece i ≃ₘ⟮D.carrier.model, 𝓡 3⟯ M.Carrier :=
  (opensDiffeomorphOfForall (D.components.piece i) (D.mem_piece_of_count_eq_zero h i)).trans
    (D.carrierDiffeomorphOfCountEqZero h)

theorem componentDiffeomorphOfCountEqZero_apply (h : D.boundary.count = 0)
    (i : Fin D.components.count) (x : D.components.piece i) :
    D.componentDiffeomorphOfCountEqZero h i x =
      D.reconstruction.val (D.boundary.quotientMap x.val) := by
  change D.reconstruction.val (D.reconstructionAtlas.interiorDiffeomorph
    ⟨x.val, D.mem_interior_of_count_eq_zero h x.val⟩).val = _
  rw [D.reconstructionAtlas.interior_map]

theorem componentDiffeomorphOfCountEqZero_preservesOrientation (h : D.boundary.count = 0)
    (i : Fin D.components.count) :
    (D.componentDiffeomorphOfCountEqZero h i).preservesOrientation
      (D.carrier.orientation.restrictOpen (D.components.piece i)) M.orientation := by
  intro x
  obtain ⟨L, hL, ho⟩ := D.reconstructionAtlas.quotient_oriented x.val
  let q : D.carrier.Carrier → D.reconstructionAtlas.assembled.Carrier := D.boundary.quotientMap
  have hq : MDifferentiableAt D.carrier.model (𝓡 3) q x.val := by
    let := D.reconstructionAtlas.charts
    let := D.reconstructionAtlas.smooth
    exact D.reconstructionAtlas.quotient_smooth.mdifferentiable (by simp) _
  let R := (D.reconstruction.val.mfderivToContinuousLinearEquiv (by simp) (q x.val)).toLinearEquiv
  have hf : (⇑(D.componentDiffeomorphOfCountEqZero h i) : D.components.piece i → M.Carrier) =
      fun y => (D.reconstruction.val ∘ q) y.val :=
    funext (D.componentDiffeomorphOfCountEqZero_apply h i)
  have hlin : ((D.componentDiffeomorphOfCountEqZero h i).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv = L.trans R := by
    apply LinearEquiv.ext
    intro v
    change mfderiv D.carrier.model (𝓡 3) (D.componentDiffeomorphOfCountEqZero h i) x v =
      mfderiv (𝓡 3) (𝓡 3) D.reconstruction.val (q x.val) (L v)
    rw [hf, DifferentialGeometry.mfderiv_restrict_open,
      mfderiv_comp x.val (D.reconstruction.val.mdifferentiable (by simp) _) hq]
    exact congrArg (mfderiv (𝓡 3) (𝓡 3) D.reconstruction.val (q x.val)) (hL v).symm
  have hmap : ∀ o, Orientation.map (Fin 3) (L.trans R) o =
      Orientation.map (Fin 3) R (Orientation.map (Fin 3) L o) := by
    intro o
    induction o using Module.Ray.ind with
    | h v hv => rfl
  rw [hlin]
  refine (hmap _).trans ?_
  change Orientation.map (Fin 3) R (Orientation.map (Fin 3) L
    (D.carrier.orientation.orientation x.val)) = _
  rw [ho, D.componentDiffeomorphOfCountEqZero_apply]
  exact D.reconstruction.property (q x.val)

def rawGraphPresentationOfCountEqZero (h : D.boundary.count = 0) (i : Fin D.components.count)
    (G : RawGraphPresentation (componentCarrier D.carrier D.components i)) :
    RawGraphPresentation (NoCuts.carrier M) :=
  G.transport (D.componentDiffeomorphOfCountEqZero h i)
    (D.componentDiffeomorphOfCountEqZero_preservesOrientation h i)

end GC.Topology.TorusDecomposition

namespace GC.Endpoint

universe u

theorem geometrizes_of_zeroCut_graph
    (hgraph : ∀ N : ConnectedClosedOrientedManifold.{u} 3,
      RawGraphPresentation (NoCuts.carrier N) → Geometrizes N)
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (h : D.boundary.count = 0) (i : Fin D.components.count)
    (G : RawGraphPresentation (componentCarrier D.carrier D.components i)) : Geometrizes M :=
  hgraph M (D.rawGraphPresentationOfCountEqZero h i G)

theorem geometrizes_of_rawGraphPresentation_of_inputs (hP : GraphPrimeStructure.{u})
    (hS : GC.Seifert.SeifertRefinement.{u}) (hT : GC.Seifert.ClosedTriangleBlockGeometry.{u})
    (hU : GC.Seifert.GoodBlockUnionGeometry.{u}) (N : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier N)) : Geometrizes N :=
  geometrizes_of_rawGraphPresentation_of_graphPrimeStructure hP
    (GC.Seifert.exists_geometric_decomposition_of_prime_rawGraphPresentation_of_inputs hS hT hU)
    N G

theorem geometrizes_of_rawGraphPresentation_of_factorInheritance_of_inputs
    (hF : RawPresentationFactorInheritance.{u}) (hS : GC.Seifert.SeifertRefinement.{u})
    (hT : GC.Seifert.ClosedTriangleBlockGeometry.{u})
    (hU : GC.Seifert.GoodBlockUnionGeometry.{u}) (N : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier N)) : Geometrizes N :=
  geometrizes_of_rawGraphPresentation_of_inputs (graphPrimeStructure_of_factorInheritance hF)
    hS hT hU N G

theorem exists_prime_geometric_decomposition_of_geometrizes
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : Geometrizes M) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  obtain ⟨C⟩ := hM
  exact ⟨C.primeData, fun j => ⟨C.geometricFactors j⟩⟩

end GC.Endpoint
