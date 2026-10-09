import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusPresentation

/-!
Packaging the actual smooth torus quotient as a compact carrier and its exact torus presentation.
The orientation ledger is supplied by the surgery orientation construction on the same quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}} (P : TorusPairing C) {k : CarrierModel}
  [ChartedSpace k.Space P.QuotientSpace] [IsManifold k.model ∞ P.QuotientSpace]

abbrev surgeryCarrier (O : ManifoldOrientation k.model P.QuotientSpace 3) : CompactCarrier.{u} where
  kind := k
  Carrier := P.QuotientSpace
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  hausdorff := inferInstance
  compact := inferInstance
  secondCountable := P.surgery_quotient_secondCountable
  orientation := O

variable (D : C.Components) {n : ℕ} (E : BoundaryTori C n)
  (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
    (P.surgerySideCollar j).target)
  (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
  (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
  (hpatch : ∀ i, ContMDiffOn (P.surgeryPatchModel n i) k.model ∞
      (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
    ContMDiffOn k.model (P.surgeryPatchModel n i) ∞
      (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target)

private def surgeryInteriorTarget : Opens P.QuotientSpace :=
  ⟨(P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).target,
    (P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).open_target⟩

private def surgeryInteriorEquivalence :
    C.interior ≃ₘ⟮C.model, k.model⟯ P.surgeryInteriorTarget D E hb := by
  let d := P.surgeryInteriorDiffeomorphism (k := k) D E hd he hb hpatch
  have hs : d.source = C.interior := P.surgeryInteriorPatch_source D
    (P.surgeryCoreBoundarySubset E hb)
  let f : C.interior → P.surgeryInteriorTarget D E hb :=
    fun x => ⟨d x, d.map_source (hs.symm.subset x.property)⟩
  let g : P.surgeryInteriorTarget D E hb → C.interior :=
    fun y => ⟨d.symm y, hs.subset (d.map_target y.property)⟩
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · intro x
    apply Subtype.ext
    exact d.left_inv (hs.symm.subset x.property)
  · intro y
    apply Subtype.ext
    exact d.right_inv y.property
  · apply (ContMDiff.subtypeVal_comp_iff (P.surgeryInteriorTarget D E hb) f).mp
    intro x
    exact contMDiffAt_subtype_iff.mpr
      (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds (hs.symm.subset x.property)))
  · apply (ContMDiff.subtypeVal_comp_iff C.interior g).mp
    intro y
    exact contMDiffAt_subtype_iff.mpr
      (d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds y.property))

private abbrev surgeryBoundaryTori (O : ManifoldOrientation k.model P.QuotientSpace 3) :
    BoundaryTori (P.surgeryCarrier O) n where
  collar := P.surgeryExternalDiffeomorphism D E hd he hb hpatch
  source_eq := P.surgeryExternalCollar_source E he
  boundary_zero j t := by
    have hh := P.surgeryExternal_zero_boundary D E hd he hb hpatch j t
    change k.model.IsBoundaryPoint (P.surgeryExternalCollar E he j (t, halfZero))
    rw [P.surgeryExternalCollar_apply E he j (zero_mem_halfCollarSource t)]
    exact hh
  disjoint := P.surgeryExternalCollar_targets_disjoint E he

private theorem surgeryBoundaryTori_image (O : ManifoldOrientation k.model P.QuotientSpace 3) :
    (P.surgeryBoundaryTori D E hd he hb hpatch O).image = P.quotientMap '' E.image := by
  ext q
  constructor
  · intro hq
    obtain ⟨j, t, ht⟩ := mem_iUnion.mp hq
    refine ⟨E.torusMap j t, mem_iUnion.mpr ⟨j, ⟨t, rfl⟩⟩, ?_⟩
    change P.surgeryExternalCollar E he j (t, halfZero) = q at ht
    rw [P.surgeryExternalCollar_apply E he j (zero_mem_halfCollarSource t)] at ht
    exact ht
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨j, ⟨t, ?_⟩⟩
    change P.surgeryExternalCollar E he j (t, halfZero) = P.quotientMap (E.torusMap j t)
    exact P.surgeryExternalCollar_apply E he j (zero_mem_halfCollarSource t)

def surgeryPresentation (O : ManifoldOrientation k.model P.QuotientSpace 3)
    (ho : ∀ x : C.Carrier,
      Orientation.map (Fin 3) (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
        (C.orientation.orientation x) = O.orientation (P.quotientMap x))
    (left right : Fin P.count → Fin D.count) (external : Fin n → Fin D.count)
    (hl : ∀ j, P.gluing.left j ⊆ D.piece (left j))
    (hr : ∀ j, P.gluing.right j ⊆ D.piece (right j))
    (hex : ∀ j, range (E.torusMap j) ⊆ D.piece (external j)) :
    TorusPresentation (P.surgeryCarrier O) where
  cutCarrier := C
  components := D
  pairing := P
  externalCount := n
  external := P.surgeryBoundaryTori D E hd he hb hpatch O
  cutExternal := E
  external_exhausted := by
    rw [P.surgeryBoundaryTori_image]
    exact P.surgeryQuotient_boundary D E hd he hb hpatch
  cut_boundary_exhausted := hb
  external_disjoint := by
    apply disjoint_left.mpr
    intro x hx hext
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hext
    have ht : E.torusMap i t ∈ (E.collar i).target :=
      (E.collar i).map_source ((E.source_eq i).symm.subset (zero_mem_halfCollarSource t))
    exact P.surgeryExternal_target_notMem_block E he i ht j hj
  reconstruction := Homeomorph.refl P.QuotientSpace
  quotient_smooth := P.surgeryQuotientFold_contMDiff D E hd he hb hpatch
  quotient_oriented x :=
    ⟨P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x,
      P.surgeryQuotientFoldTangentEquiv_apply D E hd he hb hpatch x, ho x⟩
  interiorImage := P.surgeryInteriorTarget D E hb
  interiorDiffeomorph := P.surgeryInteriorEquivalence D E hd he hb hpatch
  interior_map x := P.surgeryInteriorPatch_apply D (P.surgeryCoreBoundarySubset E hb) x.property
  seam := P.surgerySeamDiffeomorphism D E hd he hb hpatch
  seam_source := P.surgerySignedSeam_source hd
  seam_zero := P.surgerySignedSeam_zero hd
  seam_positive j t s hs hlt := P.surgerySignedSeam_positive hd j t s hs hlt
  seam_negative j t s hs hlt := P.surgerySignedSeam_negative hd j t s hs hlt
  seam_interior := P.surgerySignedSeam_target_interior D E hd he hb hpatch
  seam_disjoint := P.surgerySignedSeam_disjoint hd
  marked_collar j p hp := (P.surgeryExternalCollar_apply E he j hp).symm
  external_seam_disjoint := P.surgeryExternalCollar_seam_disjoint E he hd
  leftPiece := left
  rightPiece := right
  left_owned := hl
  right_owned := hr
  externalPiece := external
  external_owned := hex

end GC.GraphManifold.TorusPairing
