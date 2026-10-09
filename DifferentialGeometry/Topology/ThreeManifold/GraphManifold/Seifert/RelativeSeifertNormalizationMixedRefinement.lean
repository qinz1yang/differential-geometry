import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStage
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationLedger
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativePieceAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryFlat

/-!
# Mixed refinements and the initial mixed stage

Lane BR, tier R6, assembly (review 26 §2.2, §5.1). A `LocalDatum T i` is a cut system of the
component carrier `i` of a torus presentation `T`, with pieces modelled with boundary, and its port
bijection whose external half collars are the port collars of `T` on the whole collar
(`ofElementary` for an elementary presentation of the component, `ofPiece` for the component
itself). A `MixedRefinement T` chooses one for every piece, a set of frozen pieces whose local
systems have no seam and carry, piece by piece, an interior hyperbolic geometry on a compact
carrier diffeomorphic to the native piece, and product certificates on all other pieces.

Its splice (MD6's `Refinement.splice`) is a mixed stage of `Q` when `T` presents
`NoCuts.carrier Q` (`MixedRefinement.toMixedStage`): the protected seams are the old seams of `T`,
the frozen pieces are those coming from frozen components, their geometry is transported along the
native piece diffeomorphisms, the product structures come from the certificates piece by piece
(`pieceOfCertificateData`), and every inserted seam lies in a non-frozen component, so all sides
of frozen pieces are protected. The old seams are kept exactly (`toMixedStage_seam`): the splice
seam of the old index is the old seam, so the protected-seam ledger is the identity
(`toMixedStage_protEquiv`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

variable {W : CompactCarrier.{u}} {k : CarrierModel}

def pieceOfCertificateData (S : EmbeddedCutSystem W k) (j : Fin S.count)
    (base : PlanarBase.{u} (S.torusCount j))
    (triv : (base.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model base.surface.kind).prod (𝓡 1),
      k.model⟯ S.Piece j)
    (hcol : ∀ l p, p ∈ halfCollarSource →
      S.collar j l p = triv (base.collar l (p.1.1, p.2), p.1.2)) :
    ProductFibredPiece S.toTorusPresentation j (S.torusCount j) where
  base := base
  port := S.port j
  trivialization := triv.trans (S.pieceDiffeomorph j)
  collar_eq l p hp := by
    apply Subtype.ext
    refine (TorusPresentation.pieceCollar_apply S.toTorusPresentation j (S.port j l) hp).trans ?_
    rw [S.sideCollar_eq, S.sideOf_port, S.sideCollar_apply, hcol l p hp]
    rfl

def nativeHyperbolicGeometry (S : EmbeddedCutSystem W k) (j : Fin S.count)
    {C : CompactCarrier.{u}}
    (e : C.Carrier ≃ₘ⟮C.model, k.model⟯ S.Piece j)
    (g : C.InteriorGeometry ⊤) : S.cutCarrier.InteriorGeometry (S.components.piece j) :=
  transportInteriorGeometry (pieceInteriorCongr
    ((topOpensDiffeomorph (I := C.model) C.Carrier).trans
      (e.trans (S.pieceDiffeomorph j)))).symm g

structure LocalDatum (T : TorusPresentation W) (k : CarrierModel)
    (i : Fin T.components.count) where
  system : EmbeddedCutSystem (T.Component i) k
  port : Fin system.externalCount ≃ T.OwnedSide i
  port_collar : ∀ l p, p ∈ halfCollarSource →
    Subtype.val (system.fold (system.sideCollar (system.externalSide l) p)) =
      T.sideCollar (port l).val p

namespace LocalDatum

variable {T : TorusPresentation W} {i : Fin T.components.count}

def ofElementary (E : ElementaryPresentation (T.Component i))
    (port : Fin E.toTorus.externalCount ≃ T.OwnedSide i)
    (hcollar : ∀ l p, p ∈ halfCollarSource →
      (E.toTorus.external.collar l p).val = T.sideCollar (port l).val p) :
    LocalDatum T .withBoundary i where
  system := E.toPieceSystem.toCutSystem
  port := port
  port_collar l p hp := (congrArg Subtype.val
    ((E.toPieceSystem.toCutSystem.fold_sideCollar (E.toPieceSystem.externalSide l) p).trans
      (E.toPieceSystem.toCutSystem_map_collar _ _ p))).trans ((congrArg Subtype.val
    ((E.toPieceSystem.toElementaryPresentation_external_collar l p).symm.trans
      (E.toPieceSystem_external_collar l hp))).trans (hcollar l p hp))

def ofPiece (hk : T.cutCarrier.kind = k) (i : Fin T.components.count) :
    LocalDatum T k i where
  system := (T.ofPiece i).cutSystemOfKind k hk
  port := (Fintype.equivFin (T.OwnedSide i)).symm
  port_collar l p hp := by
    rw [(T.ofPiece i).cutSystemOfKind_fold_externalSide k hk l hp]
    exact T.pieceCollar_apply i _ hp

end LocalDatum

structure MixedRefinement (T : TorusPresentation W) (k : CarrierModel) where
  datum : ∀ i, LocalDatum T k i
  frozen : Finset (Fin T.components.count)
  frozen_seam : ∀ i ∈ frozen, (datum i).system.seamCount = 0
  frozen_geom : ∀ i ∈ frozen, ∀ j, ∃ (C : CompactCarrier.{u})
    (_ : C.Carrier ≃ₘ⟮C.model, k.model⟯ (datum i).system.Piece j)
    (g : C.InteriorGeometry ⊤),
      letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior ⊤)
      g.model = .hyperbolic
  cert : ∀ i, i ∉ frozen → (datum i).system.ProductCertificate

namespace MixedRefinement

variable {T : TorusPresentation W} (R : MixedRefinement T k)

def toRefinement : T.Refinement k where
  system i := (R.datum i).system
  port i := (R.datum i).port
  port_collar i := (R.datum i).port_collar

abbrev splice : TorusPresentation W := R.toRefinement.splice.toTorusPresentation

theorem splice_seam_old (d : Fin T.pairing.count) :
    R.splice.seam (finSumFinEquiv (.inr d)) = T.seam d :=
  R.toRefinement.splice_seam_old d

theorem pieceIndex_side_fst (i : Fin T.components.count)
    (c : Fin ((R.datum i).system.seamCount)) (b : Bool) :
    (R.toRefinement.pieceIndex
      (R.toRefinement.splice.side (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩))) b).1).1 =
        i := by
  have h1 : R.toRefinement.reindex
      (R.toRefinement.splice.side (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩))) b) =
        ⟨i, (R.datum i).system.side c b⟩ := by
    change R.toRefinement.reindex (R.toRefinement.sideEquiv
      (.inl (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩)), b))) = _
    rw [R.toRefinement.sideEquiv_new i c b, Equiv.apply_symm_apply]
    rfl
  exact congrArg Sigma.fst h1

theorem mem_frozen_side_of_new {i : Fin T.components.count}
    (c : Fin ((R.datum i).system.seamCount)) (hi : i ∈ R.frozen) : False := by
  have h := R.frozen_seam i hi
  exact (Fin.cast h c).elim0

end MixedRefinement

namespace MixedRefinement

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {T : TorusPresentation (NoCuts.carrier Q)}
  (R : MixedRefinement T k)

def oldSeam (d : Fin T.pairing.count) : Fin R.splice.pairing.count :=
  finSumFinEquiv (.inr d)

theorem oldSeam_injective : Injective R.oldSeam := fun _ _ h =>
  Sum.inr_injective (finSumFinEquiv.injective h)

def frozenSet : Finset (Fin R.splice.components.count) :=
  Finset.univ.filter fun J => (R.toRefinement.pieceIndex J).1 ∈ R.frozen

def protSet : Finset (Fin R.splice.pairing.count) := Finset.univ.image R.oldSeam

theorem side_mem_protSet (c : Fin R.splice.pairing.count) (b : Bool)
    (h : (R.toRefinement.splice.side c b).1 ∈ R.frozenSet) : c ∈ R.protSet := by
  obtain ⟨x, hx⟩ := (finSumFinEquiv (m := R.toRefinement.newSeamCount)
    (n := T.pairing.count)).surjective c
  subst hx
  rcases x with n | d
  · exfalso
    obtain ⟨⟨i, c'⟩, rfl⟩ := finSigmaFinEquiv.surjective n
    have hmem := (Finset.mem_filter.mp h).2
    rw [R.pieceIndex_side_fst i c' b] at hmem
    exact R.mem_frozen_side_of_new c' hmem
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

def toMixedStage : MixedStage Q where
  toTorus := R.splice
  prot := R.protSet
  frozen := R.frozenSet
  hyperbolic J hJ := by
    obtain ⟨C, e, g, hg⟩ := R.frozen_geom _ (Finset.mem_filter.mp hJ).2
      (R.toRefinement.pieceIndex J).2
    exact ⟨nativeHyperbolicGeometry R.toRefinement.splice J e g, hg⟩
  kind J := R.toRefinement.splice.torusCount J
  kind_mem J hJ := (R.cert _ fun h => hJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).kind_mem
    (R.toRefinement.pieceIndex J).2
  piece J hJ :=
    let C := R.cert _ fun h => hJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    pieceOfCertificateData R.toRefinement.splice J (C.base (R.toRefinement.pieceIndex J).2)
      (C.trivialization (R.toRefinement.pieceIndex J).2)
      (C.collar_eq (R.toRefinement.pieceIndex J).2)
  left_prot c h := R.side_mem_protSet c true h
  right_prot c h := R.side_mem_protSet c false h

theorem toMixedStage_seam (d : Fin T.pairing.count) :
    R.toMixedStage.toTorus.seam (R.oldSeam d) = T.seam d :=
  R.splice_seam_old d

def toMixedStage_protEquiv : Fin T.pairing.count ≃ R.toMixedStage.ProtSeam :=
  Equiv.ofBijective (fun d => ⟨R.oldSeam d, Finset.mem_image_of_mem _ (Finset.mem_univ d)⟩)
    ⟨fun d d' h => R.oldSeam_injective (congrArg Subtype.val h), fun c => by
      obtain ⟨d, -, hd⟩ := Finset.mem_image.mp c.2
      exact ⟨d, Subtype.ext hd⟩⟩

theorem toMixedStage_protEquiv_val (d : Fin T.pairing.count) :
    (R.toMixedStage_protEquiv d).val = R.oldSeam d := rfl

theorem toMixedStage_collarLedger (d : Fin T.pairing.count) :
    Nonempty (CollarLedger Eq (T.seam d)
      (R.toMixedStage.toTorus.seam (R.toMixedStage_protEquiv d).1)) := by
  rw [toMixedStage_protEquiv_val, toMixedStage_seam]
  exact ⟨CollarLedger.refl _⟩

end MixedRefinement

end GC.Seifert.RelativeNormalization
