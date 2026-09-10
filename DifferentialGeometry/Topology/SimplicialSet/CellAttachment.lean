import DifferentialGeometry.Topology.SimplicialSet.BoundaryHomeomorphism
import DifferentialGeometry.Topology.Simplex.ULift
import DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Topology

universe u

namespace Poincare.SSet

def nativeSimplexHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}) ≃ₜ
      stdSimplex ℝ (ULift.{u} (Fin (n + 1))) :=
  (TopCat.homeoOfIso (_root_.SSet.toTopSimplex.app ⦋n⦌)).trans
    (Poincare.Simplex.uliftHomeomorph (Fin (n + 1)))

def nativeBoundaryHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ≃ₜ
      Poincare.Simplex.boundary (ULift.{u} (Fin (n + 1))) :=
  (boundaryRealizationHomeomorph n).trans
    (Poincare.Simplex.boundaryUliftHomeomorph (Fin (n + 1)))

@[reassoc]
theorem nativeBoundaryHomeomorph_inclusion (n : ℕ) :
    _root_.SSet.toTop.map (_root_.SSet.boundary n).ι ≫
        (TopCat.isoOfHomeo (nativeSimplexHomeomorph.{u} n)).hom =
      (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n)).hom ≫
        Poincare.Simplex.Attachment.boundaryι := by
  apply ConcreteCategory.hom_ext
  intro x
  change Poincare.Simplex.uliftHomeomorph (Fin (n + 1))
      ((_root_.SSet.toTopSimplex.hom.app ⦋n⦌)
        ((_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) x)) =
    Poincare.Simplex.uliftHomeomorph (Fin (n + 1)) ((boundaryRealizationHomeomorph n x).val)
  exact congrArg (Poincare.Simplex.uliftHomeomorph (Fin (n + 1)))
    (boundaryRealizationHomeomorph_ambient n x).symm

theorem nativeSimplexHomeomorph_mem_boundary (n : ℕ)
    (x : _root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})) :
    x ∈ Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) ↔
      nativeSimplexHomeomorph n x ∈ Poincare.Simplex.boundary (ULift.{u} (Fin (n + 1))) := by
  have he (a : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
      nativeSimplexHomeomorph n ((_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) a) =
        (nativeBoundaryHomeomorph n a).val :=
    ConcreteCategory.congr_hom (nativeBoundaryHomeomorph_inclusion n) a
  constructor
  · rintro ⟨a, rfl⟩
    rw [he]
    exact (nativeBoundaryHomeomorph n a).property
  · intro hx
    refine ⟨(nativeBoundaryHomeomorph n).symm ⟨nativeSimplexHomeomorph n x, hx⟩, ?_⟩
    apply (nativeSimplexHomeomorph n).injective
    rw [he, Homeomorph.apply_symm_apply]


theorem isClosedEmbedding_toTop_boundaryι (n : ℕ) :
    IsClosedEmbedding (_root_.SSet.toTop.map (_root_.SSet.boundary n :
      (Δ[n] : _root_.SSet.{u}).Subcomplex).ι) := by
  have heq : (fun a ↦ (nativeSimplexHomeomorph n).symm (nativeBoundaryHomeomorph n a).val) =
      (_root_.SSet.toTop.map (_root_.SSet.boundary n : (Δ[n] : _root_.SSet.{u}).Subcomplex).ι) := by
    funext a
    apply (nativeSimplexHomeomorph n).injective
    rw [Homeomorph.apply_symm_apply]
    exact (ConcreteCategory.congr_hom (nativeBoundaryHomeomorph_inclusion n) a).symm
  rw [← heq]
  exact (nativeSimplexHomeomorph n).symm.isClosedEmbedding.comp
    (Poincare.Simplex.isClosed_boundary.isClosedEmbedding_subtypeVal.comp
      (nativeBoundaryHomeomorph n).isClosedEmbedding)

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def nativeSimplexRelativeChainIso (n : ℕ) :
    Poincare.Homology.relativeChainComplex (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ≅
      Poincare.Homology.relativeChainComplex
        (TopCat.of (stdSimplex ℝ (ULift.{u} (Fin (n + 1)))))
        (Poincare.Simplex.boundary (ULift.{u} (Fin (n + 1)))) R :=
  Poincare.Homology.relativeChainIso R (nativeSimplexHomeomorph n)
    (nativeSimplexHomeomorph_mem_boundary n)

variable {n : ℕ} {X Y : _root_.SSet.{u}}
  (g : (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶ X) (r : Δ[n] ⟶ Y)


def nativeAttachingMap :
    TopCat.of (Poincare.Simplex.boundary (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SSet.toTop.obj X :=
  (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n)).inv ≫ _root_.SSet.toTop.map g


def nativeCellMap :
    TopCat.of (stdSimplex ℝ (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SSet.toTop.obj Y :=
  (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).inv ≫ _root_.SSet.toTop.map r

@[reassoc]
theorem nativeSimplexHomeomorph_nativeCellMap :
    (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).hom ≫ nativeCellMap r =
      _root_.SSet.toTop.map r := by
  apply ConcreteCategory.hom_ext
  intro x
  change (_root_.SSet.toTop.map r)
    ((nativeSimplexHomeomorph n).symm (nativeSimplexHomeomorph n x)) = _
  rw [Homeomorph.symm_apply_apply]

variable {g r} {b : X ⟶ Y} (h : IsPushout (_root_.SSet.boundary n).ι g r b)

include h

theorem nativeAttachment_isPushout :
    IsPushout Poincare.Simplex.Attachment.boundaryι (nativeAttachingMap g)
      (nativeCellMap r) (_root_.SSet.toTop.map b) := by
  apply (h.map _root_.SSet.toTop).of_iso
    (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n))
    (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)) (Iso.refl _) (Iso.refl _)
  · exact nativeBoundaryHomeomorph_inclusion n
  · apply ConcreteCategory.hom_ext
    intro x
    change (_root_.SSet.toTop.map g) x = (_root_.SSet.toTop.map g)
      ((nativeBoundaryHomeomorph n).symm (nativeBoundaryHomeomorph n x))
    rw [Homeomorph.symm_apply_apply]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (nativeSimplexHomeomorph_nativeCellMap r).symm
  · simp

theorem isClosedEmbedding_toTop_attachment : IsClosedEmbedding (_root_.SSet.toTop.map b) :=
  Poincare.TopCat.Pushout.isClosedEmbedding_inr (nativeAttachment_isPushout h)
    Poincare.Simplex.Attachment.isClosedEmbedding_boundaryι


theorem realizedCell_mapsTo_range :
    Set.MapsTo (_root_.SSet.toTop.map r)
      (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι))
      (Set.range (_root_.SSet.toTop.map b)) := by
  rintro x ⟨a, rfl⟩
  exact ⟨(_root_.SSet.toTop.map g) a,
    (ConcreteCategory.congr_hom (h.map _root_.SSet.toTop).w a).symm⟩


def realizedCellRelativeChainMap :
    Poincare.Homology.relativeChainComplex (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ⟶
      Poincare.Homology.relativeChainComplex (_root_.SSet.toTop.obj Y)
        (Set.range (_root_.SSet.toTop.map b)) R :=
  Poincare.Homology.relativeChainMap R (_root_.SSet.toTop.map r) (realizedCell_mapsTo_range h)

theorem nativeSimplexRelativeChainIso_cellMap :
    (nativeSimplexRelativeChainIso R n).hom ≫
        Poincare.Simplex.Attachment.cellRelativeChainMap R (nativeAttachment_isPushout h) =
      realizedCellRelativeChainMap R h := by
  change Poincare.Homology.relativeChainMap R
      (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).hom
      (fun x hx ↦ (nativeSimplexHomeomorph_mem_boundary n x).mp hx) ≫
        Poincare.Homology.relativeChainMap R (nativeCellMap r)
          (Poincare.Simplex.Attachment.mapsTo_boundary_range_inr (nativeAttachment_isPushout h)) =
    Poincare.Homology.relativeChainMap R (_root_.SSet.toTop.map r) (realizedCell_mapsTo_range h)
  erw [← Poincare.Homology.relativeChainMap_comp]
  exact Poincare.Homology.relativeChainMap_congr R _ _ (nativeSimplexHomeomorph_nativeCellMap r)

theorem quasiIso_realizedCellRelativeChainMap : QuasiIso (realizedCellRelativeChainMap R h) := by
  rw [← nativeSimplexRelativeChainIso_cellMap]
  have : QuasiIso (Poincare.Simplex.Attachment.cellRelativeChainMap R
      (nativeAttachment_isPushout h)) :=
    Poincare.Simplex.Attachment.quasiIso_cellRelativeChainMap R (nativeAttachment_isPushout h)
  exact quasiIso_comp _ _

@[reassoc (attr := simp)]
theorem relativeProjection_realizedCellRelativeChainMap :
    Poincare.Homology.relativeProjection (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ≫
          realizedCellRelativeChainMap R h =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (_root_.SSet.toTop.map r) ≫
        Poincare.Homology.relativeProjection (_root_.SSet.toTop.obj Y)
          (Set.range (_root_.SSet.toTop.map b)) R :=
  Poincare.Homology.relativeProjection_chainMap R _ _

end Poincare.SSet
