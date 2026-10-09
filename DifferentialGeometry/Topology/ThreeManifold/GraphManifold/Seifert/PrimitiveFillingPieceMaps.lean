import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingCutMaps
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

/-!
# Labelled actual piece maps for primitive filling

The full finite filling correspondence reindexes actual host and solid maps into a diffeomorphism
of the whole cut carrier. Its formula on each labelled piece is literal. A positive host map
therefore gives the real ambient orientation equality at every point of that host.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert.PrimitiveFillingPresentation

private theorem label_point_eq {C : CompactCarrier.{u}} {I : Type*}
    (S : I → TopologicalSpace.Opens C.Carrier) (x : C.Carrier) (i j : I)
    (hij : i = j) (hi : x ∈ S i) (hj : x ∈ S j) :
    (⟨i, ⟨x, hi⟩⟩ : (a : I) × S a) = ⟨j, ⟨x, hj⟩⟩ := by
  subst j
  rfl

variable {W W' : CompactCarrier.{u}} {n r : ℕ}
  (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
  (g : (i : Option (Fin n)) →
    B.presentation.components.piece (B.piece i) ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece (B'.piece i))

def labelledPieceDiffeomorph (i : Fin B.presentation.components.count) :
    B.presentation.components.piece i ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece ((B.piece.symm.trans B'.piece) i) := by
  change B.presentation.components.piece i ≃ₘ⟮B.presentation.cutCarrier.model,
    B'.presentation.cutCarrier.model⟯
      B'.presentation.components.piece (B'.piece (B.piece.symm i))
  let a := B.piece.symm i
  have hs : B.presentation.components.piece i ≤ B.presentation.components.piece (B.piece a) := by
    rw [Equiv.apply_symm_apply]
  have ht : B.presentation.components.piece (B.piece a) ≤ B.presentation.components.piece i := by
    rw [Equiv.apply_symm_apply]
  exact {
    toFun := fun x => g a (TopologicalSpace.Opens.inclusion hs x)
    invFun := fun y => TopologicalSpace.Opens.inclusion ht ((g a).symm y)
    left_inv x := by
      apply Subtype.ext
      have hh := congrArg
        (fun y : B.presentation.components.piece (B.piece a) => y.val)
        ((g a).symm_apply_apply (TopologicalSpace.Opens.inclusion hs x))
      exact hh
    right_inv := fun y => (g a).apply_symm_apply y
    contMDiff_toFun := (g a).contMDiff.comp (contMDiff_inclusion hs)
    contMDiff_invFun := (contMDiff_inclusion ht).comp (g a).symm.contMDiff }

def cutDiffeomorph : B.presentation.cutCarrier.Carrier ≃ₘ⟮B.presentation.cutCarrier.model,
    B'.presentation.cutCarrier.model⟯
      B'.presentation.cutCarrier.Carrier :=
  PrimitiveFillingComponents.diffeomorph B.presentation.components B'.presentation.components
    (B.piece.symm.trans B'.piece) (B.labelledPieceDiffeomorph B' g)

theorem cutDiffeomorph_piece (i : Option (Fin n))
    (x : B.presentation.components.piece (B.piece i)) :
    B.cutDiffeomorph B' g x.val = (g i x).val := by
  rw [cutDiffeomorph, PrimitiveFillingComponents.diffeomorph_piece]
  change (g (B.piece.symm (B.piece i)) ⟨x.val, _⟩).val = (g i x).val
  have he := label_point_eq (fun a => B.presentation.components.piece (B.piece a)) x.val
    (B.piece.symm (B.piece i)) i (B.piece.symm_apply_apply i)
    (by rw [Equiv.apply_symm_apply]; exact x.property) x.property
  exact congrArg (fun z : (a : Option (Fin n)) ×
    B.presentation.components.piece (B.piece a) => (g z.1 z.2).val) he

theorem cutDiffeomorph_image_piece (i : Option (Fin n)) :
    B.cutDiffeomorph B' g ''
      (B.presentation.components.piece (B.piece i) : Set B.presentation.cutCarrier.Carrier) =
        (B'.presentation.components.piece (B'.piece i) :
          Set B'.presentation.cutCarrier.Carrier) := by
  rw [cutDiffeomorph, PrimitiveFillingComponents.diffeomorph_image_piece]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

theorem cutDiffeomorph_host_orientation
    (ho : (g none).preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none))))
    (x : B.presentation.components.piece (B.piece none)) :
    Orientation.map (Fin 3)
      ((B.cutDiffeomorph B' g).mfderivToContinuousLinearEquiv (by simp) x.val).toLinearEquiv
      (B.presentation.cutCarrier.orientation.orientation x.val) =
        B'.presentation.cutCarrier.orientation.orientation (B.cutDiffeomorph B' g x.val) := by
  let H := B.cutDiffeomorph B' g
  have hf : H ∘ (Subtype.val : B.presentation.components.piece (B.piece none) → _) =
      Subtype.val ∘ g none := by
    funext y
    exact B.cutDiffeomorph_piece B' g none y
  have hder := DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open
    B.presentation.cutCarrier.model B'.presentation.cutCarrier.model
    (B.presentation.components.piece (B.piece none)) H H.contMDiff x
  have hder' := DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val
    B.presentation.cutCarrier.model B'.presentation.cutCarrier.model
    (B'.presentation.components.piece (B'.piece none)) (g none) (g none).contMDiff x
  rw [hf] at hder
  have he : (H.mfderivToContinuousLinearEquiv (by simp) x.val).toLinearEquiv =
      ((g none).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    ext v
    exact congrArg (fun L => L v) (hder.symm.trans hder')
  rw [B.cutDiffeomorph_piece B' g none x]
  change Orientation.map (Fin 3)
    (H.mfderivToContinuousLinearEquiv (by simp) x.val).toLinearEquiv
      (B.presentation.cutCarrier.orientation.orientation x.val) = _
  rw [he]
  exact ho x

end GC.Seifert.PrimitiveFillingPresentation
