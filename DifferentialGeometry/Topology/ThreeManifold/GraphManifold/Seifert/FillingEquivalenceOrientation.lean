import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceGluing

/-!
# Actual orientation of filling comparisons

A cut map orientation at a host point transfers to its descended carrier map. On a connected
carrier this single actual orientation value determines the orientation everywhere, using the
smooth pullback orientation for possibly different source and target carrier models.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u v
namespace GC.Seifert
variable {W : CompactCarrier.{u}} {W' : CompactCarrier.{v}}

theorem fillingComparison_orientation_at (T : TorusPresentation W)
    (D : TorusPresentation W')
    (H : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (hcomm : ∀ x, F (T.cutMap x) = D.cutMap (H x))
    (x : T.cutCarrier.Carrier)
    (hH : Orientation.map (Fin 3)
      (H.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (T.cutCarrier.orientation.orientation x) = D.cutCarrier.orientation.orientation (H x)) :
    Orientation.map (Fin 3)
      (F.mfderivToContinuousLinearEquiv (by simp) (T.cutMap x)).toLinearEquiv
      (W.orientation.orientation (T.cutMap x)) =
        W'.orientation.orientation (F (T.cutMap x)) := by
  have ht := T.quotient_oriented x
  change ∃ L : TangentSpace T.cutCarrier.model x ≃ₗ[ℝ]
    TangentSpace W.model (T.cutMap x),
    (∀ v, L v = mfderiv T.cutCarrier.model W.model T.cutMap x v) ∧
      Orientation.map (Fin 3) L (T.cutCarrier.orientation.orientation x) =
        W.orientation.orientation (T.cutMap x) at ht
  obtain ⟨LT, hLT, hoT⟩ := ht
  have hd := D.quotient_oriented (H x)
  change ∃ L : TangentSpace D.cutCarrier.model (H x) ≃ₗ[ℝ]
    TangentSpace W'.model (D.cutMap (H x)),
    (∀ v, L v = mfderiv D.cutCarrier.model W'.model D.cutMap (H x) v) ∧
      Orientation.map (Fin 3) L (D.cutCarrier.orientation.orientation (H x)) =
        W'.orientation.orientation (D.cutMap (H x)) at hd
  rw [← hcomm x] at hd
  obtain ⟨LD, hLD, hoD⟩ := hd
  let LF := (F.mfderivToContinuousLinearEquiv (by simp) (T.cutMap x)).toLinearEquiv
  let LH := (H.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hfn : F ∘ T.cutMap = D.cutMap ∘ H := funext hcomm
  have hder := mfderiv_comp x (F.mdifferentiable (by simp) (T.cutMap x))
    (T.quotient_smooth.mdifferentiable (by simp) x)
  have hder' := mfderiv_comp x (D.quotient_smooth.mdifferentiable (by simp) (H x))
    (H.mdifferentiable (by simp) x)
  change mfderiv T.cutCarrier.model W'.model (D.cutMap ∘ H) x =
    (mfderiv D.cutCarrier.model W'.model D.cutMap (H x)).comp
      (mfderiv T.cutCarrier.model D.cutCarrier.model H x) at hder'
  rw [← hfn] at hder'
  have he : LT.trans LF = LH.trans LD := by
    ext v
    change LF (LT v) = LD (LH v)
    rw [hLT, hLD]
    exact (congrArg (fun L => L v) hder).symm.trans
      (congrArg (fun L => L v) hder')
  change Orientation.map (Fin 3) LF (W.orientation.orientation (T.cutMap x)) = _
  change Orientation.map (Fin 3) LT (T.cutCarrier.orientation.orientation x) =
    W.orientation.orientation (T.cutMap x) at hoT
  rw [← hoT]
  exact (orientation_map_trans_fin_three LT LF
    (T.cutCarrier.orientation.orientation x)).symm.trans
    ((congrArg (fun L => Orientation.map (Fin 3) L
      (T.cutCarrier.orientation.orientation x)) he).trans
      ((orientation_map_trans_fin_three LH LD
        (T.cutCarrier.orientation.orientation x)).trans
          ((congrArg (Orientation.map (Fin 3) LD) hH).trans hoD)))

theorem fillingDiffeomorph_preservesOrientation_of_eq_at [PreconnectedSpace W.Carrier]
    (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) (x : W.Carrier)
    (hx : Orientation.map (Fin 3)
      (F.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (W.orientation.orientation x) = W'.orientation.orientation (F x)) :
    F.preservesOrientation W.orientation W'.orientation := by
  let hbij := fun y : W.Carrier =>
    (F.mfderivToContinuousLinearEquiv (by simp) y).bijective
  let O := Manifold.manifoldOrientationPullback W.model W'.model
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    F F.contMDiff hbij W'.orientation
  have hO : ∀ y : W.Carrier, Orientation.map (Fin 3)
      (F.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
      (O.orientation y) = W'.orientation.orientation (F y) := by
    intro y
    have he : (differentialEquivOfBijective W.model W'.model F hbij y).toLinearEquiv =
        (F.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv := by
      ext v
      rfl
    exact he ▸ Manifold.orientation_map_manifoldOrientationPullback W.model W'.model
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      F F.contMDiff hbij W'.orientation y
  have he : O = W.orientation := ManifoldOrientation.eq_of_eq_at O W.orientation x
    ((Orientation.map (Fin 3)
      (F.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv).injective
        ((hO x).trans hx.symm))
  rw [he] at hO
  exact hO

theorem fillingComparison_oriented_of_cutPoint [PreconnectedSpace W.Carrier]
    (T : TorusPresentation W) (D : TorusPresentation W')
    (H : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (hcomm : ∀ x, F (T.cutMap x) = D.cutMap (H x)) (x : T.cutCarrier.Carrier)
    (hx : Orientation.map (Fin 3)
      (H.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (T.cutCarrier.orientation.orientation x) = D.cutCarrier.orientation.orientation (H x)) :
    F.preservesOrientation W.orientation W'.orientation :=
  fillingDiffeomorph_preservesOrientation_of_eq_at F (T.cutMap x)
    (fillingComparison_orientation_at T D H F hcomm x hx)

end GC.Seifert
