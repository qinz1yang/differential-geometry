import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.SmoothTransition
import DifferentialGeometry.Topology.Manifold.ClosedOriented.Sum

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) :
    PreservesTangentOrientation N.orientation
        (DifferentialGeometry.ManifoldOrientation.sum Q.orientation D.orientation) X.presentation ↔
      ∀ x : N.Carrier,
        ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
          Orientation.map (Fin 3)
            (LinearEquiv.ofBijective
              (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
            (N.orientation.orientation x) =
            match X.presentation x with
            | Sum.inl q => Q.orientation.orientation q
            | Sum.inr d => D.orientation.orientation d := by
  constructor
  · intro h x
    obtain ⟨hf, hfx⟩ := h.2 x
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hfx
    rw [hfx]
    cases X.presentation x <;> rfl
  · intro h
    refine ⟨X.presentation.contMDiff_toFun, fun x => ?_⟩
    have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x) :=
      (X.presentation.mfderivToContinuousLinearEquiv (by simp) x).bijective
    obtain ⟨hf, hfx⟩ := h x
    rw [Subsingleton.elim hf hbij] at hfx
    refine ⟨hbij, ?_⟩
    unfold PreservesTangentOrientationAt
    refine hfx.trans ?_
    cases X.presentation x <;> rfl

theorem SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : PreservesTangentOrientation N.orientation
      (DifferentialGeometry.ManifoldOrientation.sum Q.orientation D.orientation) X.presentation) :
    ∀ x : N.Carrier,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
        Orientation.map (Fin 3)
          (LinearEquiv.ofBijective
            (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
          (N.orientation.orientation x) =
          match X.presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d :=
  (SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation X).mp h

theorem SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ x : N.Carrier,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
        Orientation.map (Fin 3)
          (LinearEquiv.ofBijective
            (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
          (N.orientation.orientation x) =
          match X.presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d) :
    PreservesTangentOrientation N.orientation
      (DifferentialGeometry.ManifoldOrientation.sum Q.orientation D.orientation) X.presentation :=
  (SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation X).mpr h

theorem presentation_positive_self_sum (Q D : OrientedThreeStage.{u})
    (x : Q.Carrier ⊕ D.Carrier) :
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hf)
        ((Q.sum D).orientation.orientation x) =
        (Q.sum D).orientation.orientation x := by
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel
      (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x) := by
    rw [Diffeomorph.coe_refl, mfderiv_id]
    exact ⟨fun _ _ hab => hab, fun y => ⟨y, by simp⟩⟩
  refine ⟨hbij, ?_⟩
  have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
      (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hbij =
      LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.ofBijective_apply, Diffeomorph.coe_refl, mfderiv_id]
    simp
  rw [hlin]
  erw [Orientation.map_refl]
  rfl

theorem presentation_positive_refl_sum (Q D : OrientedThreeStage.{u})
    (x : Q.Carrier ⊕ D.Carrier) :
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hf)
        ((Q.sum D).orientation.orientation x) =
        Sum.elim (fun q => Q.orientation.orientation q)
          (fun d => D.orientation.orientation d) x := by
  obtain ⟨hf, hfx⟩ := presentation_positive_self_sum Q D x
  refine ⟨hf, hfx.trans ?_⟩
  cases x <;> rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
