import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum

set_option autoImplicit false
noncomputable section
open Set Function Manifold Metric Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def orientedReflectChart (M : ConnectedClosedOrientedManifold.{u} 3) :
    OrientedBallChart M.opposite.toClosedOrientedManifold where
  toBallChart := reflectChart M
  preserves_orientation := (orientedBallChart M).reflect.preserves_orientation

section

variable (X Y : ConnectedClosedOrientedManifold.{u} 3)

local instance sourceCharted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
    (ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y) boundaryAttachment).charts

local instance sourceSmooth : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y) boundaryAttachment).smooth

local instance targetCharted : ChartedSpace (EuclideanSpace ℝ (Fin 3))
    (ConnectedSumQuotient (orientedReflectChart X).toBallChart (orientedReflectChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X.opposite Y.opposite (orientedReflectChart X) (orientedReflectChart Y)
    boundaryAttachment).charts

local instance targetSmooth : IsManifold (𝓡 3) ∞
    (ConnectedSumQuotient (orientedReflectChart X).toBallChart (orientedReflectChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph) :=
  (smoothConnectedSum X.opposite Y.opposite (orientedReflectChart X) (orientedReflectChart Y)
    boundaryAttachment).smooth

noncomputable def reflectDiffeomorph :
    ConnectedSumQuotient (orientedBallChart X).toBallChart (orientedBallChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
    ConnectedSumQuotient (orientedReflectChart X).toBallChart (orientedReflectChart Y).toBallChart
      boundaryAttachment.1.toHomeomorph :=
  IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_reflectHomeomorph X Y)
    (reflectHomeomorph X Y).bijective

theorem reflectDiffeomorph_preservesOrientation :
    (reflectDiffeomorph X Y).preservesOrientation
      (smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y)
        boundaryAttachment).orientation.opposite
      (smoothConnectedSum X.opposite Y.opposite (orientedReflectChart X) (orientedReflectChart Y)
        boundaryAttachment).orientation := by
  let S := smoothConnectedSum X Y (orientedBallChart X) (orientedBallChart Y) boundaryAttachment
  let S' := smoothConnectedSum X.opposite Y.opposite (orientedReflectChart X)
    (orientedReflectChart Y) boundaryAttachment
  let c := orientedBallChart X
  let d := orientedBallChart Y
  let a := boundaryAttachment
  let F : ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient (orientedReflectChart X).toBallChart (orientedReflectChart Y).toBallChart
        a.1.toHomeomorph :=
    IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_reflectHomeomorph X Y)
      (reflectHomeomorph X Y).bijective
  let _ := S'.connected
  change F.preservesOrientation S.orientation.opposite S'.orientation
  obtain ⟨x⟩ := ConnectedSumUnit.nonempty_chart_interior c
  let IL := ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1
  let IL' := ConnectedSumQuotient.interiorLeft (orientedReflectChart X).toBallChart
    (orientedReflectChart Y).toBallChart a.1
  let Φloc : c.toBallChart.interior → (orientedReflectChart X).interior := fun y =>
    ⟨(y : X.Carrier), mem_interior_reflect X y.2⟩
  have hcomp : (F ∘ IL) = (IL' ∘ Φloc) := by
    funext y
    exact reflectHomeomorph_interiorLeft X Y y
  have hpt : IL' (Φloc x) = F (IL x) := (congrFun hcomp x).symm
  have hΦd_sub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun y : c.toBallChart.interior =>
        (Diffeomorph.refl (𝓡 3) X.Carrier ∞) (y : X.Carrier)) x :=
    (DifferentialGeometry.mdifferentiableAt_subtype_iff (I := 𝓡 3) (J := 𝓡 3)
      (f := (Diffeomorph.refl (𝓡 3) X.Carrier ∞ : X.Carrier → X.Carrier))
      (U := c.toBallChart.interior)).mpr
      ((Diffeomorph.refl (𝓡 3) X.Carrier ∞).mdifferentiable (by simp) (x : X.Carrier))
  have hΦloc_md : MDifferentiableAt (𝓡 3) (𝓡 3) Φloc x :=
    (MDifferentiableAt.subtypeVal_comp_iff (I := 𝓡 3) (J := 𝓡 3)
      (U := (orientedReflectChart X).interior) (f := Φloc) x).mp hΦd_sub
  have hmfΦloc : mfderiv (𝓡 3) (𝓡 3) Φloc x
      = mfderiv (𝓡 3) (𝓡 3)
        ((Diffeomorph.refl (𝓡 3) X.Carrier ∞) : X.Carrier → X.Carrier) (x : X.Carrier) := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡 3) (J := 𝓡 3) Φloc x]
    exact DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 3) (J := 𝓡 3)
      ((Diffeomorph.refl (𝓡 3) X.Carrier ∞) : X.Carrier → X.Carrier)
      c.toBallChart.interior x
  let eA := (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
  let eB := (F.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv
  let eC := (S'.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (Φloc x)).toLinearEquiv
  let eD := ((Diffeomorph.refl (𝓡 3) X.Carrier ∞).mfderivToContinuousLinearEquiv
    (by simp) (x : X.Carrier)).toLinearEquiv
  have hA : ⇑eA = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x) := by
    change ⇑((S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x)
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hB : ⇑eB = ⇑(mfderiv (𝓡 3) (𝓡 3) (F : _ → _) (IL x)) := by
    change ⇑((F.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3) (F : _ → _) (IL x))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hC : ⇑eC = ⇑(mfderiv (𝓡 3) (𝓡 3) IL' (Φloc x)) := by
    change ⇑((S'.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (Φloc x)).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IL' (Φloc x))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hD : ⇑eD = ⇑(mfderiv (𝓡 3) (𝓡 3)
      ((Diffeomorph.refl (𝓡 3) X.Carrier ∞) : X.Carrier → X.Carrier) (x : X.Carrier)) := by
    change ⇑(((Diffeomorph.refl (𝓡 3) X.Carrier ∞).mfderivToContinuousLinearEquiv
      (by simp) (x : X.Carrier)).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3)
        ((Diffeomorph.refl (𝓡 3) X.Carrier ∞) : X.Carrier → X.Carrier) (x : X.Carrier))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hIL_md : MDifferentiableAt (𝓡 3) (𝓡 3) IL x :=
    S.interiorLeft_localDiffeomorph.mdifferentiable (by simp) x
  have hIL'_md : MDifferentiableAt (𝓡 3) (𝓡 3) IL' (Φloc x) :=
    S'.interiorLeft_localDiffeomorph.mdifferentiable (by simp) (Φloc x)
  have hF_md : MDifferentiableAt (𝓡 3) (𝓡 3) (F : _ → _) (IL x) :=
    F.mdifferentiable (by simp) (IL x)
  have hlin : eA.trans eB = eD.trans eC := by
    apply LinearEquiv.ext
    intro v
    change ⇑eB (⇑eA v) = ⇑eC (⇑eD v)
    rw [hA, hB, hC, hD, ← hmfΦloc]
    rw [← mfderiv_comp_apply (x := x) (f := IL) (g := (F : _ → _)) hF_md hIL_md v]
    rw [hcomp]
    exact mfderiv_comp_apply (x := x) (f := Φloc) (g := IL') hIL'_md hΦloc_md v
  have hO : Orientation.map (Fin 3) eA (X.orientation.orientation (x : X.Carrier))
      = S.orientation.orientation (IL x) := S.interiorLeft_preserves_orientation x
  have hO' : Orientation.map (Fin 3) eC ((X.opposite).orientation.orientation (Φloc x))
      = S'.orientation.orientation (IL' (Φloc x)) :=
    S'.interiorLeft_preserves_orientation (Φloc x)
  have hOpp : (X.opposite).orientation.orientation (Φloc x)
      = -(X.orientation.orientation (x : X.Carrier)) := rfl
  have hpoint : Orientation.map (Fin 3) eB (S.orientation.opposite.orientation (IL x))
      = S'.orientation.orientation (F (IL x)) := by
    have hAeq : Orientation.map (Fin 3) eB (S.orientation.orientation (IL x))
        = Orientation.map (Fin 3) (eA.trans eB)
            (X.orientation.orientation (x : X.Carrier)) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z) hO.symm).trans
        (orientation_map_trans eA eB (X.orientation.orientation (x : X.Carrier))).symm
    have hstep : Orientation.map (Fin 3) eD (X.orientation.orientation (x : X.Carrier))
        = X.orientation.orientation (x : X.Carrier) :=
      Diffeomorph.preservesOrientation_refl X.orientation (x : X.Carrier)
    have hDeq : Orientation.map (Fin 3) (eD.trans eC)
        (X.orientation.orientation (x : X.Carrier))
        = Orientation.map (Fin 3) eC (X.orientation.orientation (x : X.Carrier)) :=
      (orientation_map_trans eD eC (X.orientation.orientation (x : X.Carrier))).trans
        (congrArg (fun o => Orientation.map (Fin 3) eC o) hstep)
    have hmid : Orientation.map (Fin 3) eB (S.orientation.orientation (IL x))
        = Orientation.map (Fin 3) eC (X.orientation.orientation (x : X.Carrier)) :=
      hAeq.trans
        ((congrArg (fun e => Orientation.map (Fin 3) e
          (X.orientation.orientation (x : X.Carrier))) hlin).trans hDeq)
    have hL : Orientation.map (Fin 3) eB (S.orientation.opposite.orientation (IL x))
        = -Orientation.map (Fin 3) eC (X.orientation.orientation (x : X.Carrier)) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z)
        (ManifoldOrientation.opposite_orientation S.orientation (IL x))).trans
        ((Orientation.map_neg eB (S.orientation.orientation (IL x))).trans
          (congrArg Neg.neg hmid))
    have hR : S'.orientation.orientation (F (IL x))
        = -Orientation.map (Fin 3) eC (X.orientation.orientation (x : X.Carrier)) :=
      ((congrArg (S'.orientation.orientation) hpt).symm.trans hO'.symm).trans
        ((congrArg (fun z => Orientation.map (Fin 3) eC z) hOpp).trans
          (Orientation.map_neg eC (X.orientation.orientation (x : X.Carrier))))
    exact hL.trans hR.symm
  exact Diffeomorph.preservesOrientation_of_eq_at F (S.orientation.opposite) S'.orientation
    (IL x) hpoint


theorem connectedSumOpposite_holds : connectedSumOpposite.{u} := fun X Y => by
  have e₀ : ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).opposite.toClosedOrientedManifold
      (smoothConnectedSum X.opposite Y.opposite (orientedReflectChart X) (orientedReflectChart Y)
        boundaryAttachment).toConnectedClosedOrientedManifold.toClosedOrientedManifold :=
    ⟨reflectDiffeomorph X Y, reflectDiffeomorph_preservesOrientation X Y⟩
  obtain ⟨e₁⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart (M := X.opposite)
    (N := Y.opposite) (orientedReflectChart X) (orientedBallChart X.opposite)
    (orientedReflectChart Y) boundaryAttachment
  obtain ⟨e₂⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart (M := X.opposite)
    (N := Y.opposite) (orientedBallChart X.opposite) (orientedReflectChart Y)
    (orientedBallChart Y.opposite) boundaryAttachment
  exact ⟨e₀.trans (e₁.trans e₂)⟩

end

end DifferentialGeometry.Topology
