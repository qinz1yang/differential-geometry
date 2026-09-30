import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Commutative
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology

universe u v

private theorem orientation_map_eq_self_of_refl {A : Type*} [AddCommGroup A] [Module ℝ A]
    (e : A ≃ₗ[ℝ] A) (o : Orientation ℝ A (Fin 3)) (h : e = LinearEquiv.refl ℝ A) :
    Orientation.map (Fin 3) e o = o := by
  rw [h, Orientation.map_refl]
  rfl

theorem connectedSumCommDiffeomorph_preservesOrientation
    (M : ConnectedClosedOrientedManifold.{u} 3) (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSumCommDiffeomorph M N).preservesOrientation
      (connectedSum M N).orientation (connectedSum N M).orientation := by
  let c := (orientedBallChart M).toBallChart
  let d := (orientedBallChart N).toBallChart
  let a := boundaryAttachment
  let S := smoothConnectedSum M N (orientedBallChart M) (orientedBallChart N) a
  let S' := smoothConnectedSum N M (orientedBallChart N) (orientedBallChart M) a
  let _ := S.charts
  let _ := S.smooth
  let _ := S'.charts
  let _ := S'.smooth
  let _ := S'.connected
  let O := S.orientation
  let O' := S'.orientation
  let F : ConnectedSumQuotient c d a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient d c a.1.toHomeomorph :=
    IsLocalDiffeomorph.diffeomorphOfBijective (commHomeomorph_isLocalDiffeomorph M N)
      (ConnectedSumQuotient.commHomeomorph c d a.1.toHomeomorph).bijective
  change F.preservesOrientation O O'
  obtain ⟨x⟩ := ConnectedSumUnit.nonempty_chart_interior (orientedBallChart M)
  let IL := ConnectedSumQuotient.interiorLeft c d a.1
  let IR := ConnectedSumQuotient.interiorRight d c a.1
  have hcomp : (F ∘ IL) = IR := by
    funext y
    exact ConnectedSumQuotient.commHomeomorph_interiorLeft c d y
  have hIL_md : MDifferentiableAt (𝓡 3) (𝓡 3) IL x :=
    S.interiorLeft_localDiffeomorph.mdifferentiable (by simp) x
  have hIR_md : MDifferentiableAt (𝓡 3) (𝓡 3) IR x :=
    S'.interiorRight_localDiffeomorph.mdifferentiable (by simp) x
  have hF_md : MDifferentiableAt (𝓡 3) (𝓡 3) (F : _ → _) (IL x) :=
    F.mdifferentiable (by simp) (IL x)
  let eA := (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
  let eB := (F.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv
  let eC := (S'.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
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
  have hC : ⇑eC = ⇑(mfderiv (𝓡 3) (𝓡 3) IR x) := by
    change ⇑((S'.interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IR x)
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hlin : eA.trans eB = eC := by
    apply LinearEquiv.ext
    intro w
    change ⇑eB (⇑eA w) = ⇑eC w
    rw [hA, hB, hC]
    rw [← mfderiv_comp_apply (x := x) (f := IL) (g := (F : _ → _)) hF_md hIL_md w]
    exact congrArg (fun G : c.interior →
        ConnectedSumQuotient d c a.1.toHomeomorph =>
        mfderiv (𝓡 3) (𝓡 3) G x w) hcomp
  have hO : Orientation.map (Fin 3) eA (M.orientation.orientation (x : M.Carrier))
      = O.orientation (IL x) := S.interiorLeft_preserves_orientation x
  have hO' : Orientation.map (Fin 3) eC (M.orientation.orientation (x : M.Carrier))
      = O'.orientation (IR x) := S'.interiorRight_preserves_orientation x
  have hpoint : Orientation.map (Fin 3) eB (O.orientation (IL x))
      = O'.orientation (F (IL x)) := by
    have hptOrient : (O'.orientation (IR x) : Orientation ℝ csModel (Fin 3))
        = (O'.orientation (F (IL x)) : Orientation ℝ csModel (Fin 3)) := rfl
    have hAeq : Orientation.map (Fin 3) eB (O.orientation (IL x))
        = Orientation.map (Fin 3) (eA.trans eB)
            (M.orientation.orientation (x : M.Carrier)) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z) hO.symm).trans
        (orientation_map_trans eA eB (M.orientation.orientation (x : M.Carrier))).symm
    have hCeq : Orientation.map (Fin 3) (eA.trans eB)
        (M.orientation.orientation (x : M.Carrier)) = O'.orientation (F (IL x)) :=
      (congrArg (fun e => Orientation.map (Fin 3) e
        (M.orientation.orientation (x : M.Carrier))) hlin).trans (hO'.trans hptOrient)
    exact hAeq.trans hCeq
  exact Diffeomorph.preservesOrientation_of_eq_at F O O' (IL x) hpoint

theorem connectedSumCommutative_holds : connectedSumCommutative.{u} :=
  fun M N => ⟨connectedSumCommDiffeomorph M N,
    connectedSumCommDiffeomorph_preservesOrientation M N⟩

namespace ConnectedSumUnit

variable {M : ConnectedClosedOrientedManifold.{u} 3}
variable {c : OrientedBallChart M.toClosedOrientedManifold}
variable {d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold}
variable {a : BoundaryAttachment}

theorem quotientMap_preservesOrientation (F : UnitFilling c d a) (hcollar : BallComplementCollar F)
    (hS : BallComplementSmooth F) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    (IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_quotientMap F hcollar hS)
      (quotientMap_bijective F)).preservesOrientation
      (smoothConnectedSum M standardThreeSphereLift c d a).orientation M.orientation := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
  let S := smoothConnectedSum M standardThreeSphereLift c d a
  let _ := S.charts
  let _ := S.smooth
  let _ := S.connected
  let O := S.orientation
  let Φ : ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      M.Carrier :=
    IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_quotientMap F hcollar hS)
      (quotientMap_bijective F)
  change Φ.preservesOrientation O M.orientation
  obtain ⟨x⟩ := ConnectedSumUnit.nonempty_chart_interior c
  let IL := ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1
  have hcomp : (Φ ∘ IL) = (Subtype.val : c.toBallChart.interior → M.Carrier) := by
    funext y
    rfl
  have hIL_md : MDifferentiableAt (𝓡 3) (𝓡 3) IL x :=
    S.interiorLeft_localDiffeomorph.mdifferentiable (by simp) x
  have hΦ_md : MDifferentiableAt (𝓡 3) (𝓡 3) (Φ : _ → _) (IL x) :=
    Φ.mdifferentiable (by simp) (IL x)
  let eA := (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
  let eB := (Φ.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv
  have hA : ⇑eA = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x) := by
    change ⇑((S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv) = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x)
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hB : ⇑eB = ⇑(mfderiv (𝓡 3) (𝓡 3) (Φ : _ → _) (IL x)) := by
    change ⇑((Φ.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3) (Φ : _ → _) (IL x))
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hlin : eA.trans eB = LinearEquiv.refl ℝ (TangentSpace (𝓡 3) (x : M.Carrier)) := by
    apply LinearEquiv.ext
    intro w
    change ⇑eB (⇑eA w) = w
    rw [hA, hB]
    rw [← mfderiv_comp_apply (x := x) (f := IL) (g := (Φ : _ → _)) hΦ_md hIL_md w]
    refine (congrArg (fun G : c.toBallChart.interior → M.Carrier =>
      mfderiv (𝓡 3) (𝓡 3) G x w) hcomp).trans ?_
    exact DifferentialGeometry.mfderiv_subtype_val_apply c.toBallChart.interior x w
  have hO : Orientation.map (Fin 3) eA (M.orientation.orientation (x : M.Carrier))
      = O.orientation (IL x) := S.interiorLeft_preserves_orientation x
  have hpoint : Orientation.map (Fin 3) eB (O.orientation (IL x))
      = M.orientation.orientation (Φ (IL x)) := by
    have hAeq : Orientation.map (Fin 3) eB (O.orientation (IL x))
        = Orientation.map (Fin 3) (eA.trans eB)
            (M.orientation.orientation (x : M.Carrier)) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z) hO.symm).trans
        (orientation_map_trans eA eB (M.orientation.orientation (x : M.Carrier))).symm
    have hself : Orientation.map (Fin 3) (eA.trans eB)
        (M.orientation.orientation (x : M.Carrier))
        = M.orientation.orientation (x : M.Carrier) :=
      orientation_map_eq_self_of_refl (eA.trans eB)
        (M.orientation.orientation (x : M.Carrier)) hlin
    have hpt : M.orientation.orientation (x : M.Carrier)
        = M.orientation.orientation (Φ (IL x)) := rfl
    exact hAeq.trans (hself.trans hpt)
  exact Diffeomorph.preservesOrientation_of_eq_at Φ O M.orientation (IL x) hpoint

theorem nonempty_orientedDiffeomorph_of_unitFilling (F : UnitFilling c d a)
    (hcollar : BallComplementCollar F) (hS : BallComplementSmooth F) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (ConnectedClosedOrientedManifold.toClosedOrientedManifold
        (smoothConnectedSum M standardThreeSphereLift c d a).toConnectedClosedOrientedManifold)
      M.toClosedOrientedManifold) := by
  let _ := (smoothConnectedSum M standardThreeSphereLift.{u} c d a).charts
  let _ := (smoothConnectedSum M standardThreeSphereLift.{u} c d a).smooth
  exact ⟨⟨IsLocalDiffeomorph.diffeomorphOfBijective (isLocalDiffeomorph_quotientMap F hcollar hS)
    (quotientMap_bijective F), quotientMap_preservesOrientation F hcollar hS⟩⟩

end ConnectedSumUnit

open _root_.OrientationAssembly

theorem nonempty_orientedDiffeomorph_connectedSum_sphere_right_iso
    (X : ConnectedClosedOrientedManifold.{u} 3) (P : SphereUnitFilling.S3)
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    (h : ∃ d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold,
      ∀ u : csE3, ULift.down (d.toBallChart.chart u)
        = (SphereUnitFilling.sphereBallChart P).chart (A u)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
      X.toClosedOrientedManifold) := by
  obtain ⟨d, hd⟩ := h
  let c := orientedBallChart X
  let d' := orientedBallChart standardThreeSphereLift.{u}
  obtain ⟨e₁⟩ := ConnectedSumUnit.nonempty_orientedDiffeomorph_of_unitFilling
    (M := X) (c := c) (d := d) (a := boundaryAttachment)
    (ConnectedSumUnit.unitFillingOfSphereChartIso A P d hd c)
    (ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChartIso A P d hd c)
    (ConnectedSumUnit.ballComplementSmooth_unitFillingOfSphereChartIso A P d hd c)
  obtain ⟨Ψ, hΨo, hΨ⟩ := orientedBallChartTransport_of_ballChartTransport
    d d' (connectedBallChartTransport_holds standardThreeSphereLift.{u} d d')
  obtain ⟨e₂⟩ := csTransport_diffeomorph_preservesOrientation c c d d' boundaryAttachment
    (Diffeomorph.refl (𝓡 3) X.Carrier ∞) Ψ (fun _ _ => rfl) hΨ
    (Diffeomorph.preservesOrientation_refl X.orientation)
  exact ⟨e₂.symm.trans e₁⟩

theorem nonempty_orientedDiffeomorph_connectedSum_sphere_right_unit
    (X : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
      X.toClosedOrientedManifold) := by
  obtain ⟨P0, hP0⟩ := (NormedSpace.sphere_nonempty (E := SphereUnitFilling.E4)
    (x := 0) (r := 1)).mpr (by norm_num)
  let P : SphereUnitFilling.S3 := ⟨P0, hP0⟩
  let A₁ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3))
  let oSph : SmoothOrientation (𝓡 3) SphereUnitFilling.S3 :=
    smoothOrientationOfManifoldOrientation (𝓡 3)
      (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation)
  let oF : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
      (fun u => SphereUnitFilling.sphereChartPartialIso A₁ P u)
      (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
      (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph
  let oE : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel
  rcases smoothOrientation_eq_or_eq_neg 𝓘(ℝ, SphereUnitFilling.E3) oF oE 0 with hcase | hcase
  · have hle : oF = oE := Subtype.ext (funext hcase)
    refine nonempty_orientedDiffeomorph_connectedSum_sphere_right_iso X P A₁
      ⟨orientedBallChartLiftIso A₁ P hle, ?_⟩
    intro u
    rw [orientedBallChartLiftIso_chart]
  · let A₂ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
      (LinearIsometryEquiv.neg ℝ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    have hmfA₂ : ∀ u : SphereUnitFilling.E3,
        mfderiv 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3)
          (fun u => A₂ u) u = A₂.toContinuousLinearEquiv.toContinuousLinearMap := by
      intro u
      exact ContinuousLinearMap.mfderiv_eq (𝕜 := ℝ)
        (f := (A₂ : SphereUnitFilling.E3 →L[ℝ] SphereUnitFilling.E3)) (x := u)
    have hA₂ : ContMDiff 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3) ∞
        (fun u => A₂ u) := A₂.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    have hbA₂ : ∀ u, Bijective (mfderiv 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) u) := by
      intro u
      rw [hmfA₂ u]
      exact A₂.toContinuousLinearEquiv.bijective
    have hneg : oF = euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel) := by
      have h1 : oF = negSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) oE := by
        refine Subtype.ext (funext (fun x => ?_))
        rw [negSmoothOrientation_apply]
        exact hcase x
      exact h1.trans (negSmoothOrientation_euclideanSmoothOrientation stdOrientationModel)
    have hApull : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hA₂ hbA₂
        (euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel)) = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      rw [pullbackSmoothOrientation_eq_iff]
      rw [euclideanSmoothOrientation_apply, euclideanSmoothOrientation_apply]
      have hD : differentialEquivOfBijective 𝓘(ℝ, SphereUnitFilling.E3)
          𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hbA₂ x
          = A₂.toContinuousLinearEquiv := by
        apply ContinuousLinearEquiv.ext
        funext v
        rw [differentialEquivOfBijective_apply, hmfA₂ x]
        rfl
      rw [hD]
      exact tangentOrientationEquiv_negLinearEquiv stdOrientationModel
    have h₂ : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
        (fun u => SphereUnitFilling.sphereChartPartialIso A₂ P u)
        (SphereUnitFilling.contMDiff_sphereChartPartialIso A₂ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      have hcomp := pullbackSmoothOrientation_comp_apply 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3) (fun u : SphereUnitFilling.E3 => A₂ u)
        (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
        hA₂ (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P) hbA₂
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph x
      erw [hcomp]
      have hinner : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph = oF := rfl
      rw [hinner, hneg, hApull]
    refine nonempty_orientedDiffeomorph_connectedSum_sphere_right_iso X P A₂
      ⟨orientedBallChartLiftIso A₂ P h₂, ?_⟩
    intro u
    rw [orientedBallChartLiftIso_chart]

theorem sphereUnitLaws_holds : sphereUnitLaws.{u} :=
  ⟨fun X =>
      (connectedSumCommutative_holds standardThreeSphereLift.{u} X).elim fun e₁ =>
        (nonempty_orientedDiffeomorph_connectedSum_sphere_right_unit X).elim fun e₂ =>
          ⟨e₁.trans e₂⟩,
    fun X => nonempty_orientedDiffeomorph_connectedSum_sphere_right_unit X⟩

theorem connectedSumLaws_of_associative (hassoc : connectedSumAssociative.{u}) :
    connectedSumLaws.{u} :=
  connectedSumLaws_of_unit_commutative_associative
    sphereUnitLaws_holds connectedSumCommutative_holds hassoc

end DifferentialGeometry.Topology
