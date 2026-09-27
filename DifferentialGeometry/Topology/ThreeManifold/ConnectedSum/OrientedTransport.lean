import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TransportDiffeomorphism
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

set_option autoImplicit false
noncomputable section

open Set Function Manifold Topology Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u u' v v'

theorem csTransport_diffeomorph_preservesOrientation
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{u'} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (d' : OrientedBallChart N'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (Φd : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (Ψd : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N'.Carrier)
    (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
      Φd.toHomeomorph (c.toBallChart.chart x) = c'.toBallChart.chart x)
    (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
      Ψd.toHomeomorph (d.toBallChart.chart x) = d'.toBallChart.chart x)
    (hΦo : Φd.preservesOrientation M.orientation M'.orientation) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M' N' c' d' a).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  let _ := (smoothConnectedSum M N c d a).charts
  let _ := (smoothConnectedSum M N c d a).smooth
  let _ := (smoothConnectedSum M' N' c' d' a).charts
  let _ := (smoothConnectedSum M' N' c' d' a).smooth
  let S := smoothConnectedSum M N c d a
  let S' := smoothConnectedSum M' N' c' d' a
  let O := S.orientation
  let O' := S'.orientation
  let F : ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph
      ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph :=
    IsLocalDiffeomorph.diffeomorphOfBijective
      (isLocalDiffeomorph_csTransport c c' d d' a Φd Ψd hΦ hΨ)
      (csTransport c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart a.1
        Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ).bijective
  obtain ⟨x⟩ := ConnectedSumUnit.nonempty_chart_interior c
  let IL := ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1
  let IL' := ConnectedSumQuotient.interiorLeft c'.toBallChart d'.toBallChart a.1
  let Φloc : c.toBallChart.interior → c'.toBallChart.interior := fun y =>
    ⟨Φd (y : M.Carrier),
      map_mem_interior' c.toBallChart c'.toBallChart Φd.toHomeomorph hΦ y⟩
  have hcomp : (F ∘ IL) = (IL' ∘ Φloc) := by
    funext y
    exact csTransport_interiorLeft c.toBallChart c'.toBallChart d.toBallChart d'.toBallChart
      a.1 Φd.toHomeomorph Ψd.toHomeomorph hΦ hΨ y
  have hpt : IL' (Φloc x) = F (IL x) := (congrFun hcomp x).symm
  have hmfΦloc : mfderiv (𝓡 3) (𝓡 3) Φloc x
      = mfderiv (𝓡 3) (𝓡 3) (Φd : M.Carrier → M'.Carrier) (x : M.Carrier) := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡 3) (J := 𝓡 3) Φloc x]
    exact DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 3) (J := 𝓡 3)
      (Φd : M.Carrier → M'.Carrier) c.toBallChart.interior x
  have hΦd_sub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun y : c.toBallChart.interior => Φd (y : M.Carrier)) x :=
    (DifferentialGeometry.mdifferentiableAt_subtype_iff (I := 𝓡 3) (J := 𝓡 3)
      (f := (Φd : M.Carrier → M'.Carrier)) (U := c.toBallChart.interior)).mpr
      (Φd.mdifferentiable (by simp) (x : M.Carrier))
  have hΦloc_md : MDifferentiableAt (𝓡 3) (𝓡 3) Φloc x :=
    (MDifferentiableAt.subtypeVal_comp_iff (I := 𝓡 3) (J := 𝓡 3)
      (U := c'.toBallChart.interior) (f := Φloc) x).mp hΦd_sub
  let eA := (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
  let eB := (F.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv
  let eC := (S'.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (Φloc x)).toLinearEquiv
  let eD := (Φd.mfderivToContinuousLinearEquiv (by simp) (x : M.Carrier)).toLinearEquiv
  have hA : ⇑eA = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x) := by
    change ⇑((S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3) IL x)
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
  have hD : ⇑eD = ⇑(mfderiv (𝓡 3) (𝓡 3) (Φd : M.Carrier → M'.Carrier)
      (x : M.Carrier)) := by
    change ⇑((Φd.mfderivToContinuousLinearEquiv (by simp) (x : M.Carrier)).toLinearEquiv)
      = ⇑(mfderiv (𝓡 3) (𝓡 3) (Φd : M.Carrier → M'.Carrier) (x : M.Carrier))
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
    refine (congrArg (fun G : c.toBallChart.interior →
        ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph =>
        mfderiv (𝓡 3) (𝓡 3) G x v) hcomp).trans ?_
    exact mfderiv_comp_apply (x := x) (f := Φloc) (g := IL') hIL'_md hΦloc_md v
  have hO : Orientation.map (Fin 3) eA (M.orientation.orientation (x : M.Carrier))
      = O.orientation (IL x) := S.interiorLeft_preserves_orientation x
  have hO' : Orientation.map (Fin 3) eC (M'.orientation.orientation (Φloc x))
      = O'.orientation (IL' (Φloc x)) := S'.interiorLeft_preserves_orientation (Φloc x)
  have hpoint : Orientation.map (Fin 3) eB (O.orientation (IL x))
      = O'.orientation (F (IL x)) := by
    have hptOrient : (O'.orientation (IL' (Φloc x)) : Orientation ℝ csModel (Fin 3))
        = (O'.orientation (F (IL x)) : Orientation ℝ csModel (Fin 3)) := rfl
    have hΦo' : M'.orientation.orientation (Φloc x)
        = Orientation.map (Fin 3) eD (M.orientation.orientation (x : M.Carrier)) :=
      (hΦo (x : M.Carrier)).symm
    have hAeq : Orientation.map (Fin 3) eB (O.orientation (IL x))
        = Orientation.map (Fin 3) (eA.trans eB) (M.orientation.orientation (x : M.Carrier)) :=
      (congrArg (fun z => Orientation.map (Fin 3) eB z) hO.symm).trans
        (orientation_map_trans eA eB (M.orientation.orientation (x : M.Carrier))).symm
    have hDeq : Orientation.map (Fin 3) (eD.trans eC) (M.orientation.orientation (x : M.Carrier))
        = O'.orientation (F (IL x)) :=
      (orientation_map_trans eD eC (M.orientation.orientation (x : M.Carrier))).trans
        ((congrArg (fun z => Orientation.map (Fin 3) eC z) hΦo'.symm).trans
          (hO'.trans hptOrient))
    exact hAeq.trans ((congrArg (fun e => Orientation.map (Fin 3) e
      (M.orientation.orientation (x : M.Carrier))) hlin).trans hDeq)
  let _ := (smoothConnectedSum M' N' c' d' a).connected
  exact ⟨F, Diffeomorph.preservesOrientation_of_eq_at F O O' (IL x) hpoint⟩

theorem connectedSumOrientedChartTransport_holds :
    connectedSumOrientedChartTransport.{u} :=
  fun _ _ _ _ c c' d d' a Φ Ψ hΦo _ hΦ hΨ =>
    csTransport_diffeomorph_preservesOrientation c c' d d' a Φ Ψ hΦ hΨ hΦo

theorem connectedSumOrientedTransport_holds : connectedSumOrientedTransport.{u} :=
  connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport
    selfTransport_holds connectedSumOrientedChartTransport_holds

theorem connectedSumLaws_of_unit_commutative_associative
    (hunit : sphereUnitLaws.{u}) (hcomm : connectedSumCommutative.{u})
    (hassoc : connectedSumAssociative.{u}) : connectedSumLaws.{u} :=
  connectedSumLaws_of_binaryConnectedSumLaws
    (binaryConnectedSumLaws_of_unit_assoc_comm_transport hunit hcomm hassoc
      connectedSumOrientedTransport_holds)

end DifferentialGeometry.Topology
