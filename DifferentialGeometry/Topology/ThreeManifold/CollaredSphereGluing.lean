import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependenceAttachment
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountAbelianizationRank
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def collaredSphereGluing (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (a : BoundaryAttachment) : ConnectedClosedOrientedManifold.{u} 3 :=
  (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold

theorem collaredSphereGluing_carrier (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    (collaredSphereGluing M N c d a).Carrier =
      ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph := rfl

theorem collaredSphereGluing_boundary_eq (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) (z : S2) :
    ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph
        (c.toBallChart.boundaryMap z) =
      ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph
        (d.toBallChart.boundaryMap (a.1.toHomeomorph z)) :=
  ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph z

theorem collaredSphereGluing_jointly_surjective (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
    (x : (collaredSphereGluing M N c d a).Carrier) :
    (∃ y, ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph y = x) ∨
      ∃ y, ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph y = x :=
  ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph x

theorem preconnectedSpace_collaredSphereGluing (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    PreconnectedSpace (collaredSphereGluing M N c d a).Carrier := inferInstance

theorem orientedDiffeomorph_collaredSphereGluing_of_charts
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (collaredSphereGluing M N c d a).toClosedOrientedManifold
      (collaredSphereGluing M N c' d' a).toClosedOrientedManifold) :=
  nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts c c' d d' a

theorem orientedDiffeomorph_collaredSphereGluing_connectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (collaredSphereGluing M N c d boundaryAttachment).toClosedOrientedManifold
      (connectedSum M N).toClosedOrientedManifold) := by
  simpa only [collaredSphereGluing, connectedSum] using
    nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts c (orientedBallChart M) d
      (orientedBallChart N) boundaryAttachment

theorem orientedDiffeomorph_collaredSphereGluing_finiteConnectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (collaredSphereGluing M N c d boundaryAttachment).toClosedOrientedManifold
      (finiteConnectedSum [M, N]).toClosedOrientedManifold) := by
  simpa only [finiteConnectedSum_cons_cons, finiteConnectedSum_singleton] using
    orientedDiffeomorph_collaredSphereGluing_connectedSum M N c d

theorem orientedDiffeomorph_collaredSphereGluing_of_collarExtension
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold)
    {a a' : BoundaryAttachment} (hiso : BoundaryAttachmentIsotopic a a')
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c' d') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (collaredSphereGluing M N c d a).toClosedOrientedManifold
      (collaredSphereGluing M N c' d' a').toClosedOrientedManifold) :=
  nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts_and_attachment c c' d d' hiso hsmooth

theorem freeProduct_collaredSphereGluing (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) :
    Nonempty (FundamentalGroup (collaredSphereGluing M N c d boundaryAttachment).Carrier
        (chosenPoint (collaredSphereGluing M N c d boundaryAttachment)) ≃*
      Monoid.Coprod (FundamentalGroup M.Carrier (chosenPoint M))
        (FundamentalGroup N.Carrier (chosenPoint N))) := by
  obtain ⟨e⟩ := orientedDiffeomorph_collaredSphereGluing_connectedSum M N c d
  obtain ⟨h⟩ := fundamentalGroup_connectedSum_freeProduct M N
  refine ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e.1.toHomeomorph.toHomotopyEquiv
    (chosenPoint _) (e.1 (chosenPoint _)) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.1 (chosenPoint _))
      (chosenPoint (connectedSum M N))).trans h)⟩

structure CollaredBlock where
  block : ConnectedClosedOrientedManifold.{u} 3
  Sphere : Type u
  fintypeSphere : Fintype Sphere
  chart : Sphere → OrientedBallChart block.toClosedOrientedManifold

attribute [instance] CollaredBlock.fintypeSphere

namespace CollaredBlock

variable (B : CollaredBlock.{u})

def seamGluing (i j : B.Sphere) (a : BoundaryAttachment) :
    ConnectedClosedOrientedManifold.{u} 3 :=
  collaredSphereGluing B.block B.block (B.chart i) (B.chart j) a

theorem seamGluing_boundary_eq (i j : B.Sphere) (a : BoundaryAttachment) (z : S2) :
    ConnectedSumQuotient.inl (B.chart i).toBallChart (B.chart j).toBallChart a.1.toHomeomorph
        ((B.chart i).toBallChart.boundaryMap z) =
      ConnectedSumQuotient.inr (B.chart i).toBallChart (B.chart j).toBallChart a.1.toHomeomorph
        ((B.chart j).toBallChart.boundaryMap (a.1.toHomeomorph z)) :=
  collaredSphereGluing_boundary_eq B.block B.block (B.chart i) (B.chart j) a z

theorem orientedDiffeomorph_seamGluing_connectedSum (i j : B.Sphere) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (B.seamGluing i j boundaryAttachment).toClosedOrientedManifold
      (connectedSum B.block B.block).toClosedOrientedManifold) :=
  orientedDiffeomorph_collaredSphereGluing_connectedSum B.block B.block (B.chart i) (B.chart j)

theorem orientedDiffeomorph_seamGluing_finiteConnectedSum (i j : B.Sphere) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (B.seamGluing i j boundaryAttachment).toClosedOrientedManifold
      (finiteConnectedSum [B.block, B.block]).toClosedOrientedManifold) :=
  orientedDiffeomorph_collaredSphereGluing_finiteConnectedSum B.block B.block
    (B.chart i) (B.chart j)

theorem exists_orientedBallChart_seamGluing_left (i j k : B.Sphere) (a : BoundaryAttachment)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      (B.chart k).chart x ∉
        (B.chart i).chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ f : OrientedBallChart (B.seamGluing i j a).toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ∃ hx : (B.chart k).chart x ∉
          (B.chart i).chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
          f.toBallChart.chart x =
            ConnectedSumQuotient.inl (B.chart i).toBallChart (B.chart j).toBallChart
              a.1.toHomeomorph ⟨(B.chart k).chart x, hx⟩ :=
  ConnectedSumQuotient.exists_orientedBallChart_inl (B.chart i) (B.chart j) a (B.chart k) hdisj

theorem exists_orientedBallChart_seamGluing_right (i j k : B.Sphere) (a : BoundaryAttachment)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      (B.chart k).chart x ∉
        (B.chart j).chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ f : OrientedBallChart (B.seamGluing i j a).toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ∃ hx : (B.chart k).chart x ∉
          (B.chart j).chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
          f.toBallChart.chart x =
            ConnectedSumQuotient.inr (B.chart i).toBallChart (B.chart j).toBallChart
              a.1.toHomeomorph ⟨(B.chart k).chart x, hx⟩ :=
  ConnectedSumQuotient.exists_orientedBallChart_inr (B.chart i) (B.chart j) a (B.chart k) hdisj

theorem freeProduct_seamGluing (i j : B.Sphere) :
    Nonempty (FundamentalGroup (B.seamGluing i j boundaryAttachment).Carrier
        (chosenPoint (B.seamGluing i j boundaryAttachment)) ≃*
      Monoid.Coprod (FundamentalGroup B.block.Carrier (chosenPoint B.block))
        (FundamentalGroup B.block.Carrier (chosenPoint B.block))) :=
  freeProduct_collaredSphereGluing B.block B.block (B.chart i) (B.chart j)

theorem not_orientedDiffeomorph_seamGluing_singleton_of_isSphereTwoTimesCircleFactor
    (hS : isSphereTwoTimesCircleFactor B.block) (i j : B.Sphere) :
    ¬ Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (B.seamGluing i j boundaryAttachment).toClosedOrientedManifold
      (finiteConnectedSum [B.block]).toClosedOrientedManifold) := by
  intro h
  obtain ⟨e⟩ := B.orientedDiffeomorph_seamGluing_finiteConnectedSum i j
  obtain ⟨e'⟩ := h
  exact not_orientedDiffeomorph_cons_cons_singleton_of_isSphereTwoTimesCircleFactor hS
    ⟨e.symm.trans e'⟩

theorem isEmpty_seamIndex [IsEmpty B.Sphere] : IsEmpty (B.Sphere × B.Sphere) := inferInstance

end CollaredBlock

def standardThreeSphereBlock : CollaredBlock.{u} where
  block := standardThreeSphereLift.{u}
  Sphere := PUnit.{u + 1}
  fintypeSphere := inferInstance
  chart := fun _ => orientedBallChart standardThreeSphereLift.{u}

def sphereTwoTimesCircleBlock : CollaredBlock.{0} where
  block := sphereTwoTimesCircleLift
  Sphere := PUnit.{1}
  fintypeSphere := inferInstance
  chart := fun _ => orientedBallChart sphereTwoTimesCircleLift

theorem orientedDiffeomorph_standardThreeSphereBlock_seamGluing :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (standardThreeSphereBlock.{u}.seamGluing PUnit.unit PUnit.unit
        boundaryAttachment).toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨e⟩ := standardThreeSphereBlock.orientedDiffeomorph_seamGluing_connectedSum
    PUnit.unit PUnit.unit
  obtain ⟨f⟩ := connectedSum_sphere_left standardThreeSphereLift.{u}
  exact ⟨e.trans f⟩

theorem orientedDiffeomorph_sphereTwoTimesCircleBlock_seamGluing :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (sphereTwoTimesCircleBlock.seamGluing PUnit.unit PUnit.unit
        boundaryAttachment).toClosedOrientedManifold
      (connectedSum sphereTwoTimesCircleLift sphereTwoTimesCircleLift).toClosedOrientedManifold) :=
  sphereTwoTimesCircleBlock.orientedDiffeomorph_seamGluing_connectedSum PUnit.unit PUnit.unit

end DifferentialGeometry.Topology
