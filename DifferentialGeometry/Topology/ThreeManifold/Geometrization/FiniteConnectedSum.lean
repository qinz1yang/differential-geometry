import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteCongruence

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

def GeometrizationCertificate.connectedSum
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (C : GeometrizationCertificate M) (D : GeometrizationCertificate N) :
    GeometrizationCertificate (DifferentialGeometry.Topology.connectedSum M N) := by
  let L := C.primeData.factors
  let K := D.primeData.factors
  let e := (finiteConnectedSum_append_orientedDiffeomorph L K).some
  let f := (connectedSumOrientedTransport_holds
    (finiteConnectedSum L) M (finiteConnectedSum K) N
    ⟨C.primeData.reconstruction⟩ ⟨D.primeData.reconstruction⟩).some
  refine {
    primeData := {
      factors := L ++ K
      factors_nonempty := by
        intro h
        exact C.primeData.factors_nonempty (List.append_eq_nil_iff.mp h).1
      prime := by
        intro P hP
        rcases List.mem_append.mp hP with hP | hP
        · exact C.primeData.prime P hP
        · exact D.primeData.prime P hP
      reconstruction := e.trans f }
    geometricFactors := ?_ }
  intro i
  by_cases hi : i.val < L.length
  · have he : (L ++ K).get i = L.get ⟨i.val, hi⟩ := by
      simp only [List.get_eq_getElem, List.getElem_append_left hi]
    exact he.symm ▸ C.geometricFactors ⟨i.val, hi⟩
  · have hj : i.val - L.length < K.length := by
      have := i.isLt
      simp only [List.length_append] at this
      omega
    have he : (L ++ K).get i = K.get ⟨i.val - L.length, hj⟩ := by
      simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt hi)]
    exact he.symm ▸ D.geometricFactors ⟨i.val - L.length, hj⟩

theorem geometrizes_connectedSum
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (hM : Geometrizes M) (hN : Geometrizes N) :
    Geometrizes (connectedSum M N) := by
  obtain ⟨C⟩ := hM
  obtain ⟨D⟩ := hN
  exact ⟨C.connectedSum D⟩

theorem geometrizes_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ P ∈ L, Geometrizes P) : Geometrizes (finiteConnectedSum L) := by
  induction L with
  | nil => exact standardThreeSphereLift_geometrizes
  | cons M L ih =>
      have hM : Geometrizes M := h M (by simp)
      have hL : Geometrizes (finiteConnectedSum L) :=
        ih (fun P hP => h P (by simp [hP]))
      cases L with
      | nil => exact hM
      | cons N K => exact geometrizes_connectedSum hM hL

def MarkedFactorReconstruction (M : ConnectedClosedOrientedManifold.{u} 3)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum L).toClosedOrientedManifold M.toClosedOrientedManifold)

theorem geometrizes_of_markedFactors
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (geometry : ∀ P ∈ L, Geometrizes P)
    (reconstruction : MarkedFactorReconstruction M L) : Geometrizes M := by
  obtain ⟨f⟩ := reconstruction
  exact geometrizes_of_orientedDiffeomorph f (geometrizes_finiteConnectedSum L geometry)

end GC.Endpoint
