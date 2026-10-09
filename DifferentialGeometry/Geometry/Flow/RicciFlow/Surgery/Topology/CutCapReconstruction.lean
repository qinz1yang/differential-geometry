import DifferentialGeometry.Topology.ThreeManifold.CutCapConnectedSumSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

namespace GC.Surgery
open DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
universe u

structure CutCapSumData {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) where
  Group : Type u
  finite_group : Finite Group
  assign : ConnectedComponents E.capped.Carrier → Group
  factors : Group → List (ConnectedComponents E.capped.Carrier)
  sphereProducts : Group → ℕ
  mem_factors : ∀ w K, K ∈ factors w ↔ assign K = w
  nodup_factors : ∀ w, (factors w).Nodup
  nonempty_factors : ∀ w, factors w ≠ []
  reconstruct : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier
    (Σ w, (finiteConnectedSum ((factors w).map E.capped.component ++
      List.replicate (sphereProducts w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) ∞

theorem actual_cutCapSumData {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) : Nonempty (CutCapSumData E) := by
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, ⟨D⟩⟩ :=
    E.exists_diffeomorph_finiteConnectedSum_capComponents
  exact ⟨⟨W, hW, assign, L, k, hm, hn, hne, D⟩⟩

namespace CutCapSumData
variable {M Q : ClosedOrientedManifold.{u} 3} {E : SphericalCutCapTransition M Q}
  (R : CutCapSumData E)

theorem unique_component_assignment (K : ConnectedComponents E.capped.Carrier) :
    ∃! w, K ∈ R.factors w := by
  refine ⟨R.assign K, (R.mem_factors _ _).mpr rfl, ?_⟩
  intro w hw
  exact ((R.mem_factors w K).mp hw).symm

theorem disjoint_factor_lists {v w : R.Group} (h : v ≠ w) :
    List.Disjoint (R.factors v) (R.factors w) := by
  rw [List.disjoint_left]
  intro K hv hw
  exact h (((R.mem_factors v K).mp hv).symm.trans ((R.mem_factors w K).mp hw))

def componentEquiv : (Σ w : R.Group, {K // K ∈ R.factors w}) ≃
    ConnectedComponents E.capped.Carrier where
  toFun x := x.2.1
  invFun K := ⟨R.assign K, K, (R.mem_factors _ _).mpr rfl⟩
  left_inv x := by
    rcases x with ⟨w, K, hK⟩
    have h := (R.mem_factors w K).mp hK
    cases h
    rfl
  right_inv _ := rfl

theorem source_reconstructed_without_loss :
    Function.Bijective R.reconstruct := R.reconstruct.bijective

end CutCapSumData

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem smooth_event_reconstruction {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    Nonempty (CutCapSumData
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition X h)) :=
  actual_cutCapSumData _

theorem smooth_event_maps_are_actual {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    let E := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition X h
    (E.presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = X.presentation ∧
      ∀ x : X.trace.tubes.core, E.capping.coreInclusion x = X.trace.capping.coreInclusion x :=
  ⟨rfl, h.coreInclusion_eq⟩

theorem observation_event_reconstructions {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (hbfr : T.hasBoundaryFrameReversing)
    (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.toObservationTower.observe b hb).eventCount) :
    ∃ h : SmoothCutCapCompletion ((T.toObservationTower.observe b hb).event i).transition,
      Nonempty (CutCapSumData
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition
          ((T.toObservationTower.observe b hb).event i).transition h)) := by
  obtain ⟨h⟩ := T.hasCutCapCompletion_toObservationTower hbfr b hb i
  exact ⟨h, smooth_event_reconstruction _ h⟩

end GC.Surgery
