import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHorizonExtension

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}}

def extendAt (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) : RetainedCoreHistory P₀ :=
  H.extendHorizon t (hend ▸ hat.le) (G.closedPrefix t hat hts) hG

def extendAtTime (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) :
    Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon :=
  ⟨t, (H.toHistory.time_nonneg _).trans hat.le, le_rfl⟩

theorem capWindowPoint_extendHorizon_iff (H : RetainedCoreHistory P₀) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) {T : ℝ}
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ∃ records' : ∀ i, GeometricCutoffRecord (H.extendHorizon T hT S hS).toHistory i p,
      (∀ p₀ δ₀ ρ₀, H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records →
        (H.extendHorizon T hT S hS).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records') ∧
      (∀ i b, ((records' i).static b).neck.scale = ((records i).static b).neck.scale) ∧
      ∀ y t D θ, (H.extendHorizon T hT S hS).CapWindowPoint records' (Fin.last _) y t D θ ↔
        H.CapWindowPoint records (Fin.last H.eventCount) y t D θ := by
  refine ⟨fun i => (records i).extendHorizon T hT S hS, fun p₀ δ₀ ρ₀ hrec => ?_,
    fun _ _ => rfl, fun y t D θ => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrec
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨j, hl, A, b, x, h1, h2, h3⟩
    exact ⟨j, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, x, h1, h2, h3⟩
  · rintro ⟨j, hl, A, b, x, h1, h2, h3⟩
    exact ⟨j, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, x, h1, h2, h3⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
