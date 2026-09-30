import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeBoundCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u

def StageFiniteDegreeBound (P : OrientedThreeStage.{u}) (N : ℕ) : Prop :=
  ∀ (U : Set P.Carrier) (x : P.Carrier), U = connectedComponent x →
    ∀ y : U, Finite (FundamentalGroup U y) → Nat.card (FundamentalGroup U y) ≤ N

def UniformHistoryDegreeBound (P : OrientedThreeStage.{u}) (g : P.Metric) (N : ℕ) : Prop :=
  ∀ (H : RetainedCoreHistory.{u}) {B : ℝ} {p : CutoffParameters} {δ ρ : ℝ},
    H.InCutoffClass g B p δ ρ →
      ∀ j : Fin (H.eventCount + 1), StageFiniteDegreeBound (H.stage j) N

theorem canonicalBallConsumer_of_stage_degree (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      StageFiniteDegreeBound P N → ∀ r : ℝ, 0 < r →
      r^4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ*r^3) ≤ riemannianVolumeMeasure I3 P.Carrier g
        (riemannianBallOf g x r) := by
  obtain ⟨κ,hκ,hball⟩ := degreeBoundCanonicalConsumer.{u} ε C1 C2 N hN
  refine ⟨κ,hκ,?_⟩
  intro P g x W hc hdegree r hr hcurv
  apply hball W hc ?_ r hr hcurv
  intro hn
  cases hA : W.alternative with
  | round whole D =>
    have hf := (spatialRound_volume_lower_div_fundamental_degree D
      ⟨x, interior_subset W.center_inside⟩).1
    exact hdegree W.domain.carrier x whole _ hf
  | neck data => exact (hn (by rw [hA]; trivial)).elim
  | cap data deep => exact (hn (by rw [hA]; trivial)).elim
  | positive whole data sec => exact (hn (by rw [hA]; trivial)).elim

end GC.GeneralFlow
