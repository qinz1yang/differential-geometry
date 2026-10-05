import DifferentialGeometry.Geometry.Neck.Normalized.Order
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Terminal.CorePresentation.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Curvature.RoundCylinder

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure AdaptedHistoricalNeck (D : OneStepIncoming.{u})
    (horn : NeckCylinder → ↥D.slab.terminalRegularOpen) (d h : ℝ) (k : ℕ) where
  d_pos : 0 < d
  d_lt_quarter : d < 1 / 4
  h_pos : 0 < h
  order_lower : 2 * ⌊d⁻¹⌋₊ + 4 ≤ k
  depth_ge : D.startTime ≤ D.endTime - 2 * h ^ 2
  chart : NeckCylinder → ↥D.slab.terminalRegularOpen
  chart_agrees_horn : ∃ W : Set NeckCylinder,
    IsOpen W ∧ Set.range (fun y : Sphere 2 => (y, (0 : ℝ))) ⊆ W ∧ Set.EqOn chart horn W
  shift : ℝ
  shift_lower : d⁻¹ + 1 < shift
  neck : NormalizedNeck D.terminal.metric d k
  chart_eq_neck : ∀ p : neckBuffer d, chart (p.1.1, shift - p.1.2) = neck.chart p
  scale_eq : neck.scale = (h ^ 2)⁻¹
  pastMetric : ℝ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer d)
  pastMetric_inner : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime,
    ∀ (x : neckBuffer d) (V W : TangentSpace NeckCylinderModel x),
      (pastMetric t).inner x V W = neck.scale *
        (D.slab.flow.base.metric t).inner (neck.chart x).1
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x V)
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x W)
  past_closeness : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime, ∀ m : ℕ, m ≤ k →
    metricDerivNormSupOn (neckClosedTest d) m (pastMetric t)
      (roundCylinderMetric.restrictOpen (neckBuffer d))
      (roundCylinderMetric.restrictOpen (neckBuffer d)) < d

def historicalNeckRecognition (τ ε d : ℝ) (k : ℕ) (Λ : ℝ) : Prop :=
  0 < d ∧ d < 1 / 4 ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k ∧
    ∃ H : ℝ, 0 < H ∧
      ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
        (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
        (h : ℝ),
        0 < h → h ≤ H → 2 * h ^ 2 < τ → Λ * (P.coreRadius ^ 2)⁻¹ < (h ^ 2)⁻¹ →
          Nonempty (AdaptedHistoricalNeck D (P.horn c e) d h k)

variable {D : OneStepIncoming.{u}}



def AdaptedHistoricalNeck.lowerOrder {d h : ℝ} {k j : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    AdaptedHistoricalNeck D horn d h j where
  d_pos := A.d_pos
  d_lt_quarter := A.d_lt_quarter
  h_pos := A.h_pos
  order_lower := hlow
  depth_ge := A.depth_ge
  chart := A.chart
  chart_agrees_horn := A.chart_agrees_horn
  shift := A.shift
  shift_lower := A.shift_lower
  neck := A.neck.lowerOrder hjk
  chart_eq_neck := A.chart_eq_neck
  scale_eq := A.scale_eq
  pastMetric := A.pastMetric
  pastMetric_inner := A.pastMetric_inner
  past_closeness := fun t ht m hm => A.past_closeness t ht m (le_trans hm hjk)

theorem AdaptedHistoricalNeck.center_scalar_eq {d h : ℝ} {k : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) :
    metricScalarAt D.terminal.metric A.neck.center = (h ^ 2)⁻¹ :=
  A.neck.scale_scalar.symm.trans A.scale_eq

theorem historicalNeckRecognition.mono_order {τ ε d Λ : ℝ} {k j : ℕ}
    (H : historicalNeckRecognition.{u} τ ε d k Λ) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    historicalNeckRecognition.{u} τ ε d j Λ := by
  obtain ⟨hd0, hd1, -, H0, hH0, hrec⟩ := H
  refine ⟨hd0, hd1, hlow, H0, hH0, fun D P c e h hh0 hhH hτ hscale => ?_⟩
  obtain ⟨A⟩ := hrec D P c e h hh0 hhH hτ hscale
  exact ⟨A.lowerOrder hjk hlow⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
