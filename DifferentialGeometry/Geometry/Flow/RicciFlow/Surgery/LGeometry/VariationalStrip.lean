import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.BufferedControl
import DifferentialGeometry.Geometry.Measure.RiemannianBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MetricFamily
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

structure VariationalStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  finish_le_horizon : finish ≤ H.horizon
  start_lt_finish : start < finish
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

namespace VariationalStrip

noncomputable def reducedLength {H : ObservedHistory.{u}} (S : VariationalStrip H) (u : ℝ)
    (x : (H.stage 0).Carrier) : ℝ :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength
    S.metricAt S.finish S.admissible S.pole (S.finish - u) x

end VariationalStrip

structure JacobianStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  poleTime : ℝ
  start_nonneg : 0 ≤ start
  start_lt : start < poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

noncomputable def regularMinimizingSet {H : ObservedHistory.{u}}
    (g : ℝ → (H.stage 0).Metric) (t₀ : ℝ)
    (admissible regular : (ℝ → (H.stage 0).Carrier) → Prop) (p : (H.stage 0).Carrier)
    (τ : ℝ) : Set (H.stage 0).Carrier :=
  {x | ∃ γ : ℝ → (H.stage 0).Carrier,
    admissible γ ∧ regular γ ∧ γ 0 = p ∧ γ τ = x ∧
      reducedAction g t₀ τ γ = reducedLength g t₀ admissible p τ x}

def isJacobianInput : Prop :=
  ∀ _d : OldData, ∃ modul : ℝ → ℝ,
    (∀ v : ℝ, 0 < v → 0 < modul v) ∧ Monotone modul ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → v < δ → modul v < ε) ∧
    ∀ (H : ObservedHistory.{u}) (S : JacobianStrip H) (s : ℝ),
      s ∈ Ioo S.start S.poleTime → S.radius ^ 2 < S.poleTime - s →
      letI : MeasurableSpace (H.stage 0).Carrier := borel (H.stage 0).Carrier
      ∀ (V : Set (H.stage 0).Carrier), MeasurableSet V →
      V ⊆ regularMinimizingSet S.metricAt S.poleTime S.admissible S.regular S.pole
        (S.poleTime - s) →
      ∀ v : ℝ, 0 < v →
        riemannianBallVolume (S.metricAt S.poleTime) S.pole S.radius < v * S.radius ^ 3 →
          reducedVolume S.metricAt S.poleTime S.admissible S.pole (S.poleTime - s) V ≤
            ENNReal.ofReal (modul v)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
