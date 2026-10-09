import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.HistorySlicePinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PinchingTimeScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PrefixKappaEnvelope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace FILL910
universe u

theorem exists_initial_postScalarBarrier (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters),
        (∀ n (i : Fin (F.tower.history n).eventCount),
          GeometricCutoffRecord (F.tower.history n).toHistory i (p n)) →
        ∀ t : ℝ, 0 ≤ t → ∀ x : (GC.LongTime.postStage F.observation t).Carrier,
          -3 / (2 * (t + c)) ≤ metricScalarAt (GC.LongTime.postMetric F.observation t) x := by
  obtain ⟨a, ha, _, hscalar⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a / 2, by positivity, ?_⟩
  intro F p records
  apply A03b_postMetric_scalar_lower F p records (by positivity)
  intro x
  convert hscalar x using 1
  ring

theorem postMetric_curvature_bound_at_time_scale {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {a₀ t s b CR : ℝ} (ha₀ : 0 ≤ a₀)
    (ht : 0 < t) (hs : 0 < s) (hb : 0 < b) (hsb : s ≤ b * Real.sqrt t)
    (hCR : 0 ≤ CR) (x : (GC.LongTime.postStage F.observation t).Carrier)
    (hfixed : InFixedHamiltonIveyRegion (GC.LongTime.postMetric F.observation t) (a₀ + t) x)
    (hscalar : metricScalarAt (GC.LongTime.postMetric F.observation t) x ≤ CR / s ^ 2) :
    Real.sqrt (normSq0S (GC.LongTime.postMetric F.observation t) x 4
      (metricRm04At (GC.LongTime.postMetric F.observation t) x)) ≤
      2 * Real.sqrt 3 * (CR / 2 + max CR (2 * Real.exp 4 * b ^ 2)) / s ^ 2 :=
  A04b_rm_le_of_pinching_at_time_scale _ x ha₀ ht (by linarith) hs hb hsb hCR hfixed hscalar

theorem exists_initial_postPinchingCurvatureBound (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters),
        (∀ n (i : Fin (F.tower.history n).eventCount),
          GeometricCutoffRecord (F.tower.history n).toHistory i (p n)) →
        ∀ (t s b CR : ℝ), 0 < t → 0 < s → 0 < b → s ≤ b * Real.sqrt t → 0 ≤ CR →
        ∀ x : (GC.LongTime.postStage F.observation t).Carrier,
          metricScalarAt (GC.LongTime.postMetric F.observation t) x ≤ CR / s ^ 2 →
          Real.sqrt (normSq0S (GC.LongTime.postMetric F.observation t) x 4
            (metricRm04At (GC.LongTime.postMetric F.observation t) x)) ≤
            2 * Real.sqrt 3 * (CR / 2 + max CR (2 * Real.exp 4 * b ^ 2)) / s ^ 2 := by
  obtain ⟨a₀, ha₀, hpinch⟩ := A04a_postMetric_pinching P g
  refine ⟨a₀, ha₀, ?_⟩
  intro F p records t s b CR ht hs hb hsb hCR x hscalar
  exact postMetric_curvature_bound_at_time_scale F ha₀.le ht hs hb hsb hCR x
    (hpinch F p records t ht.le x) hscalar

theorem exists_oneTower_noncollapsed_envelope {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (κ ρ : ℕ → ℝ) (hκ : ∀ n, 0 < κ n)
    (hn : ∀ n, (F.tower.history n).NoncollapsedBefore (κ n) (ρ n) (n : ℝ)) :
    ∃ κ' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 < κ' t) ∧ AntitoneOn κ' (Ici 0) ∧
      ∀ n, (F.tower.history n).NoncollapsedBefore (κ' n) (ρ n) (n : ℝ) := by
  obtain ⟨κ', hpos, hanti, hle⟩ := A07_antitone_positive_envelope κ hκ
  refine ⟨κ', hpos, hanti, ?_⟩
  intro n t p r ht hr hball
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (hle n)) le_rfl).trans
    (hn n t p r ht hr hball)

end FILL910
