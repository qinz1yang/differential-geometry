import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SurgeryPath_CX2
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The dimension-three scalar threshold implied by G3a's Riemann bound. -/
theorem scalar_le_nine_rm_bound_CX2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (x : P.Carrier) {K r : ℝ}
    (hRm : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ K / r ^ 2) :
    metricScalarAt g x ≤ (9 * K) / r ^ 2 := by
  have hs := scalar_abs_le_rm g x
  change |metricScalarAt g x| ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * _ at hs
  norm_num [ThreeSpace] at hs
  calc
    metricScalarAt g x ≤ |metricScalarAt g x| := le_abs_self _
    _ ≤ 9 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) := hs
    _ ≤ 9 * (K / r ^ 2) := mul_le_mul_of_nonneg_left hRm (by norm_num)
    _ = (9 * K) / r ^ 2 := by ring

/-- Uniform surgery avoidance for paths in the late half interval, using
exactly the actual records and nominal-radius clause of W2. -/
theorem exists_recent_path_lift_CX2
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (K Λ₀ : ℝ) :
    ∃ T Λ : ℝ, 0 < T ∧ 1 ≤ Λ ∧ Λ₀ ≤ Λ ∧
      ∀ t : ℝ, T ≤ t →
      ∀ n (i : Fin (F.tower.history n).toHistory.eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ r : ℝ, 0 < r → (∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
      ∀ γ : ℝ → ((F.tower.history n).stage i.succ).Carrier,
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc (0 : ℝ) 1) →
        (∀ s ∈ Icc (0 : ℝ) 1,
          Real.sqrt (normSq0S ((F.tower.history n).toHistory.event i).outputMetric (γ s) 4
            (metricRm04At ((F.tower.history n).toHistory.event i).outputMetric (γ s))) ≤ K / r ^ 2) →
      ∀ x : ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen,
        ((F.tower.history n).toHistory.event i).RegularCrossing x.val (γ 0) →
        ∃ η : ℝ → ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen,
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 η (Icc (0 : ℝ) 1) ∧ η 0 = x ∧
          (∀ s ∈ Icc (0 : ℝ) 1,
            ((F.tower.history n).toHistory.event i).RegularCrossing (η s).val (γ s)) ∧
          metricPathELength ((F.tower.history n).toHistory.event i).terminal.metric η 0 1 =
            metricPathELength ((F.tower.history n).toHistory.event i).outputMetric γ 0 1 ∧
          ∀ s ∈ Icc (0 : ℝ) 1,
            Real.sqrt (normSq0S ((F.tower.history n).toHistory.event i).terminal.metric (η s) 4
              (metricRm04At ((F.tower.history n).toHistory.event i).terminal.metric (η s))) ≤ K / r ^ 2 := by
  obtain ⟨T, hT, hδ⟩ := eventually_recent_cutoff_accuracy_CX2 Hp hdec
  obtain ⟨Λ, hΛ, hΛ₀, hKΛ⟩ := exists_cutoff_multiplier_CX2 (9 * K) Λ₀
  refine ⟨T, Λ, hT, hΛ, hΛ₀, ?_⟩
  intro t ht n i hi r hr hnom γ hγ hRm x hcross
  obtain ⟨η, hη, hη0, hcrossη, hlength⟩ := lift_outgoing_path_CX2 (Hp.records n i) hr hΛ hKΛ (hδ t ht n i hi) hnom γ hγ
    (fun s hs => scalar_le_nine_rm_bound_CX2 _ _ _ (hRm s hs)) x hcross
  refine ⟨η, hη, hη0, hcrossη, hlength, ?_⟩
  intro s hs
  have heq := MetricCutCapEvent.RegularCrossing.rmNormSq_eq
    ((F.tower.history n).toHistory.event i) (p := η s) (hcrossη s hs)
  exact (congrArg Real.sqrt heq).trans_le (hRm s hs)

end GC.LongTime.Ch12
