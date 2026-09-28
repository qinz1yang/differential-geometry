import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem ObservedHistory.scalar_backwardPointTrace_eq_of_survivor_identity
    (K : ObservedHistory.{u}) (tn a w : Icc (0 : ℝ) K.horizon) (haw : a ≤ w) (hwt : w ≤ tn)
    {R : ℝ} (hR : 0 < R) {W : Opens (K.stageAt tn).Carrier}
    (h : ℝ → SmoothRiemannianMetric ThreeModel W)
    (f : (j : K.StageInterval (K.activeStage a) (K.activeStage tn)) → W →
      (K.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin K.eventCount) (hi : K.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ K.activeStage tn), ∀ x : W,
      (K.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlast : ∀ x : W, f ⟨K.activeStage tn, K.activeStage_mono (haw.trans hwt), le_rfl⟩ x = x.val)
    {σ : ℝ} (hσ : (w : ℝ) = tn + σ / R)
    (hid : ∀ j : K.StageInterval (K.activeStage a) (K.activeStage tn),
      (tn : ℝ) + σ / R ∈ K.stageDomain j.val →
        h σ = scaleMetric R hR (localPullMetric (K.stageMetric j.val ((tn : ℝ) + σ / R)) (f j)
          (hf j)))
    (x : W) (Bt : BackwardPointTrace K (K.activeStage w) (K.activeStage tn)
      (K.activeStage_mono hwt) x.val) :
    metricScalarAt (K.stageMetric (K.activeStage w) w)
        (Bt.point (K.activeStage w) le_rfl (K.activeStage_mono hwt)) =
      R * metricScalarAt (h σ) x := by
  have haw' : K.activeStage a ≤ K.activeStage w := K.activeStage_mono haw
  let B : BackwardPointTrace K (K.activeStage w) (K.activeStage tn)
      (K.activeStage_mono hwt) x.val :=
    { point := fun j hj hl => f ⟨j, haw'.trans hj, hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i (haw'.trans hi) hl x }
  let j₀ : K.StageInterval (K.activeStage a) (K.activeStage tn) :=
    ⟨K.activeStage w, haw', K.activeStage_mono hwt⟩
  have hpt : Bt.point (K.activeStage w) le_rfl (K.activeStage_mono hwt) = f j₀ x :=
    BackwardPointTrace.point_unique Bt B _ le_rfl _
  have hdom : (tn : ℝ) + σ / R ∈ K.stageDomain j₀.val := hσ ▸ K.activeStage_mem w
  rw [hpt, hid j₀ hdom, metricScalarAt_scaleMetric, metricScalarAt_localPull, ← hσ,
    mul_inv_cancel_left₀ hR.ne']

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
