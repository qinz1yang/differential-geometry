import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingPatch_CX5

set_option autoImplicit false

/-! # CH12-S55 G3a: the `hmetric` binder of `persistentModelPatch_of_dyadic_lifts_CX5` from the
order-0 `ckErr` accuracy of the discrete maps (S8: `ckErr < η_j ≤ 1`).  Window-level statement in
exactly the shape of the CX5 binder (history `n`, stage range `[first, last]`, lift `φ`). -/

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

/-- `hmetric` (CX5) for one window: if the lift `φ` of the window is `HEq` to the actual-flow map
`w t` on the open set `A`, and `ckErr_S45 … (w t) 0 < 1` there, then the physical map
`bsm ∘ φ` has `ψ^* g_t ≤ 4 t · h`. -/
theorem hmetric_window_S55 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last) (a b : ℝ)
    (ha0 : 0 ≤ a)
    (hb : b ≤ (F.tower.history n).horizon)
    (stages : ∀ t : Icc (0 : ℝ) (F.tower.history n).horizon, (t : ℝ) ∈ Ioo a b →
      first ≤ (F.tower.history n).toHistory.activeStage t ∧
        (F.tower.history n).toHistory.activeStage t ≤ last)
    (A : Set H.Carrier) (hA : IsOpen A)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (w : ∀ t : Icc (0 : ℝ) (F.tower.history n).horizon, (t : ℝ) ∈ Ioo a b →
      H.Carrier → (postStage F.observation t).Carrier)
    (hraw : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      ∀ p ∈ A, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage t) (stages t ht).1 (stages t ht).2 (φ p))
        (w t ht p))
    (hck : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      ∀ p ∈ A, ckErr_S45 H (postMetric F.observation t) (t : ℝ)⁻¹ (w t ht) 0 p < 1) :
    ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      ∀ p ∈ A, ∀ v : TangentSpace (𝓡 3) p,
        let history := (F.tower.history n).toHistory;
        let ψ := history.backwardSurvivorMap first last ordered (history.activeStage t)
          (stages t ht).1 (stages t ht).2 ∘ φ;
        (history.stageMetric (history.activeStage t) t).inner (ψ p)
          (mfderiv (𝓡 3) (𝓡 3) ψ p v) (mfderiv (𝓡 3) (𝓡 3) ψ p v) ≤
            4 * (t : ℝ) * H.metric.inner p v v := by
  intro t ht p hp v
  have htpos : 0 < (t : ℝ) := ha0.trans_lt ht.1
  have hτn : (t : ℝ) ≤ ((n : ℕ) : ℝ) := by
    have := F.tower.horizon_eq n
    exact ht.2.le.trans (this ▸ hb)
  have hpd := postData_eq_history_O3 F.observation n t t.2.1 hτn
    ((F.tower.history n).toHistory.activeStage t) rfl
  -- the physical bound on the sheet `A`, for the family `w t`
  have hf : ∀ q ∈ A, ∀ u : TangentSpace (𝓡 3) q,
      (t : ℝ)⁻¹ * (postMetric F.observation t).inner (w t ht q) (mfderiv (𝓡 3) (𝓡 3) (w t ht) q u)
        (mfderiv (𝓡 3) (𝓡 3) (w t ht) q u) ≤ 2 * H.metric.inner q u u := by
    intro q hq u
    have := pullback_inner_le_of_ckErr_S49 H (postMetric F.observation t) (t : ℝ)⁻¹ (w t ht) q
      (hck t ht q hq) u
    simpa [one_add_one_eq_two] using this
  exact physical_metric_of_heq_S49 H hpd.1.symm _ _ hpd.2.symm _ (w t ht) A hA
    (fun q hq => hraw t ht q hq) htpos hf p hp v

end GC.LongTime.Ch12
