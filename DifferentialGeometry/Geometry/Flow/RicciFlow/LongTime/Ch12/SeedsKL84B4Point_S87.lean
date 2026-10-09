import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.G3bTracedRegion_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33

/-!
# CH12-S87 G2: (b4) at one time `w` of the window, from a trace of the centre

`b4_point_S87`: if `X₂` is a backward trace of `x0` over `[a₂, u]` with `|Rm| ≤ K/r²` on the `20r`-balls
around its points (all times in `[a₂, u]`), then for every `w ∈ [a_w, u]`, `a_w = w - τ r²`, `a₂ ≤ a_w`,
`H.isTracedRegion w (X₂ w) (2r) (τ r²) (K/r²)`.  Regular `w`: `record_seed_tracedRegion_CX2` with the
restricted trace; event `w` (`H.time (H.activeStage w) = w`): the explicit binder `hev`
(= `record_seed_tracedRegion_CX2` with `hregular` replaced by `H.time (H.activeStage t) = t`, `0 < t`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem b4_point_S87 (H : ObservedHistory.{u}) (params : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i params)
    (hev : ∀ {a t : Icc (0 : ℝ) H.horizon} {τ r K Λ : ℝ},
      0 < τ → 0 < r → 0 < K → 1 ≤ Λ → 2 * (9 * K) < Λ ^ 2 → Real.exp (9 * K * τ) < 2 →
      a.val = t.val - τ * r ^ 2 → ∀ (hat : a ≤ t), H.time (H.activeStage t) = t.val → 0 < t.val →
      ∀ {p y : (H.stageAt t).Carrier},
      y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r →
      ∀ (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y),
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2) →
      (∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ j, (records i).delta j ≤ 1 / 8646) →
      (∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ h, Λ * (records i).nominalRadius h ≤ r) →
      H.isTracedRegion t p (2 * r) (τ * r ^ 2) (K / r ^ 2))
    {τ r K Λ : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hΛ : 1 ≤ Λ)
    (hKΛ : 2 * (9 * K) < Λ ^ 2) (hexp : Real.exp (9 * K * τ) < 2)
    {a₂ a_w w u : Icc (0 : ℝ) H.horizon} (hw0 : 0 < w.val) (ha : a_w.val = w.val - τ * r ^ 2)
    (ha₂ : a₂ ≤ a_w) (haw : a_w ≤ w) (hwu : w ≤ u) {x0 : (H.stage (H.activeStage u)).Carrier}
    (X : BackwardPointTrace H (H.activeStage a₂) (H.activeStage u) (H.activeStage_mono (ha₂.trans (haw.trans hwu))) x0)
    (hRm : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a₂ ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hδ : ∀ (i : Fin H.eventCount), H.activeStage a₂ ≤ i.castSucc → i.succ ≤ H.activeStage u →
      ∀ j, (records i).delta j ≤ 1 / 8646)
    (hnom : ∀ (i : Fin H.eventCount), H.activeStage a₂ ≤ i.castSucc → i.succ ≤ H.activeStage u →
      ∀ h, Λ * (records i).nominalRadius h ≤ r) :
    H.isTracedRegion w (X.point (H.activeStage w) (H.activeStage_mono (ha₂.trans haw))
      (H.activeStage_mono hwu)) (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  let y := X.point (H.activeStage w) (H.activeStage_mono (ha₂.trans haw)) (H.activeStage_mono hwu)
  let Y := (X.restrictLast (H.activeStage_mono (ha₂.trans haw)) (H.activeStage_mono hwu)).restrictFirst
    (H.activeStage_mono ha₂) (H.activeStage_mono haw)
  have hY : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a_w ≤ v) (hvw : v ≤ w),
      Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvw) =
        X.point (H.activeStage v) (H.activeStage_mono (ha₂.trans hav))
          (H.activeStage_mono (hvw.trans hwu)) := fun v hav hvw => rfl
  have hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a_w ≤ v) (hvt : v ≤ w),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2 := by
    intro v hav hvw q hq
    rw [hY v hav hvw] at hq
    exact hRm v (ha₂.trans hav) (hvw.trans hwu) q hq
  have hcross : ∀ (i : Fin H.eventCount), H.activeStage a_w ≤ i.castSucc →
      i.succ ≤ H.activeStage w → H.activeStage a₂ ≤ i.castSucc ∧ i.succ ≤ H.activeStage u :=
    fun i hf hl => ⟨(H.activeStage_mono ha₂).trans hf, hl.trans (H.activeStage_mono hwu)⟩
  have hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w) y r :=
    mem_riemannianBallOf_self_S33 _ _ hr
  have hδ' : ∀ (i : Fin H.eventCount), H.activeStage a_w ≤ i.castSucc → i.succ ≤ H.activeStage w →
      ∀ j, (records i).delta j ≤ 1 / 8646 :=
    fun i hf hl => hδ i (hcross i hf hl).1 (hcross i hf hl).2
  have hnom' : ∀ (i : Fin H.eventCount), H.activeStage a_w ≤ i.castSucc → i.succ ≤ H.activeStage w →
      ∀ h, Λ * (records i).nominalRadius h ≤ r :=
    fun i hf hl => hnom i (hcross i hf hl).1 (hcross i hf hl).2
  by_cases hreg : H.time (H.activeStage w) < w.val
  · exact record_seed_tracedRegion_CX2 H params records hτ hr hK hΛ hKΛ hexp ha haw hreg hy Y hbound hδ' hnom'
  · have hle := H.activeStage_time_le w
    exact hev hτ hr hK hΛ hKΛ hexp ha haw (le_antisymm hle (not_lt.mp hreg)) hw0 hy Y hbound hδ' hnom'

end GC.LongTime.Ch12
