import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84SlabBarrierIco_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84CapExclude_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84TraceBuild_S74

/-!
# CH12-S74 G2 (b1'), the one-event step of the backward trace with the single global barrier

`event_step_S74`: the `hstep` of `exists_backwardTrace_of_step_S74` for
`Good j q := ∀ t ∈ H.stageDomain j, a0 ≤ t → t ≤ u → metricScalarAt (H.stageMetric j t) q ≤ (β - 2C (u - t))⁻¹`
(window start `a0`): a point `q` of the output stage of event `i` whose initial scalar satisfies the
barrier has a regular-crossing preimage (cap exclusion, `(β - 2C(u - a0))⁻¹ < C₁²/(4 r0²)`) with the
barrier on the whole part `[a0, time i.succ)` of the slab (terminal limit = output scalar, slab barrier
from `σ₀ = u - time i.succ` restarted at `c = max a0 (time i.castSucc)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace GC.LongTime.Ch12

universe u

theorem event_step_S74 {H : ObservedHistory.{u}} (i : Fin H.eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {C₁ r0 M β C u a0 : ℝ} (hC : 0 < C) (hβ : 0 < β)
    (hβM : β * M < 1) (hC₁ : 0 < C₁) (hr0 : 0 < r0)
    (hscale : ∀ (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hnom : ∀ h, C₁ * R.nominalRadius h ≤ r0)
    {θ : ℝ → ℝ} (hθ : ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), θ t ≤ M)
    (hP2 : ∀ y : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      θ t < (H.event i).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t y ^ 2)
    (hu : H.time i.succ ≤ u) (ha0 : a0 < H.time i.succ) (hden : 0 < β - 2 * C * (u - a0))
    (hcapB : (β - 2 * C * (u - a0))⁻¹ < C₁ ^ 2 / (4 * r0 ^ 2))
    (q : (H.stage i.succ).Carrier)
    (hq : metricScalarAt (H.initialMetric i.succ) q ≤ (β - 2 * C * (u - H.time i.succ))⁻¹) :
    ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' q ∧
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ), a0 ≤ t →
        metricScalarAt (H.stageMetric i.castSucc t) p' ≤ (β - 2 * C * (u - t))⁻¹ := by
  have hlt : H.time i.castSucc < H.time i.succ := H.time_strictMono (Fin.castSucc_lt_succ (i := i))
  have hout : metricScalarAt (H.event i).outputMetric q ≤ (β - 2 * C * (u - H.time i.succ))⁻¹ := by
    rw [H.event_output i]; exact hq
  have hmono : (β - 2 * C * (u - H.time i.succ))⁻¹ ≤ (β - 2 * C * (u - a0))⁻¹ := by
    apply inv_anti₀ hden
    have : 2 * C * (u - H.time i.succ) ≤ 2 * C * (u - a0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  obtain ⟨p', hp'⟩ := exists_regularCrossing_of_scalar_lt_S74 R hC₁ hr0 hscale hrc hnom q
    (lt_of_le_of_lt (hout.trans hmono) hcapB)
  refine ⟨p', hp', fun t ht hat => ?_⟩
  have hL := flow_scalar_tendsto_of_regularCrossing_S74 (H.event i) hp'
  have hc1 : H.time i.castSucc ≤ max a0 (H.time i.castSucc) := le_max_right _ _
  have hc2 : max a0 (H.time i.castSucc) < H.time i.succ := max_lt ha0 hlt
  have hbar := incoming_scalar_backward_barrier_Ico_S74 (H.event i).incoming p' hC (θ := θ)
    (hP2 p') (c := max a0 (H.time i.castSucc)) hc1 hc2 hβ hβM (σ0 := u - H.time i.succ)
    (by linarith) hθ
    (by
      have h1 : u - H.time i.succ + (H.time i.succ - max a0 (H.time i.castSucc)) =
          u - max a0 (H.time i.castSucc) := by ring
      rw [h1]
      have : 2 * C * (u - max a0 (H.time i.castSucc)) ≤ 2 * C * (u - a0) :=
        mul_le_mul_of_nonneg_left (by linarith [le_max_left a0 (H.time i.castSucc)]) (by positivity)
      linarith)
    hL hout t ⟨max_le hat ht.1, ht.2⟩
  have heq : u - H.time i.succ + (H.time i.succ - t) = u - t := by ring
  rw [heq] at hbar
  have hs : metricScalarAt (H.stageMetric i.castSucc t) p' =
      (H.event i).incoming.flow.scalar t p' := by
    simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rfl
  rw [hs]
  exact hbar

end GC.LongTime.Ch12
