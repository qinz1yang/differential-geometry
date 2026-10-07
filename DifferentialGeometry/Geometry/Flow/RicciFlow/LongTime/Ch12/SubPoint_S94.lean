import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubTrace_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84B4Point_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubArith_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84EventHev_S94

/-!
# CH12-S94 G2 (b): `hsub86N_point_S94`, the per-`w` step of `hsub86N_S94`

For `w ∈ [u - τ₁ r0², u]`: `|Rm| ≤ C (2 C2 Mb)` on the `20 r`-balls around the points of the trace `X₂` of
`x0` (`rm_ball_bound_S87` with `Mb = 16 A'/r0²`, `r = κ₀ r0/2`, `SubArith_S87`), cutoff accuracy and
nominal radii on the window, then `b4_point_S87` (regular `w`: CX2 `record_seed`; event `w`: `hev_S94`),
and the final rewrite to `(κ₀ r0, τ₂ r0², C Q (r0²)⁻¹)`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hsub86N_point_S94 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) {C : ℝ}
    (hCrm : ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (v : ℝ) ≤ s.time →
      ∀ (x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier)
        (Mb : ℝ), 1 ≤ Mb →
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ Mb →
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x)) ≤ C * Mb)
    {A' Q κ₀ K Λs τs τ₁ τ₂ C₁ : ℝ} (hA'1 : 1 ≤ A') (hQdef : Q = 32 * Hp.C2 * A') (hQ : 0 < Q)
    (hκdef : κ₀ = 1 / (10 * (Q + 1))) (hκ : 0 < κ₀) (hKdef : K = C * Q * κ₀ ^ 2 / 4) (hK : 0 < K)
    (hΛs1 : 1 ≤ Λs) (hΛsK : 2 * (9 * K) < Λs ^ 2) (hτs : 0 < τs) (hexp : Real.exp (9 * K * τs) < 2)
    (hτ₂def : τ₂ = τs * κ₀ ^ 2 / 4) (hτ₂ : 0 < τ₂) (hτ₂le : τ₂ ≤ τ₁) (hC₁Λ : 2 * Λs / κ₀ ≤ C₁)
    (s : RegularSlice F.observation) (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
    (hu0 : 0 < (u : ℝ)) (hus : (u : ℝ) ≤ s.time) {r0 : ℝ} (hr0 : 0 < r0)
    (hrad : r0 ≤ Hp.parameters.neckRadius u) (hr0A : r0 ^ 2 ≤ A')
    (hLu : (τ₁ + τ₂) * r0 ^ 2 ≤ (u : ℝ) / 2)
    (hδ : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc ((u : ℝ) / 2) u →
      ∀ j, (Hp.records n i).delta j ≤ 1 / 8646)
    (hnom : ∀ m (i : Fin (F.tower.history m).eventCount),
      (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - (τ₁ + τ₂) * r0 ^ 2) u →
      ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0)
    {a₂ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon} (ha₂ : (a₂ : ℝ) = (u : ℝ) - (τ₁ + τ₂) * r0 ^ 2)
    (hau : a₂ ≤ u) {x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier}
    (X : BackwardPointTrace (sliceTowerHistory_CX2 s) ((sliceTowerHistory_CX2 s).activeStage a₂)
      ((sliceTowerHistory_CX2 s).activeStage u) ((sliceTowerHistory_CX2 s).activeStage_mono hau) x0)
    (hX : ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a₂ ≤ w) (hwu : w ≤ u),
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage w) w)
        (X.point ((sliceTowerHistory_CX2 s).activeStage w)
          ((sliceTowerHistory_CX2 s).activeStage_mono haw)
          ((sliceTowerHistory_CX2 s).activeStage_mono hwu)) ≤ 16 * A' / r0 ^ 2)
    (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a₂ ≤ w) (hwu : w ≤ u)
    (hw1 : (u : ℝ) - τ₁ * r0 ^ 2 ≤ w) :
    (sliceTowerHistory_CX2 s).isTracedRegion w
      (X.point ((sliceTowerHistory_CX2 s).activeStage w)
        ((sliceTowerHistory_CX2 s).activeStage_mono haw)
        ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
      (κ₀ * r0) (τ₂ * r0 ^ 2) (C * Q * (r0 ^ 2)⁻¹) := by
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hτ₁ : 0 < τ₁ := lt_of_lt_of_le hτ₂ hτ₂le
  have hτr : 0 < τ₂ * r0 ^ 2 := by positivity
  have hrpos : 0 < κ₀ * r0 / 2 := by positivity
  have hMb : 1 ≤ 16 * A' / r0 ^ 2 := arith_Mb_S87 hr0 hr0A
  have hL2 : (τ₁ + τ₂) * r0 ^ 2 = τ₁ * r0 ^ 2 + τ₂ * r0 ^ 2 := by ring
  -- the new left endpoint a_w = w - τ₂ r0²
  have hawnn : 0 ≤ (w : ℝ) - τ₂ * r0 ^ 2 := by
    have := a₂.2.1
    linarith
  let aw : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(w : ℝ) - τ₂ * r0 ^ 2, hawnn, by linarith [w.2.2]⟩
  have ha : aw.val = w.val - τs * (κ₀ * r0 / 2) ^ 2 := by
    change (w : ℝ) - τ₂ * r0 ^ 2 = _
    rw [arith_depth_S87 hτ₂def]
  have ha₂aw : a₂ ≤ aw := show (a₂ : ℝ) ≤ (w : ℝ) - τ₂ * r0 ^ 2 by rw [ha₂]; linarith
  have hawle : aw ≤ w := show (w : ℝ) - τ₂ * r0 ^ 2 ≤ w by linarith
  have hw0 : 0 < (w : ℝ) := by linarith
  have hRm : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a₂ ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v)
        (X.point ((sliceTowerHistory_CX2 s).activeStage v)
          ((sliceTowerHistory_CX2 s).activeStage_mono hav)
          ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (20 * (κ₀ * r0 / 2)),
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ K / (κ₀ * r0 / 2) ^ 2 := by
    intro v hav hvu q hq
    have hvs : (v : ℝ) ≤ s.time := (show (v : ℝ) ≤ u from hvu).trans hus
    have hNM : (Hp.parameters.neckRadius v ^ 2)⁻¹ ≤ 16 * A' / r0 ^ 2 := by
      have h := Hp.radius_antitone (Set.mem_Ici.mpr v.2.1) (Set.mem_Ici.mpr hu0.le) hvu
      have h1 : (Hp.parameters.neckRadius v ^ 2)⁻¹ ≤ (r0 ^ 2)⁻¹ :=
        inv_anti₀ hr2 (pow_le_pow_left₀ hr0.le (hrad.trans h) 2)
      refine h1.trans ?_
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hr2]
      linarith
    have h := rm_ball_bound_S87 Hp hCrm s v hvs hMb hNM (arith_ball_S87 hQdef hκdef hQ hr0) _
      (hX v hav hvu) q hq
    rwa [arith_rm_S87 hQdef hKdef hκ hr0] at h
  have hwin : ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount),
      (sliceTowerHistory_CX2 s).activeStage a₂ ≤ i.castSucc →
      i.succ ≤ (sliceTowerHistory_CX2 s).activeStage u →
      ((sliceTowerHistory_CX2 s).time i.succ ∈ Icc ((u : ℝ) / 2) u ∧
        (sliceTowerHistory_CX2 s).time i.succ ∈ Icc ((u : ℝ) - (τ₁ + τ₂) * r0 ^ 2) u) := by
    intro i hf hl
    obtain ⟨h1, h2⟩ := window_event_S87 (sliceTowerHistory_CX2 s) i hf hl
    rw [ha₂] at h1
    exact ⟨⟨by linarith, h2⟩, ⟨h1.le, h2⟩⟩
  have hδ' : ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount),
      (sliceTowerHistory_CX2 s).activeStage a₂ ≤ i.castSucc →
      i.succ ≤ (sliceTowerHistory_CX2 s).activeStage u →
      ∀ j, (Hp.records (sliceTowerIndex_CX2 s) i).delta j ≤ 1 / 8646 :=
    fun i hf hl => hδ (sliceTowerIndex_CX2 s) i (hwin i hf hl).1
  have hnom' : ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount),
      (sliceTowerHistory_CX2 s).activeStage a₂ ≤ i.castSucc →
      i.succ ≤ (sliceTowerHistory_CX2 s).activeStage u →
      ∀ h, Λs * (Hp.records (sliceTowerIndex_CX2 s) i).nominalRadius h ≤ κ₀ * r0 / 2 := by
    intro i hf hl h
    have hn := hnom (sliceTowerIndex_CX2 s) i (hwin i hf hl).2 h
    have hnp := (Hp.records (sliceTowerIndex_CX2 s) i).nominal_pos h
    have hΛ : Λs ≤ κ₀ * C₁ / 2 := by
      have := (div_le_iff₀ hκ).mp hC₁Λ
      linarith
    calc Λs * (Hp.records (sliceTowerIndex_CX2 s) i).nominalRadius h
        ≤ (κ₀ * C₁ / 2) * (Hp.records (sliceTowerIndex_CX2 s) i).nominalRadius h :=
          mul_le_mul_of_nonneg_right hΛ hnp.le
      _ = κ₀ / 2 * (C₁ * (Hp.records (sliceTowerIndex_CX2 s) i).nominalRadius h) := by ring
      _ ≤ κ₀ / 2 * r0 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = κ₀ * r0 / 2 := by ring
  have hb := b4_point_S87 (sliceTowerHistory_CX2 s) Hp.parameters (Hp.records (sliceTowerIndex_CX2 s))
    (hev_S94 Hp (sliceTowerIndex_CX2 s)) hτs hrpos hK hΛs1 hΛsK hexp hw0 ha ha₂aw hawle hwu X
    hRm hδ' hnom'
  have e1 : 2 * (κ₀ * r0 / 2) = κ₀ * r0 := by ring
  rw [e1, arith_depth_S87 hτ₂def, arith_out_S87 hKdef hκ hr0] at hb
  exact hb

end GC.LongTime.Ch12
