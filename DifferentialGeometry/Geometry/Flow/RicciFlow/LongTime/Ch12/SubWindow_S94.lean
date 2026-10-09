import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubPoint_S94

/-!
# CH12-S94 G2 (c1): `hsub86N_window_S94`, the slice-wise part of `hsub86N_S94`

The scalar trace on `[u - (τ₁+τ₂) r0², u]` (`hsub86N_trace_S87`) and the per-`w` step (`hsub86N_point_S94`)
for one slice `s`, one time `u`, one centre `x0`, with the constants as explicit numeric premises.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hsub86N_window_S94 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    {C : ℝ}
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
    {A A' Cb Q κ₀ K Λs τs τ₁ τ₂ C₁ : ℝ} (hA0 : 0 < A) (hAA' : A < A') (hA'1 : 1 ≤ A') (hCb : 0 < Cb)
    (hCbC : (Ctime : ℝ) ≤ Cb) (hτ₁def : τ₁ = 1 / (64 * Cb * A')) (hQdef : Q = 32 * Hp.C2 * A') (hQ : 0 < Q)
    (hκdef : κ₀ = 1 / (10 * (Q + 1))) (hκ : 0 < κ₀) (hKdef : K = C * Q * κ₀ ^ 2 / 4) (hK : 0 < K)
    (hΛs1 : 1 ≤ Λs) (hΛsK : 2 * (9 * K) < Λs ^ 2) (hτs : 0 < τs) (hexp : Real.exp (9 * K * τs) < 2)
    (hτ₂def : τ₂ = τs * κ₀ ^ 2 / 4) (hτ₂ : 0 < τ₂) (hτ₂le : τ₂ ≤ τ₁) (hC₁A : 8 * A' + 1 ≤ C₁)
    (hC₁Λ : 2 * Λs / κ₀ ≤ C₁)
    (s : RegularSlice F.observation) (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
    (hu0 : 0 < (u : ℝ)) (hus : (u : ℝ) ≤ s.time)
    (hreg : (sliceTowerHistory_CX2 s).time ((sliceTowerHistory_CX2 s).activeStage u) < (u : ℝ))
    (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) {r0 : ℝ} (hr0 : 0 < r0)
    (hrad : r0 ≤ Hp.parameters.neckRadius u) (hr0A : r0 ^ 2 ≤ A')
    (hLu : (τ₁ + τ₂) * r0 ^ 2 ≤ (u : ℝ) / 2)
    (hrcI : ∀ t : ℝ, (u : ℝ) / 2 < t → Hp.parameters.recenterConstant * δ t ≤ 1 / 2)
    (htop : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage u) u) x0 ≤ 4 * A / r0 ^ 2)
    (hδ : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc ((u : ℝ) / 2) u →
      ∀ j, (Hp.records n i).delta j ≤ 1 / 8646)
    (hnom : ∀ m (i : Fin (F.tower.history m).eventCount),
      (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - (τ₁ + τ₂) * r0 ^ 2) u →
      ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0) :
    ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hat : a ≤ u)
      (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
        ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
        ((sliceTowerHistory_CX2 s).activeStage_mono hat) x0),
      (a : ℝ) = (u : ℝ) - τ₁ * r0 ^ 2 ∧
      ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
        (sliceTowerHistory_CX2 s).isTracedRegion w
          (X.point ((sliceTowerHistory_CX2 s).activeStage w)
            ((sliceTowerHistory_CX2 s).activeStage_mono haw)
            ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
          (κ₀ * r0) (τ₂ * r0 ^ 2) (C * Q * (r0 ^ 2)⁻¹) := by
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hτ₁ : 0 < τ₁ := lt_of_lt_of_le hτ₂ hτ₂le
  obtain ⟨a₂, ha₂, ha₂u, X₂, hX₂⟩ := hsub86N_trace_S87 Hp hP2 hscale s u hu0 hreg x0 hr0 hrad
    (A := A) (A' := A') (Cb := Cb) (β := r0 ^ 2 / (8 * A')) (C₁ := C₁) (τ₁ := τ₁) (τ₂ := τ₂) hA0
    hAA' hA'1 hCb hCbC rfl hτ₁def hτ₂ hτ₂le hC₁A hLu hrcI htop hnom
  have h1 : 0 < τ₁ * r0 ^ 2 := mul_pos hτ₁ hr2
  have h2 : 0 < τ₂ * r0 ^ 2 := mul_pos hτ₂ hr2
  have hL2 : (τ₁ + τ₂) * r0 ^ 2 = τ₁ * r0 ^ 2 + τ₂ * r0 ^ 2 := by ring
  have hau₁ : (u : ℝ) - τ₁ * r0 ^ 2 ≤ u := by linarith
  have hnn₁ : 0 ≤ (u : ℝ) - τ₁ * r0 ^ 2 := by linarith [u.2.1]
  let a₁ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(u : ℝ) - τ₁ * r0 ^ 2, hnn₁, hau₁.trans u.2.2⟩
  have ha₂a₁ : a₂ ≤ a₁ := show (a₂ : ℝ) ≤ u - τ₁ * r0 ^ 2 by rw [ha₂]; linarith
  have ha₁u : a₁ ≤ u := hau₁
  refine ⟨a₁, ha₁u, X₂.restrictFirst ((sliceTowerHistory_CX2 s).activeStage_mono ha₂a₁)
    ((sliceTowerHistory_CX2 s).activeStage_mono ha₁u), rfl, ?_⟩
  intro w haw hwu
  exact hsub86N_point_S94 Hp hCrm hA'1 hQdef hQ hκdef hκ hKdef hK hΛs1 hΛsK hτs hexp hτ₂def hτ₂ hτ₂le
    hC₁Λ s u hu0 hus hr0 hrad hr0A hLu hδ hnom ha₂ ha₂u X₂ hX₂ w (ha₂a₁.trans haw) hwu haw

end GC.LongTime.Ch12
