import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubWindow_S94
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubConsts_S94

/-!
# CH12-S94 G2 (c): `hsub86N_S94` (tower-history window form; `hscale` the only explicit input)

Assembly: constants (`hsub86N_consts_S94`) + the slice-wise part `hsub86N_window_S94` (scalar trace
`hsub86N_trace_S87`, per-`w` step `hsub86N_point_S94`, which uses the proved event-time seed `hev_S94`).
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

theorem hsub86N_S94 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z)) :
  ∃ ε C₁ K τ₁ τ₂ Λ T κ₀ : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
    τ₁ + τ₂ ≤ Λ ∧ 0 < T ∧ 0 < κ₀ ∧
    ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
    (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
    ∀ (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r0 : ℝ), 0 < r0 →
      r0 ≤ Hp.parameters.neckRadius u →
      (∀ m (i : Fin (F.tower.history m).eventCount),
        (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r0 ^ 2) u →
        ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0) →
      (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) x0 r0,
        SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r0 ^ 2)⁻¹)) →
      (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) x0 (r0 / 2),
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 / 2 →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
            ballVolume ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
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
            (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) := by
  obtain ⟨A, hA1, hAtop⟩ := top_scalar_le_S87 Hp
  obtain ⟨C, hCpos, hCrm⟩ := rm_bound_prefix_S74 Hp
  obtain ⟨T₀, hT₀, hδT⟩ := eventually_recent_cutoff_accuracy_CX2 Hp hdec
  have hκrc : 0 < Hp.parameters.recenterConstant := by
    linarith [Hp.parameters.recenterConstant_ge_four]
  obtain ⟨B, hB⟩ := hdec (1 / (2 * Hp.parameters.recenterConstant)) (by positivity)
  obtain ⟨rbar, hrbardef⟩ : ∃ rbar : ℝ, rbar = Hp.parameters.neckRadius 0 := ⟨_, rfl⟩
  have hrbar : 0 < rbar := hrbardef ▸ Hp.parameters.neckRadius_pos 0 le_rfl
  have hA0 : 0 < A := by linarith
  obtain ⟨A', Cb, Q, κ₀, K, Λs, τs, τ₁, τ₂, C₁, T, hA'def, hAA', hA'1, hCbdef, hCb, hCbC, hQdef, hQ,
    hκdef, hκ, hKdef, hK, hΛs1, hΛsK, hτs, hexp, hτ₁def, hτ₁, hτ₂def, hτ₂, hτ₂le, hC₁1, hC₁A, hC₁Λ,
    hTT₀, hTB, hTL, hT⟩ := hsub86N_consts_S94 (B := B) hA1 hrbar hCpos Hp.C2_ge_one Ctime.coe_nonneg hT₀
  refine ⟨1 / 2, C₁, C * Q, τ₁, τ₂, τ₁ + τ₂, T, κ₀, by norm_num, le_rfl, hC₁1, mul_pos hCpos hQ, hτ₁, hτ₂,
    le_rfl, hT, hκ, ?_⟩
  intro s hsT u hTu hus ⟨hu0, hunev⟩ x0 r0 hr0 hrad hnom hsec hvol
  have hr0rbar : r0 ≤ rbar := hrbardef ▸ hrad.trans
    (Hp.radius_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu0.le) hu0.le)
  have hr02 : r0 ^ 2 ≤ rbar ^ 2 := pow_le_pow_left₀ hr0.le hr0rbar 2
  have hr0A : r0 ^ 2 ≤ A' := by rw [hA'def]; linarith
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hLu : (τ₁ + τ₂) * r0 ^ 2 ≤ (u : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_left hr02 (by positivity : 0 ≤ τ₁ + τ₂)
    nlinarith [hTL, hTu]
  have hrcI : ∀ t : ℝ, (u : ℝ) / 2 < t → Hp.parameters.recenterConstant * δ t ≤ 1 / 2 := by
    intro t ht
    have hBt : B < t := by linarith
    calc Hp.parameters.recenterConstant * δ t
        ≤ Hp.parameters.recenterConstant * (1 / (2 * Hp.parameters.recenterConstant)) :=
          mul_le_mul_of_nonneg_left (hB t hBt).le hκrc.le
      _ = 1 / 2 := by field_simp
  exact hsub86N_window_S94 Hp hP2 hscale hCrm hA0 hAA' hA'1 hCb hCbC hτ₁def hQdef hQ hκdef hκ hKdef hK
    hΛs1 hΛsK hτs hexp hτ₂def hτ₂ hτ₂le hC₁A hC₁Λ s u hu0 hus
    ((regular_iff_slice_S74 hu0 hus).mpr hunev) x0 hr0 hrad hr0A hLu hrcI
    (hAtop s u hus x0 hr0 hrad (ε := 1 / 2) (by norm_num) hvol) (hδT u (hTT₀.trans hTu)) hnom

end GC.LongTime.Ch12
