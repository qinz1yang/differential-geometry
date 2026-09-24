import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorChartFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}}

private theorem incoming_extended_riemannNorm_le_of_initial_scalar_bound
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
    {q Q a₀ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q)
    (hpinch : ∀ t ∈ Ico (H.time last) s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ x.val)
    (htime : 2 * C * (s - H.time first) * Q ≤ 1) :
    ∀ t ∈ Icc (H.time last) s,
      Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpast (t : ℝ) (ht : t ∈ Ico (H.time last) s) :
      G.riemannNorm t x.val ≤ 2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
    have hs := A.scalar_incoming_le_two_mul_initial_of_time_sub_le G hinit x.val hq hqQ
      hbound hfinal hscalar ht
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le _) (by positivity)) hQ.le).trans htime)
    have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x.val ha₀
      le_rfl (hpinch t ht) hs
    rw [max_eq_left (by positivity : 0 ≤ 2 * Q), show 2 * Q / 2 = Q by ring] at hr
    exact hr
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · rw [L.extendedMetric_before hlt, rmNormSq_restrictOpen]
    exact hpast t ⟨ht.1, hlt⟩
  · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
    apply le_of_tendsto (L.tendsto_riemannNorm x)
    filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
    exact hpast t ⟨ht.1.le, ht.2⟩

namespace ObservedHistory

variable {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

include hle in
private theorem exists_closed_stage_of_mem_Icc
    {t : ℝ} (ht : t ∈ Icc (H.time first) (H.time i.succ)) :
    ∃ j : Fin H.eventCount, first ≤ j.castSucc ∧ j.castSucc ≤ i.castSucc ∧
      t ∈ Icc (H.time j.castSucc) (H.time j.succ) := by
  by_cases hlast : H.time i.castSucc ≤ t
  · exact ⟨i, hle, le_rfl, hlast, ht.2⟩
  have hti : t < H.time i.castSucc := lt_of_not_ge hlast
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1, ht.2.trans (H.time_le_horizon_at i.succ)⟩
  let k := H.activeStage tH
  have hk : k < i.castSucc := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := i.isLt; change k.val < H.eventCount; omega⟩
  have hn := H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)
  exact ⟨j, hkfirst, hk.le, H.activeStage_time_le tH, hn.le⟩

theorem riemannNorm_backwardSurvivorTerminal_le_of_initial_scalar_bound
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hle t)
    (z : H.backwardSurvivorTerminalFace first i hle)
    {q Q a₀ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl z.val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl z.val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl z.val) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first)
      (H.backwardSurvivorMap first i.castSucc hle first le_rfl hle z.val) ≤ Q)
    (hpinch : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl z.val))
    (htime : 2 * C * (H.time i.succ - H.time first) * Q ≤ 1) :
    ∀ t ∈ Icc (H.time first) (H.time i.succ),
      Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let A : BackwardPointTrace H first i.castSucc hle z.val.val := Classical.choice z.val.property
  have heq (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ i.castSucc) :
      H.backwardSurvivorMap first i.castSucc hle j hf hl z.val = A.point j hf hl :=
    H.backwardSurvivorMap_eq_point first i.castSucc hle j hf hl z.val A
  have hscalarA : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q := by
    rw [← heq]
    exact hscalar
  have hboundA : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2 := by
    intro j hf hl
    simpa only [heq] using hbound j hf (j.castSucc_lt_succ.le.trans hl)
  intro t ht
  obtain ⟨j, hf, hl, htj⟩ := exists_closed_stage_of_mem_Icc (hle := hle) ht
  by_cases he : j = i
  · subst j
    rw [hlast t htj, backwardSurvivorTerminalFaceMetric, normSq0S_metricRm04At_localPullMetric]
    apply incoming_extended_riemannNorm_le_of_initial_scalar_bound (H.event i).incoming
      (H.event i).terminal (H.event_initial i)
      (H.backwardSurvivorTerminalFaceMap first i hle z) A hq hqQ ha₀ hboundA
    · simpa only [H.backwardSurvivorMap_last, H.backwardSurvivorTerminalFaceMap_val] using hbound i hle le_rfl
    · exact hscalarA
    · simpa only [H.backwardSurvivorMap_last, H.backwardSurvivorTerminalFaceMap_val] using hpinch i hle le_rfl
    · exact htime
    · exact htj
  · have hjnext : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val ≤ i.val := hl
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    rw [hslabs j hf hjnext t htj, rmNormSq_restrictOpen,
      backwardSurvivorSlabMetric, normSq0S_metricRm04At_localPullMetric]
    apply A.extended_riemannNorm_le_of_initial_scalar_bound hq hqQ ha₀ hboundA hscalarA
      j hf hjnext (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hjnext z.val)
    · exact heq j.castSucc hf hl
    · exact hpinch j hf hl
    · apply le_trans _ htime
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (sub_le_sub_right (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr hl)) _)
          (by positivity)) (hq.trans_le hqQ).le
    · exact htj

private theorem normalized_hamiltonIvey_curvature_bound
    {C₀ q a₀ : ℝ} (hq : 0 < q) (haq : 1 ≤ a₀ * q) :
    (2 * Real.sqrt 3 * (C₀ * q + max (2 * (C₀ * q)) (Real.exp 4 / a₀))) / q ≤
      2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4)) := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hterm : Real.exp 4 / a₀ ≤ Real.exp 4 * q := by
    apply (div_le_iff₀ ha₀).mpr
    nlinarith [mul_le_mul_of_nonneg_left haq (Real.exp_pos 4).le]
  have hmax : max (2 * (C₀ * q)) (Real.exp 4 / a₀) ≤
      max (2 * C₀) (Real.exp 4) * q := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) (Real.exp 4)) hq.le]
    · exact hterm.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq.le)
  apply (div_le_iff₀ hq).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ 2 * Real.sqrt 3)]

theorem curvature_bound_normalized_backwardSurvivor_chart_of_initial_scalar_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hle t)
    (Ξ : X → H.backwardSurvivorTerminalFace first i hle)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    (hpinch : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val))
    (htime : 2 * C * C₀ * (q * (H.time i.succ - H.time first)) ≤ 1)
    {D : RealTimeInterval} (L : SolutionOn (I := ThreeModel) (M := X) D)
    (hmetric : ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), L.base.metric t =
      localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ x : X,
      normSq0S (L.base.metric t) x 4 (L.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  intro t ht x
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have htG : H.time first + t / q ∈ Icc (H.time first) (H.time i.succ) := by
    constructor
    · have := div_nonneg ht.1 hq.le
      linarith
    · have := (div_le_iff₀ hq).mpr (show t ≤ (H.time i.succ - H.time first) * q by nlinarith [ht.2])
      linarith
  have hs : metricScalarAt (H.initialMetric first)
      (H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (Ξ x).val) ≤ C₀ * q := by
    rw [hbirth x]
    exact hscalar x
  have ht0 : 2 * C * (H.time i.succ - H.time first) * (C₀ * q) ≤ 1 := by
    nlinarith [htime]
  have hb := riemannNorm_backwardSurvivorTerminal_le_of_initial_scalar_bound G hslabs hlast
    (Ξ x) hr hrQ ha₀ (hbound x) hs (hpinch x) ht0 _ htG
  have hscale : Real.sqrt (normSq0S (scaleMetric q hq (G (H.time first + t / q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (G (H.time first + t / q))) (Ξ x))) =
      Real.sqrt (normSq0S (G (H.time first + t / q)) (Ξ x) 4
        (metricRm04At (G (H.time first + t / q)) (Ξ x))) / q := by
    convert! CheegerGromovCompactness.curvDerivNorm_scaleMetric
      (G (H.time first + t / q)) q hq 0 (Ξ x) using 1
    simp only [pow_zero, mul_one]
    rfl
  have hn : Real.sqrt (normSq0S (L.base.metric t) x 4 (L.base.rm04 t x)) ≤
      2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4)) := by
    change Real.sqrt (normSq0S (L.base.metric t) x 4 (metricRm04At (L.base.metric t) x)) ≤ _
    rw [hmetric t ht, normSq0S_metricRm04At_localPullMetric, hscale]
    exact (div_le_div_of_nonneg_right hb hq.le).trans
      (normalized_hamiltonIvey_curvature_bound hq haq)
  exact (Real.sqrt_le_iff.mp hn).2

theorem curvature_bound_normalized_backwardSurvivor_chart_of_initial_fixedHamiltonIveyRegion
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hle t)
    (Ξ : X → H.backwardSurvivorTerminalFace first i hle)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (H.time i.succ - H.time first)) ≤ 1)
    {D : RealTimeInterval} (L : SolutionOn (I := ThreeModel) (M := X) D)
    (hmetric : ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), L.base.metric t =
      localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ x : X,
      normSq0S (L.base.metric t) x 4 (L.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  apply curvature_bound_normalized_backwardSurvivor_chart_of_initial_scalar_bound
    G hslabs hlast Ξ hΞ J hbirth hr hq hrQ haq hbound hscalar _ htime L hmetric
  intro x j hf hl t ht
  let y := H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val
  have ht0 : 0 ≤ t := (H.time_nonneg j.castSucc).trans ht.1
  have hstage : t ∈ H.stageDomain j.castSucc := by
    simpa only [stageDomain, Fin.lastCases_castSucc] using ht
  have hregion : InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) (a₀ + t) y := by
    simpa only [stageMetric, Fin.lastCases_castSucc] using (hp.1 j.castSucc t hstage y).1
  apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ y).mpr
  exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
    ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) y).mp hregion)

open DifferentialGeometry.Tensor.Coordinates in
theorem exists_normalized_backwardSurvivor_chart_solution_curvature_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (Ξ : X → H.backwardSurvivorTerminalFace first i hle)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Ξ x).val) ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (H.time i.succ - H.time first)) ≤ 1) :
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = H.backwardSurvivorTerminalFaceMetric first i hle t) ∧
      ∃ L : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q * (H.time i.succ - H.time first))
            (by have ht := H.time_strictMono (hle.trans_lt i.castSucc_lt_succ); positivity)),
        IsSolutionOn L ∧ L.base.metric 0 = g₀ ∧
        (∀ t, L.base.metric t =
          localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) ∧
        (∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => chartGramMatrix (L.base.metric z.1) x z.2 k l)
            (Icc 0 (q * (H.time i.succ - H.time first)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
        ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ x : X,
          normSq0S (L.base.metric t) x 4 (L.base.rm04 t x) ≤
            (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  obtain ⟨G, hslabs, hlast, L, hL, hLzero, hmetric, hgram⟩ :=
    H.exists_normalized_backwardSurvivor_chart_solution first i hle Ξ hΞ J hbirth q hq g₀ hzero
  refine ⟨G, hslabs, hlast, L, hL, hLzero, hmetric, hgram, ?_⟩
  exact curvature_bound_normalized_backwardSurvivor_chart_of_initial_fixedHamiltonIveyRegion
    G hslabs hlast Ξ hΞ J hbirth hr hq hrQ haq hbound hscalar records hfixed hlower htime L
    (fun t _ => hmetric t)

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
