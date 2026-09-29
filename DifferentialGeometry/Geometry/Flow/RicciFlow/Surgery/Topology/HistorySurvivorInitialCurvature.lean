import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorChartFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
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

theorem riemannNorm_backwardSurvivorTerminal_le_of_scalar_bound_at_time
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hle t)
    (z : H.backwardSurvivorTerminalFace first i hle)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.castSucc ≤ i.castSucc)
    {q Q a₀ τ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl z.val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl z.val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl z.val) ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first i.castSucc hle j₀.castSucc
        hfirst hj₀ z.val) ≤ Q)
    (hpinch : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl z.val))
    (htime : 2 * C * (H.time i.succ - τ) * Q ≤ 1) :
    ∀ t ∈ Icc τ (H.time i.succ),
      Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let A : BackwardPointTrace H first i.castSucc hle z.val.val := Classical.choice z.val.property
  have heq (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ i.castSucc) :
      H.backwardSurvivorMap first i.castSucc hle j hf hl z.val = A.point j hf hl :=
    H.backwardSurvivorMap_eq_point first i.castSucc hle j hf hl z.val A
  have hscalarA : (H.event j₀).incoming.flow.scalar τ (A.point j₀.castSucc hfirst hj₀) ≤ Q := by
    rw [← heq]
    exact hscalar
  intro t ht
  obtain ⟨j, hf₀, hl, htj⟩ := exists_closed_stage_of_mem_Icc (hle := hj₀)
    (show t ∈ Icc (H.time j₀.castSucc) (H.time i.succ) from ⟨hτ.1.trans ht.1, ht.2⟩)
  have hf := hfirst.trans hf₀
  have hj : j₀ ≤ j := Fin.castSucc_le_castSucc_iff.mp hf₀
  have hboundA : ∀ l : Fin H.eventCount, ∀ hf' : j₀.castSucc ≤ l.castSucc,
      ∀ hl' : l.castSucc ≤ j.castSucc, ∀ s ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar s (A.point l.castSucc (hfirst.trans hf') (hl'.trans hl)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hfirst.trans hf') (hl'.trans hl))) (Iic s) s| ≤
        C * (H.event l).incoming.flow.scalar s (A.point l.castSucc (hfirst.trans hf') (hl'.trans hl)) ^ 2 := by
    intro l hf' hl'
    simpa only [heq] using hbound l hf' (hl'.trans hl)
  have htimej : 2 * C * (H.time j.succ - τ) * Q ≤ 1 := by
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sub_le_sub_right (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr hl)) τ)
        (by positivity)) (hq.trans_le hqQ).le
  by_cases he : j = i
  · subst j
    rw [hlast t htj, backwardSurvivorTerminalFaceMetric, normSq0S_metricRm04At_localPullMetric]
    apply A.extended_riemannNorm_le_of_earlier_scalar_bound_at_time hq hqQ ha₀
      j₀ i hfirst hj le_rfl hboundA hτ hscalarA
      (H.backwardSurvivorTerminalFaceMap first i hle z)
    · simp only [H.backwardSurvivorTerminalFaceMap_val, A.endpoint_eq]
    · intro s hs hτs
      simpa only [H.backwardSurvivorMap_last, H.backwardSurvivorTerminalFaceMap_val] using
        hpinch i hj₀ le_rfl s hs hτs
    · exact htime
    · exact htj
    · exact ht.1
  · have hjnext : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val ≤ i.val := hl
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    rw [hslabs j hf hjnext t htj, rmNormSq_restrictOpen,
      backwardSurvivorSlabMetric, normSq0S_metricRm04At_localPullMetric]
    apply A.extended_riemannNorm_le_of_earlier_scalar_bound_at_time hq hqQ ha₀
      j₀ j hfirst hj hl hboundA hτ hscalarA
      (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hjnext z.val)
    · exact heq j.castSucc hf hl
    · exact fun s hs hτs => hpinch j hf₀ hl s hs hτs
    · exact htimej
    · exact htj
    · exact ht.1

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
  let j₀ : Fin H.eventCount := ⟨first.val, lt_of_le_of_lt (show first.val ≤ i.val from hle) i.isLt⟩
  have he : j₀.castSucc = first := Fin.ext rfl
  have hτ : H.time first ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ) := by
    rw [← he]
    exact ⟨le_rfl, H.time_strictMono j₀.castSucc_lt_succ⟩
  apply riemannNorm_backwardSurvivorTerminal_le_of_scalar_bound_at_time
    G hslabs hlast z j₀ he.symm.le (he.le.trans hle) hq hqQ ha₀
  · intro j hf hl
    exact hbound j (he.symm.le.trans hf) hl
  · exact hτ
  · change metricScalarAt ((H.event j₀).incoming.flow.base.metric (H.time first)) _ ≤ Q
    rw [← congrArg H.time he, H.event_initial]
    exact hscalar
  · intro j hf hl t ht _
    exact hpinch j (he.symm.le.trans hf) hl t ht
  · exact htime


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

theorem curvature_bound_normalized_backwardSurvivor_chart_of_scalar_bound_at_time
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
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.castSucc ≤ i.castSucc)
    {r q C₀ a₀ τ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl (Ξ x).val) ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : ∀ x, (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first i.castSucc hle j₀.castSucc hfirst hj₀ (Ξ x).val) ≤ C₀ * q)
    (hpinch : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc, ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first i.castSucc hle j.castSucc (hfirst.trans hf) hl (Ξ x).val))
    (htime : 2 * C * C₀ * (q * (H.time i.succ - τ)) ≤ 1)
    {D : RealTimeInterval} (L : SolutionOn (I := ThreeModel) (M := X) D)
    (hmetric : ∀ t ∈ Icc (q * (τ - H.time first)) (q * (H.time i.succ - H.time first)), L.base.metric t =
      localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc (q * (τ - H.time first)) (q * (H.time i.succ - H.time first)), ∀ x : X,
      normSq0S (L.base.metric t) x 4 (L.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  intro t ht x
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have htG : H.time first + t / q ∈ Icc τ (H.time i.succ) := by
    constructor
    · have := (le_div_iff₀ hq).mpr (show (τ - H.time first) * q ≤ t by nlinarith [ht.1])
      linarith
    · have := (div_le_iff₀ hq).mpr (show t ≤ (H.time i.succ - H.time first) * q by nlinarith [ht.2])
      linarith
  have ht0 : 2 * C * (H.time i.succ - τ) * (C₀ * q) ≤ 1 := by
    nlinarith [htime]
  have hb := riemannNorm_backwardSurvivorTerminal_le_of_scalar_bound_at_time G hslabs hlast
    (Ξ x) j₀ hfirst hj₀ hr hrQ ha₀ (hbound x) hτ (hscalar x) (hpinch x) ht0 _ htG
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
  let j₀ : Fin H.eventCount := ⟨first.val, lt_of_le_of_lt (show first.val ≤ i.val from hle) i.isLt⟩
  have he : j₀.castSucc = first := Fin.ext rfl
  have hτ : H.time first ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ) := by
    rw [← he]
    exact ⟨le_rfl, H.time_strictMono j₀.castSucc_lt_succ⟩
  have hnormalized := curvature_bound_normalized_backwardSurvivor_chart_of_scalar_bound_at_time
    G hslabs hlast Ξ hΞ j₀ he.symm.le (he.le.trans hle) hr hq hrQ haq
    (fun x j hf hl => hbound x j (he.symm.le.trans hf) hl) hτ
    (by
      intro x
      change metricScalarAt ((H.event j₀).incoming.flow.base.metric (H.time first)) _ ≤ C₀ * q
      rw [← congrArg H.time he, H.event_initial]
      exact (hbirth x ▸ hscalar x))
    (fun x j hf hl t ht _ => hpinch x j (he.symm.le.trans hf) hl t ht)
    htime L (by simpa only [sub_self, mul_zero] using hmetric)
  simpa only [sub_self, mul_zero] using hnormalized


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

section Incoming

variable {last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem riemannNorm_backwardSurvivorIncoming_le_of_initial_scalar_bound
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (z : H.backwardSurvivorIncomingDomain first last hle G)
    {q Q a₀ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) z.val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) z.val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) z.val) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t z.val.val →
      |derivWithin (fun v => G.flow.scalar v z.val.val) (Iic t) t| ≤ C * G.flow.scalar t z.val.val ^ 2)
    (hscalar : metricScalarAt (H.initialMetric first)
      (H.backwardSurvivorMap first last hle first le_rfl hle z.val) ≤ Q)
    (hpinch : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) z.val))
    (hpinchFinal : ∀ t ∈ Ico (H.time last) s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ z.val.val)
    (htime : 2 * C * (s - H.time first) * Q ≤ 1) :
    ∀ t ∈ Icc (H.time first) s,
      Real.sqrt (normSq0S (gflow t) z 4 (metricRm04At (gflow t) z)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let A : BackwardPointTrace H first last hle z.val.val := Classical.choice z.val.property
  have heq (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
      H.backwardSurvivorMap first last hle j hf hl z.val = A.point j hf hl :=
    H.backwardSurvivorMap_eq_point first last hle j hf hl z.val A
  have hscalarA : metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ Q := by
    rw [← heq]
    exact hscalar
  have hboundA : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2 := by
    intro j hf hl
    simpa only [heq] using hbound j hf hl
  intro t ht
  by_cases hlasttime : H.time last ≤ t
  · rw [hlast t ⟨hlasttime, ht.2⟩, backwardSurvivorIncomingMetric,
      normSq0S_metricRm04At_localPullMetric]
    exact incoming_extended_riemannNorm_le_of_initial_scalar_bound G L hinit
      (H.backwardSurvivorIncomingMap first last hle G z) A hq hqQ ha₀ hboundA hfinal hscalarA
      hpinchFinal htime t ⟨hlasttime, ht.2⟩
  · have hti : t < H.time last := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
    let k := H.activeStage tH
    have hk : k < last := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hti
    have hf : first ≤ k := H.le_activeStage tH first ht.1
    let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
    have hl : j.succ ≤ last := hk
    have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
      ⟨H.activeStage_time_le tH,
        (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
    rw [hslabs j hf hl t htj, rmNormSq_restrictOpen,
      backwardSurvivorSlabMetric, normSq0S_metricRm04At_localPullMetric]
    apply A.extended_riemannNorm_le_of_initial_scalar_bound hq hqQ ha₀ hboundA hscalarA
      j hf hl (H.backwardSurvivorTerminalMap first last hle j hf hl z.val)
    · exact heq j.castSucc hf (j.castSucc_lt_succ.le.trans hl)
    · exact hpinch j hf hl
    · apply le_trans _ htime
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (sub_le_sub_right ((H.time_strictMono.monotone hl).trans G.lt.le) _)
          (by positivity)) (hq.trans_le hqQ).le
    · exact htj

theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_initial_scalar_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) (s),
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    (hpinch : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val))
    (hpinchFinal : ∀ x : X, ∀ t ∈ Ico (H.time last) s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ (Ξ x).val.val)
    (htime : 2 * C * C₀ * (q * (s - H.time first)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hmetric : ∀ t ∈ Icc 0 (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  intro t ht x
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have htG : H.time first + t / q ∈ Icc (H.time first) (s) := by
    constructor
    · have := div_nonneg ht.1 hq.le
      linarith
    · have := (div_le_iff₀ hq).mpr (show t ≤ (s - H.time first) * q by nlinarith [ht.2])
      linarith
  have hs : metricScalarAt (H.initialMetric first)
      (H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val) ≤ C₀ * q := by
    rw [hbirth x]
    exact hscalar x
  have ht0 : 2 * C * (s - H.time first) * (C₀ * q) ≤ 1 := by
    nlinarith [htime]
  have hb := riemannNorm_backwardSurvivorIncoming_le_of_initial_scalar_bound G L hinit
    gflow hslabs hlast (Ξ x) hr hrQ ha₀ (hbound x) (hfinal x) hs (hpinch x)
    (hpinchFinal x) ht0 _ htG
  have hscale : Real.sqrt (normSq0S (scaleMetric q hq (gflow (H.time first + t / q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (gflow (H.time first + t / q))) (Ξ x))) =
      Real.sqrt (normSq0S (gflow (H.time first + t / q)) (Ξ x) 4
        (metricRm04At (gflow (H.time first + t / q)) (Ξ x))) / q := by
    convert! CheegerGromovCompactness.curvDerivNorm_scaleMetric
      (gflow (H.time first + t / q)) q hq 0 (Ξ x) using 1
    simp only [pow_zero, mul_one]
    rfl
  have hn : Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤
      2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4)) := by
    change Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x)) ≤ _
    rw [hmetric t ht, normSq0S_metricRm04At_localPullMetric, hscale]
    exact (div_le_div_of_nonneg_right hb hq.le).trans
      (normalized_hamiltonIvey_curvature_bound hq haq)
  exact (Real.sqrt_le_iff.mp hn).2

theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_initial_fixedHamiltonIveyRegion
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) (s),
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (s - H.time first)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hmetric : ∀ t ∈ Icc 0 (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have hstart : H.time last ∈ H.stageDomain last := by
    cases last using Fin.lastCases with
    | last =>
      simpa only [stageDomain, Fin.lastCases_last] using
        (show H.time (Fin.last H.eventCount) ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
          ⟨le_rfl, H.time_le_horizon⟩)
    | cast j =>
      simpa only [stageDomain, Fin.lastCases_castSucc] using
        (show H.time j.castSucc ∈ Ico (H.time j.castSucc) (H.time j.succ) from
          ⟨le_rfl, H.time_strictMono j.castSucc_lt_succ⟩)
  have hinitHI (x : (H.stage last).Carrier) :
      InFixedHamiltonIveyRegion (H.initialMetric last) (a₀ + H.time last) x ∧
        -3 / (a₀ + H.time last) ≤ metricScalarAt (H.initialMetric last) x := by
    simpa only [H.stageMetric_initial] using hp.1 last (H.time last) hstart x
  have hfuture := G.fixedHamiltonIveyRegion_and_scalar_lower
    (by linarith [H.time_nonneg last] : 0 < a₀ + H.time last)
    (fun x => by rw [hinit]; exact (hinitHI x).1)
    (fun x => by
      change -3 / (a₀ + H.time last) ≤ metricScalarAt (G.flow.base.metric (H.time last)) x
      rw [hinit]
      exact (hinitHI x).2)
  apply curvature_bound_normalized_backwardSurvivorIncoming_chart_of_initial_scalar_bound
    G L hinit gflow hslabs hlast Ξ hΞ J hbirth hr hq hrQ haq hbound hfinal hscalar _ _ htime S hmetric
  · intro x j hf hl t ht
    let y := H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val
    have ht0 : 0 ≤ t := (H.time_nonneg j.castSucc).trans ht.1
    have hstage : t ∈ H.stageDomain j.castSucc := by
      simpa only [stageDomain, Fin.lastCases_castSucc] using ht
    have hregion : InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) (a₀ + t) y := by
      simpa only [stageMetric, Fin.lastCases_castSucc] using (hp.1 j.castSucc t hstage y).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ y).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) y).mp hregion)
  · intro x t ht
    have ht0 : 0 ≤ t := (H.time_nonneg last).trans ht.1
    have hregion : InFixedHamiltonIveyRegion (G.flow.base.metric t) (a₀ + t) (Ξ x).val.val := by
      simpa only [show a₀ + H.time last + t - H.time last = a₀ + t by ring] using
        (hfuture t ht (Ξ x).val.val).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ (Ξ x).val.val).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) (Ξ x).val.val).mp hregion)

theorem exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x)
    {r q C₀ a₀ : ℝ} {C : ℝ≥0} (hr : 0 < r) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (s - H.time first)) ≤ 1) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ∃ S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q * (s - H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t =
          localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
        (∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) x z.2 k l)
            (Icc 0 (q * (s - H.time first)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
        ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ x : X,
          normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
            (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  obtain ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram⟩ :=
    H.exists_normalized_backwardSurvivorIncoming_chart_solution first last hle G L hinit
      Ξ hΞ J hbirth q hq g₀ hzero
  refine ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram, ?_⟩
  exact curvature_bound_normalized_backwardSurvivorIncoming_chart_of_initial_fixedHamiltonIveyRegion
    G L hinit gflow hslabs hlast Ξ hΞ J hbirth hr hq hrQ haq hbound hfinal hscalar
    records hfixed hlower htime S (fun t _ => hmetric t)

end Incoming
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {H : ObservedHistory.{u}}


namespace ObservedHistory

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem riemannNorm_backwardSurvivorIncoming_le_of_scalar_bound_at_time
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (z : H.backwardSurvivorIncomingDomain first last hle G)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.succ ≤ last)
    {q Q a₀ τ : ℝ} {C : ℝ≥0} (hQ : 0 < Q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) z.val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) z.val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) z.val) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t z.val.val →
      |derivWithin (fun v => G.flow.scalar v z.val.val) (Iic t) t| ≤ C * G.flow.scalar t z.val.val ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first last hle j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀) z.val) ≤ Q)
    (hpinch : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) z.val))
    (hpinchFinal : ∀ t ∈ Ico (H.time last) s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ z.val.val)
    (htime : 2 * C * (s-τ) * Q ≤ 1) :
    ∀ t ∈ Icc τ s,
      Real.sqrt (normSq0S (gflow t) z 4 (metricRm04At (gflow t) z)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let A : BackwardPointTrace H first last hle z.val.val := Classical.choice z.val.property
  have heq (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
      H.backwardSurvivorMap first last hle j hf hl z.val = A.point j hf hl :=
    H.backwardSurvivorMap_eq_point first last hle j hf hl z.val A
  have hscalarA : (H.event j₀).incoming.flow.scalar τ
      (A.point j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀)) ≤ Q := by
    rw [← heq]
    exact hscalar
  have hboundA : ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl)) ^ 2 := by
    intro j hf hl
    simpa only [heq] using hbound j hf hl
  have hlate : ∀ t ∈ Ico (H.time last) s,
      G.riemannNorm t z.val.val ≤ 2 * Real.sqrt 3 * (Q+max (2*Q) (Real.exp 4/a₀)) := by
    intro t ht
    have hs := BackwardPointTrace.scalar_incoming_le_two_mul_of_scalar_bound_at_time G hinit z.val.val A
      j₀ hfirst hj₀ hQ hqQ hboundA hfinal hτ hscalarA ht
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le _) (by positivity)) hQ.le).trans htime)
    have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) z.val.val ha₀
      le_rfl (hpinchFinal t ht) hs
    rw [max_eq_left (by positivity : 0 ≤ 2*Q),show 2*Q/2=Q by ring] at hr
    exact hr
  intro t ht
  by_cases hlasttime : H.time last ≤ t
  · rw [hlast t ⟨hlasttime,ht.2⟩,backwardSurvivorIncomingMetric,normSq0S_metricRm04At_localPullMetric]
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · rw [L.extendedMetric_before hlt,rmNormSq_restrictOpen]
      exact hlate t ⟨hlasttime,hlt⟩
    · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
      apply le_of_tendsto (L.tendsto_riemannNorm (H.backwardSurvivorIncomingMap first last hle G z))
      filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
      exact hlate t ⟨ht.1.le,ht.2⟩
  · have hti : t < H.time last := lt_of_not_ge hlasttime
    have hfirsttime : H.time first ≤ t :=
      ((H.time_strictMono.monotone hfirst).trans hτ.1).trans ht.1
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t,(H.time_nonneg first).trans hfirsttime,hti.le.trans (H.time_le_horizon_at last)⟩
    let k := H.activeStage tH
    have hk : k < last := H.time_strictMono.lt_iff_lt.mp ((H.activeStage_time_le tH).trans_lt hti)
    have hf₀ : j₀.castSucc ≤ k := H.le_activeStage tH j₀.castSucc (hτ.1.trans ht.1)
    have hf : first ≤ k := hfirst.trans hf₀
    let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
    have hl : j.succ ≤ last := hk
    have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
      ⟨H.activeStage_time_le tH,(H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
    rw [hslabs j hf hl t htj,rmNormSq_restrictOpen,
      backwardSurvivorSlabMetric,normSq0S_metricRm04At_localPullMetric]
    apply A.extended_riemannNorm_le_of_earlier_scalar_bound_at_time hQ le_rfl ha₀
      j₀ j hfirst (Fin.castSucc_le_castSucc_iff.mp hf₀) (j.castSucc_lt_succ.le.trans hl)
      (fun l hfl hlj u hu hR => hboundA l hfl
        ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hlj)).trans hl) u hu (hqQ.trans_lt hR))
      hτ hscalarA (H.backwardSurvivorTerminalMap first last hle j hf hl z.val)
    · exact heq j.castSucc hf (j.castSucc_lt_succ.le.trans hl)
    · exact hpinch j hf₀ hl
    · apply le_trans _ htime
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (sub_le_sub_right ((H.time_strictMono.monotone hl).trans G.lt.le) _) (by positivity)) hQ.le
    · exact htj
    · exact ht.1

theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_scalar_bound_at_time
    {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
    [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) (s),
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.succ ≤ last)
    {r q C₀ a₀ τ : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : ∀ x, (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first last hle j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀) (Ξ x).val) ≤ C₀ * q)
    (hpinch : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val))
    (hpinchFinal : ∀ x : X, ∀ t ∈ Ico (H.time last) s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ (Ξ x).val.val)
    (htime : 2 * C * C₀ * (q * (s - τ)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := X) D)
    (hmetric : ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  intro t ht x
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have htG : H.time first + t / q ∈ Icc τ s := by
    constructor
    · have := (le_div_iff₀ hq).mpr (show (τ-H.time first)*q ≤ t by nlinarith [ht.1])
      linarith
    · have := (div_le_iff₀ hq).mpr (show t ≤ (s-H.time first)*q by nlinarith [ht.2])
      linarith
  have ht0 : 2 * C * (s-τ) * (C₀*q) ≤ 1 := by nlinarith [htime]
  have hb := riemannNorm_backwardSurvivorIncoming_le_of_scalar_bound_at_time G L hinit
    gflow hslabs hlast (Ξ x) j₀ hfirst hj₀ (mul_pos hC₀ hq) hrQ ha₀ (hbound x) (hfinal x) hτ
    (hscalar x) (hpinch x) (hpinchFinal x) ht0 _ htG
  have hscale : Real.sqrt (normSq0S (scaleMetric q hq (gflow (H.time first + t / q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (gflow (H.time first + t / q))) (Ξ x))) =
      Real.sqrt (normSq0S (gflow (H.time first + t / q)) (Ξ x) 4
        (metricRm04At (gflow (H.time first + t / q)) (Ξ x))) / q := by
    convert! CheegerGromovCompactness.curvDerivNorm_scaleMetric
      (gflow (H.time first + t / q)) q hq 0 (Ξ x) using 1
    simp only [pow_zero, mul_one]
    rfl
  have hn : Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤
      2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4)) := by
    change Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x)) ≤ _
    rw [hmetric t ht]
    change CheegerGromovCompactness.curvDerivNorm 0
      (localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) x ≤ _
    rw [CheegerGromovCompactness.curvDerivNorm_localPullMetric]
    change Real.sqrt (normSq0S (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x))) ≤ _
    rw [hscale]
    exact (div_le_div_of_nonneg_right hb hq.le).trans
      (normalized_hamiltonIvey_curvature_bound hq haq)
  exact (Real.sqrt_le_iff.mp hn).2


theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_scalar_bound_at_time_of_initial_fixedHamiltonIveyRegion
    {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
    [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) (s),
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.succ ≤ last)
    {r q C₀ a₀ τ : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc,
      ∀ hl : j.succ ≤ last, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hscalar : ∀ x, (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first last hle j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀) (Ξ x).val) ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (s - τ)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := X) D)
    (hmetric : ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have hstart : H.time last ∈ H.stageDomain last := by
    cases last using Fin.lastCases with
    | last =>
      simpa only [stageDomain, Fin.lastCases_last] using
        (show H.time (Fin.last H.eventCount) ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
          ⟨le_rfl, H.time_le_horizon⟩)
    | cast j =>
      simpa only [stageDomain, Fin.lastCases_castSucc] using
        (show H.time j.castSucc ∈ Ico (H.time j.castSucc) (H.time j.succ) from
          ⟨le_rfl, H.time_strictMono j.castSucc_lt_succ⟩)
  have hinitHI (x : (H.stage last).Carrier) :
      InFixedHamiltonIveyRegion (H.initialMetric last) (a₀ + H.time last) x ∧
        -3 / (a₀ + H.time last) ≤ metricScalarAt (H.initialMetric last) x := by
    simpa only [H.stageMetric_initial] using hp.1 last (H.time last) hstart x
  have hfuture := G.fixedHamiltonIveyRegion_and_scalar_lower
    (by linarith [H.time_nonneg last] : 0 < a₀ + H.time last)
    (fun x => by rw [hinit]; exact (hinitHI x).1)
    (fun x => by
      change -3 / (a₀ + H.time last) ≤ metricScalarAt (G.flow.base.metric (H.time last)) x
      rw [hinit]
      exact (hinitHI x).2)
  apply curvature_bound_normalized_backwardSurvivorIncoming_chart_of_scalar_bound_at_time
    G L hinit gflow hslabs hlast Ξ hΞ j₀ hfirst hj₀ hC₀ hq hrQ haq hbound hfinal hτ hscalar _ _ htime S hmetric
  · intro x j hf hl t ht _
    let y := H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ξ x).val
    have ht0 : 0 ≤ t := (H.time_nonneg j.castSucc).trans ht.1
    have hstage : t ∈ H.stageDomain j.castSucc := by
      simpa only [stageDomain, Fin.lastCases_castSucc] using ht
    have hregion : InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) (a₀ + t) y := by
      simpa only [stageMetric, Fin.lastCases_castSucc] using (hp.1 j.castSucc t hstage y).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ y).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) y).mp hregion)
  · intro x t ht
    have ht0 : 0 ≤ t := (H.time_nonneg last).trans ht.1
    have hregion : InFixedHamiltonIveyRegion (G.flow.base.metric t) (a₀ + t) (Ξ x).val.val := by
      simpa only [show a₀ + H.time last + t - H.time last = a₀ + t by ring] using
        (hfuture t ht (Ξ x).val.val).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ (Ξ x).val.val).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) (Ξ x).val.val).mp hregion)


theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_final_scalar_bound_at_time
    {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
    [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    {r q C₀ a₀ τ : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ t ∈ Ioo τ s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hτ : τ ∈ Ico (H.time last) s)
    (hscalar : ∀ x, G.flow.scalar τ (Ξ x).val.val ≤ C₀ * q)
    (hpinch : ∀ x : X, ∀ t ∈ Ico τ s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ (Ξ x).val.val)
    (htime : 2 * C * C₀ * (q * (s - τ)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := X) D)
    (hmetric : ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  intro t ht x
  have htG : H.time first + t/q ∈ Icc τ s := by
    constructor
    · have := (le_div_iff₀ hq).mpr (show (τ-H.time first)*q ≤ t by nlinarith [ht.1])
      linarith
    · have := (div_le_iff₀ hq).mpr (show t ≤ (s-H.time first)*q by nlinarith [ht.2])
      linarith
  have ht0 : 2 * C * (s-τ) * (C₀*q) ≤ 1 := by nlinarith [htime]
  have hb := OrientedThreeStage.IncomingSlab.TerminalLimitMetric.riemannNorm_extendedMetric_le_of_scalar_bound_at_time
    G L (H.backwardSurvivorIncomingMap first last hle G (Ξ x)) (mul_pos hC₀ hq)
    hrQ ha₀ hτ (hbound x) (hscalar x) (hpinch x) ht0 _ htG
  have hb' : Real.sqrt (normSq0S (gflow (H.time first+t/q)) (Ξ x) 4
      (metricRm04At (gflow (H.time first+t/q)) (Ξ x))) ≤
        2 * Real.sqrt 3 * (C₀*q+max (2*(C₀*q)) (Real.exp 4/a₀)) := by
    rw [hlast _ ⟨hτ.1.trans htG.1,htG.2⟩,backwardSurvivorIncomingMetric,
      normSq0S_metricRm04At_localPullMetric]
    exact hb
  have hscale : Real.sqrt (normSq0S (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x))) =
      Real.sqrt (normSq0S (gflow (H.time first+t/q)) (Ξ x) 4
        (metricRm04At (gflow (H.time first+t/q)) (Ξ x))) / q := by
    convert! CheegerGromovCompactness.curvDerivNorm_scaleMetric (gflow (H.time first+t/q)) q hq 0 (Ξ x) using 1
    simp only [pow_zero,mul_one]
    rfl
  have hn : Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤
      2 * Real.sqrt 3 * (C₀+max (2*C₀) (Real.exp 4)) := by
    change Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x)) ≤ _
    rw [hmetric t ht]
    change CheegerGromovCompactness.curvDerivNorm 0
      (localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) x ≤ _
    rw [CheegerGromovCompactness.curvDerivNorm_localPullMetric]
    change Real.sqrt (normSq0S (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x) 4
      (metricRm04At (scaleMetric q hq (gflow (H.time first+t/q))) (Ξ x))) ≤ _
    rw [hscale]
    exact (div_le_div_of_nonneg_right hb' hq.le).trans
      (normalized_hamiltonIvey_curvature_bound hq haq)
  exact (Real.sqrt_le_iff.mp hn).2


theorem curvature_bound_normalized_backwardSurvivorIncoming_chart_of_final_scalar_bound_at_time_of_initial_fixedHamiltonIveyRegion
    {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
    [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    {r q C₀ a₀ τ : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hbound : ∀ x : X, ∀ t ∈ Ioo τ s, r < G.flow.scalar t (Ξ x).val.val →
      |derivWithin (fun v => G.flow.scalar v (Ξ x).val.val) (Iic t) t| ≤
        C * G.flow.scalar t (Ξ x).val.val ^ 2)
    (hτ : τ ∈ Ico (H.time last) s)
    (hscalar : ∀ x, G.flow.scalar τ (Ξ x).val.val ≤ C₀ * q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (htime : 2 * C * C₀ * (q * (s - τ)) ≤ 1)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := X) D)
    (hmetric : ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) :
    ∀ t ∈ Icc (q * (τ - H.time first)) (q * (s - H.time first)), ∀ x : X,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
        (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have hstart : H.time last ∈ H.stageDomain last := by
    cases last using Fin.lastCases with
    | last =>
      simpa only [stageDomain, Fin.lastCases_last] using
        (show H.time (Fin.last H.eventCount) ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
          ⟨le_rfl,H.time_le_horizon⟩)
    | cast j =>
      simpa only [stageDomain, Fin.lastCases_castSucc] using
        (show H.time j.castSucc ∈ Ico (H.time j.castSucc) (H.time j.succ) from
          ⟨le_rfl,H.time_strictMono j.castSucc_lt_succ⟩)
  have hinitHI (x : (H.stage last).Carrier) :
      InFixedHamiltonIveyRegion (H.initialMetric last) (a₀+H.time last) x ∧
        -3/(a₀+H.time last) ≤ metricScalarAt (H.initialMetric last) x := by
    simpa only [H.stageMetric_initial] using hp.1 last (H.time last) hstart x
  have hfuture := G.fixedHamiltonIveyRegion_and_scalar_lower
    (by linarith [H.time_nonneg last] : 0 < a₀+H.time last)
    (fun x => by rw [hinit]; exact (hinitHI x).1)
    (fun x => by
      change -3/(a₀+H.time last) ≤ metricScalarAt (G.flow.base.metric (H.time last)) x
      rw [hinit]
      exact (hinitHI x).2)
  apply curvature_bound_normalized_backwardSurvivorIncoming_chart_of_final_scalar_bound_at_time
    G L gflow hlast Ξ hΞ hC₀ hq hrQ haq hbound hτ hscalar _ htime S hmetric
  intro x t ht
  have hbefore : t ∈ Ico (H.time last) s := ⟨hτ.1.trans ht.1,ht.2⟩
  have ht0 : 0 ≤ t := (H.time_nonneg last).trans hbefore.1
  have hregion : InFixedHamiltonIveyRegion (G.flow.base.metric t) (a₀+t) (Ξ x).val.val := by
    simpa only [show a₀+H.time last+t-H.time last = a₀+t by ring] using
      (hfuture t hbefore (Ξ x).val.val).1
  apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ (Ξ x).val.val).mpr
  exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀+t) (by linarith)
    ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀+t) (Ξ x).val.val).mp hregion)


end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {s τ : ℝ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound_of_final_scalar_bound_at_time
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (Ψ : X → H.backwardSurvivorDomain first last hle)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    {r q C₀ a₀ Kpast : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hτ : τ ∈ Ico (H.time last) s)
    (hbound : ∀ x : X, ∀ t ∈ Ioo τ s, r < G.flow.scalar t (Ψ x).val →
      |derivWithin (fun v => G.flow.scalar v (Ψ x).val) (Iic t) t| ≤
        C * G.flow.scalar t (Ψ x).val ^ 2)
    (hscalar : ∀ x, G.flow.scalar τ (Ψ x).val ≤ C₀ * q)
    (htime : 2*C*C₀*(q*(s-τ)) ≤ 1)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (G₀ : (H.stage last).IncomingSlab (H.time last) τ) (L₀ : G₀.TerminalLimitMetric)
    (hsource₀ : ∀ t, G₀.flow.base.metric t = G.flow.base.metric t)
    (hterminal₀ : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first last hle G₀)
    (hΞ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ₀)
    (hprojection₀ : ∀ x, (Ξ₀ x).val = Ψ x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G₀))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G₀))
    (hlast₀ : ∀ t ∈ Icc (H.time last) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first last hle G₀ L₀ t)
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := X) D₀)
    (hmetric₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first+t/q))) Ξ₀ hΞ₀)
    (hcurv₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), ∀ x : X,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast) :
    ∃ (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ),
      (∀ x, (Ξ x).val = Ψ x) ∧
      (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x) ∧
      ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ∃ S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q*(s-H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t = localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) ∧
        (∀ (x : X) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) x z.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
        (∀ t ∈ Icc 0 (q*(τ-H.time first)), S.base.metric t = S₀.base.metric t) ∧
        ∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ x : X,
          normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
            max Kpast ((2 * Real.sqrt 3 * (C₀+max (2*C₀) (Real.exp 4))) ^ 2) := by
  have hbudget : 2*C*(C₀ * q)*(s-τ) ≤ 1 := by nlinarith [htime]
  obtain ⟨Ξ,hΞ,hprojection,hbirth',gflow,hslabs,hlast,S,hS,hSzero,hmetric,hgram⟩ :=
    H.exists_normalized_backwardSurvivorIncoming_chart_solution_of_scalar_bound_at_time
      first last hle G L hinit Ψ hΨ (mul_pos hC₀ hq) hrQ hτ hbound hscalar hbudget J hbirth q hq g₀ hzero
  have hlate := curvature_bound_normalized_backwardSurvivorIncoming_chart_of_final_scalar_bound_at_time_of_initial_fixedHamiltonIveyRegion
    G L hinit gflow hlast Ξ hΞ hC₀ hq hrQ haq
    (fun x => by simpa only [hprojection] using hbound x)
    hτ (fun x => by simpa only [hprojection] using hscalar x)
    records hfixed hlower htime S (fun t _ => hmetric t)
  have hpast : ∀ t ∈ Icc 0 (q*(τ-H.time first)), S.base.metric t = S₀.base.metric t := by
    intro t ht
    rw [hmetric, hmetric₀ t ht]
    rw [localPullMetric_scaleMetric,localPullMetric_scaleMetric]
    congr 1
    have htphys : H.time first+t/q ∈ Icc (H.time first) τ := by
      constructor
      · have := div_nonneg ht.1 hq.le
        linarith
      · have := (div_le_iff₀ hq).mpr (show t ≤ (τ-H.time first)*q by nlinarith [ht.2])
        linarith
    exact (H.localPullMetric_backwardSurvivorIncoming_flow_eq_of_source_eq first last hle G₀ L₀ G L
      hτ.2 hsource₀ hterminal₀ gflow₀ gflow hslabs₀ hslabs hlast₀ hlast Ξ₀ Ξ hΞ₀ hΞ
      (fun x => by rw [hprojection₀ x,hprojection x]) htphys).symm
  refine ⟨Ξ,hΞ,hprojection,hbirth',gflow,hslabs,hlast,S,hS,hSzero,hmetric,hgram,hpast,?_⟩
  intro t ht x
  by_cases hbefore : t ≤ q*(τ-H.time first)
  · have hcp := hcurv₀ t ⟨ht.1,hbefore⟩ x
    change normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ _
    rw [hpast t ⟨ht.1,hbefore⟩]
    exact hcp.trans (le_max_left _ _)
  · exact (hlate t ⟨(lt_of_not_ge hbefore).le,ht.2⟩ x).trans (le_max_right _ _)

theorem exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound_of_earlier_scalar_bound_at_time
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (Ψ : X → H.backwardSurvivorDomain first last hle)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (j₀ : Fin H.eventCount) (hfirst : first ≤ j₀.castSucc) (hj₀ : j₀.succ ≤ last)
    {r q C₀ a₀ Kpast : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hτ : τ ∈ Ico (H.time j₀.castSucc) (H.time j₀.succ))
    (hbound : ∀ x : X, ∀ j : Fin H.eventCount, ∀ hf : j₀.castSucc ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      r < (H.event j).incoming.flow.scalar t
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ψ x)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ψ x))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (H.backwardSurvivorMap first last hle j.castSucc (hfirst.trans hf) (j.castSucc_lt_succ.le.trans hl) (Ψ x)) ^ 2)
    (hfinal : ∀ x : X, ∀ t ∈ Ioo (H.time last) s, r < G.flow.scalar t (Ψ x).val →
      |derivWithin (fun v => G.flow.scalar v (Ψ x).val) (Iic t) t| ≤
        C * G.flow.scalar t (Ψ x).val ^ 2)
    (hscalar : ∀ x, (H.event j₀).incoming.flow.scalar τ
      (H.backwardSurvivorMap first last hle j₀.castSucc hfirst (j₀.castSucc_lt_succ.le.trans hj₀) (Ψ x)) ≤ C₀ * q)
    (htime : 2*C*C₀*(q*(s-τ)) ≤ 1)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (G₀ : (H.stage j₀.castSucc).IncomingSlab (H.time j₀.castSucc) τ) (L₀ : G₀.TerminalLimitMetric)
    (hsource₀ : ∀ t, G₀.flow.base.metric t = (H.event j₀).incoming.flow.base.metric t)
    (hterminal₀ : L₀.metric = ((H.event j₀).incoming.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first j₀.castSucc hfirst G₀)
    (hΞ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ₀)
    (hbirth₀ : ∀ x, H.backwardSurvivorMap first j₀.castSucc hfirst first le_rfl hfirst (Ξ₀ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first j₀.castSucc hfirst G₀))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ j₀.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first j₀.castSucc hfirst j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first j₀.castSucc hfirst G₀))
    (hlast₀ : ∀ t ∈ Icc (H.time j₀.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first j₀.castSucc hfirst G₀ L₀ t)
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := X) D₀)
    (hmetric₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first+t/q))) Ξ₀ hΞ₀)
    (hcurv₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), ∀ x : X,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast) :
    ∃ (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ),
      (∀ x, (Ξ x).val = Ψ x) ∧
      (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x) ∧
      ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ∃ S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q*(s-H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t = localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) ∧
        (∀ (x : X) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) x z.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
        (∀ t ∈ Icc 0 (q*(τ-H.time first)), S.base.metric t = S₀.base.metric t) ∧
        ∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ x : X,
          normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
            max Kpast ((2 * Real.sqrt 3 * (C₀+max (2*C₀) (Real.exp 4))) ^ 2) := by
  obtain ⟨Ξ,hΞ,hprojection⟩ :=
    H.exists_backwardSurvivorIncoming_chart_of_earlier_scalar_bound_at_time first last hle G hinit
      Ψ hΨ j₀ hfirst hj₀ (mul_pos hC₀ hq) hrQ hbound hfinal hτ hscalar (by nlinarith [htime])
  have hbirth' : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x := by
    intro x
    rw [hprojection x]
    exact hbirth x
  obtain ⟨gflow,hslabs,hlast,S,hS,hSzero,hmetric,hgram⟩ :=
    H.exists_normalized_backwardSurvivorIncoming_chart_solution first last hle G L hinit Ξ hΞ
      J hbirth' q hq g₀ hzero
  have hlate := curvature_bound_normalized_backwardSurvivorIncoming_chart_of_scalar_bound_at_time_of_initial_fixedHamiltonIveyRegion
    G L hinit gflow hslabs hlast Ξ hΞ j₀ hfirst hj₀ hC₀ hq hrQ haq
    (fun x => by simpa only [hprojection] using hbound x)
    (fun x => by simpa only [hprojection] using hfinal x)
    hτ (fun x => by simpa only [hprojection] using hscalar x)
    records hfixed hlower htime S (fun t _ => hmetric t)
  have hpast : ∀ t ∈ Icc 0 (q*(τ-H.time first)), S.base.metric t = S₀.base.metric t := by
    intro t ht
    rw [hmetric, hmetric₀ t ht]
    rw [localPullMetric_scaleMetric,localPullMetric_scaleMetric]
    congr 1
    have htphys : H.time first+t/q ∈ Icc (H.time first) τ := by
      constructor
      · have := div_nonneg ht.1 hq.le
        linarith
      · have := (div_le_iff₀ hq).mpr (show t ≤ (τ-H.time first)*q by nlinarith [ht.2])
        linarith
    exact (H.localPullMetric_backwardSurvivorIncoming_flow_eq_of_earlier_source_eq first last hle G
      j₀ hfirst hj₀ G₀ L₀ hsource₀ hterminal₀ hτ.2 gflow₀ gflow hslabs₀ hslabs hlast₀
      Ξ₀ Ξ hΞ₀ hΞ (fun x => (hbirth₀ x).trans (hbirth' x).symm) htphys).symm
  refine ⟨Ξ,hΞ,hprojection,hbirth',gflow,hslabs,hlast,S,hS,hSzero,hmetric,hgram,hpast,?_⟩
  intro t ht x
  by_cases hbefore : t ≤ q*(τ-H.time first)
  · have hcp := hcurv₀ t ⟨ht.1,hbefore⟩ x
    change normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ _
    rw [hpast t ⟨ht.1,hbefore⟩]
    exact hcp.trans (le_max_left _ _)
  · exact (hlate t ⟨(lt_of_not_ge hbefore).le,ht.2⟩ x).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {s τ : ℝ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_normalized_backwardSurvivorIncoming_embedding_solution_curvature_bound_of_final_scalar_bound_at_time
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (Ψ : X → H.backwardSurvivorDomain first last hle)
    (hΨ : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ)
    {r q C₀ a₀ Kpast : ℝ} {C : ℝ≥0} (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q)
    (haq : 1 ≤ a₀ * q)
    (hτ : τ ∈ Ico (H.time last) s)
    (hbound : ∀ x : X, ∀ t ∈ Ioo τ s, r < G.flow.scalar t (Ψ x).val →
      |derivWithin (fun v => G.flow.scalar v (Ψ x).val) (Iic t) t| ≤
        C * G.flow.scalar t (Ψ x).val ^ 2)
    (hscalar : ∀ x, G.flow.scalar τ (Ψ x).val ≤ C₀ * q)
    (htime : 2*C*C₀*(q*(s-τ)) ≤ 1)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (G₀ : (H.stage last).IncomingSlab (H.time last) τ) (L₀ : G₀.TerminalLimitMetric)
    (hsource₀ : ∀ t, G₀.flow.base.metric t = G.flow.base.metric t)
    (hterminal₀ : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first last hle G₀)
    (hΞ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ₀)
    (hprojection₀ : ∀ x, (Ξ₀ x).val = Ψ x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G₀))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G₀))
    (hlast₀ : ∀ t ∈ Icc (H.time last) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first last hle G₀ L₀ t)
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := X) D₀)
    (hmetric₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first+t/q))) Ξ₀ hΞ₀)
    (hcurv₀ : ∀ t ∈ Icc 0 (q*(τ-H.time first)), ∀ x : X,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast) :
    ∃ (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ (p : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle p.val)
        (z : X), J z = A.point first le_rfl hle →
          H.backwardSurvivorIncomingMap first last hle G (Ξ z) = p) ∧
      (∀ x, (Ξ x).val = Ψ x) ∧
      (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x) ∧
      ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ∃ S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q*(s-H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t = localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) ∧
        (∀ (x : X) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) x z.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
        (∀ t ∈ Icc 0 (q*(τ-H.time first)), S.base.metric t = S₀.base.metric t) ∧
        ∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ x : X,
          normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
            max Kpast ((2 * Real.sqrt 3 * (C₀+max (2*C₀) (Real.exp 4))) ^ 2) := by
  have hΨloc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv Ψ
      hΨ.contMDiff (fun x => (hΨ.isImmersion.isImmersionAt x).mfderiv_injective (by simp)) rfl
  obtain ⟨Ξ, hΞ, hprojection, hbirth', hrest⟩ :=
    exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound_of_final_scalar_bound_at_time
      G L hinit Ψ hΨloc hC₀ hq hrQ haq hτ hbound hscalar htime J hbirth g₀ hzero
      records hfixed hlower G₀ L₀ hsource₀ hterminal₀ Ξ₀ hΞ₀ hprojection₀
      gflow₀ hslabs₀ hlast₀ S₀ hmetric₀ hcurv₀
  have hinj : Function.Injective Ξ := by
    intro x y hxy
    apply hΨ.isEmbedding.injective
    exact (hprojection x).symm.trans ((congrArg Subtype.val hxy).trans (hprojection y))
  have hemb : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      hΞ hinj
  refine ⟨Ξ, hΞ, hemb, ?_, hprojection, hbirth', hrest⟩
  intro p A z hz
  exact H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle G
    J Ξ hbirth' p A z hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
