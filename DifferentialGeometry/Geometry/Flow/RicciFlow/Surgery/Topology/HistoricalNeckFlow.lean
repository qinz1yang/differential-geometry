import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckCurvature
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm

noncomputable section
open Set Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance : IsManifold ThreeModel 1 (H.backwardSurvivorDomain first i.castSucc hle) :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold ThreeModel 1 (H.backwardSurvivorTerminalFace first i hle) :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    IsManifold ThreeModel 1 (H.backwardSurvivorFootprintInterior first i hle K) :=
  IsManifold.of_le (n := ∞) (by decide)

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
  have hj : j.castSucc = k := rfl
  have hn := H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)
  refine ⟨j, hkfirst, hk.le, H.activeStage_time_le tH, ?_⟩
  exact hn.le

private theorem rmNorm_footprint_slab
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc)
    (t : ℝ) (x : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S
      (((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) x 4
      (metricRm04At (((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) x)) =
      Real.sqrt (normSq0S ((H.event j).terminal.extendedMetric t)
        (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hl x.val.val) 4
        (metricRm04At ((H.event j).terminal.extendedMetric t)
          (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hl x.val.val))) := by
  rw [rmNormSq_restrictOpen, rmNormSq_restrictOpen]
  change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4 (metricRm04At (localPullMetric _ _ _) _)) = _
  rw [normSq0S_metricRm04At_localPullMetric]

private theorem rmNorm_footprint_last
    (K : Set (H.event i).incoming.terminalRegularOpen) (t : ℝ)
    (x : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S
      ((H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K)) x 4
      (metricRm04At ((H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K)) x)) =
      Real.sqrt (normSq0S ((H.event i).terminal.extendedMetric t)
        (H.backwardSurvivorFootprintMap first i hle K x) 4
        (metricRm04At ((H.event i).terminal.extendedMetric t)
          (H.backwardSurvivorFootprintMap first i hle K x))) := by
  rw [rmNormSq_restrictOpen]
  change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4 (metricRm04At (localPullMetric _ _ _) _)) = _
  rw [normSq0S_metricRm04At_localPullMetric]
  rfl

private theorem rmNorm_footprint_of_closed_stage_bounds
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (B c : ℝ)
    (hB : ∀ x ∈ K, ∀ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ y : (H.event j).incoming.terminalRegularOpen, y.val = A.point j.castSucc hf hl →
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ), c ≤ t →
        Real.sqrt (normSq0S ((H.event j).terminal.extendedMetric t) y 4
          (metricRm04At ((H.event j).terminal.extendedMetric t) y)) ≤ B)
    {t : ℝ} (ht : t ∈ Icc (H.time first) (H.time i.succ)) (hct : c ≤ t)
    (z : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤ B := by
  let x := H.backwardSurvivorFootprintMap first i hle K z
  have hx : x ∈ K := interior_subset z.property
  let A : BackwardPointTrace H first i.castSucc hle x.val := Classical.choice z.val.val.property
  obtain ⟨j,hf,hl,htj⟩ := exists_closed_stage_of_mem_Icc (hle := hle) ht
  by_cases he : j = i
  · subst j
    rw [hlast t htj, rmNorm_footprint_last]
    exact hB x hx A i hle le_rfl x A.endpoint_eq.symm t htj hct
  · have hjnext : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val ≤ i.val := hl
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    rw [hslabs j hf hjnext t htj, rmNorm_footprint_slab]
    apply hB x hx A j hf hl
      (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hjnext z.val.val)
    · exact H.backwardSurvivorMap_eq_point first i.castSucc hle j.castSucc hf hl z.val.val A
    · exact htj
    · exact hct


private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

theorem NormalizedNeck.exists_historical_footprint_isSolutionOn_curvature_bound
    {δ₀ δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hδ : δ₀ ≤ δ) (hδ1 : δ < 1) (hprecision : δ₀ ≤ eps)
    (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (htrace : ∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ H.time i.succ)
    (htime : 6 * C * (H.time i.succ - c) * N.scale ≤ 1) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen,
      K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} ∧
      IsCompact K ∧ IsConnected K ∧ N.center ∈ K ∧
      range (N.monoDelta hδ hδ1).chart ⊆ interior K ∧
      IsCompact (riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale)) ∧
      riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale) ⊆ interior K ∧
      range (H.backwardSurvivorFootprintMap first i hle K) = interior K ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
        (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
          G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K)) ∧
        G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
          (H.backwardSurvivorFootprintMap first i hle K)
          (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
        IsSolutionOn ({ base := { metric := G } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
            (RealTimeInterval.closed c (H.time i.succ) hcs)) ∧
        ∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
          normSq0S (G t) x 4 (metricRm04At (G t) x) ≤
            (4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)) ^ 2 := by
  obtain ⟨K,hK,hcompact,hconn,hcenter,hchart,hball,hballsub,hscalar,hinterior,hclosed⟩ :=
    N.exists_compact_footprint_historical_curvature_bound hδ hδ1 hprecision hsmall hk
      a ha hpublic hfit hq hqQ hPhi first hle hbound hpinch
  have htraceK : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
    intro x hx
    exact htrace x (hK ▸ hx)
  obtain ⟨G,hslabs,hlast,hterminal,hsm,hsol⟩ :=
    H.exists_backwardSurvivorFootprint_isSolutionOn first i hle K
  refine ⟨K,hK,hcompact,hconn,hcenter,hchart,hball,hballsub,
    H.range_backwardSurvivorFootprintMap first i hle K htraceK,
    G,hslabs,hlast,hterminal,?_,?_⟩
  · exact isSolutionOn_timeRestrict hsol
      (fun t ht => ⟨hc.trans ht.1,ht.2⟩) (fun t ht => ⟨hc.trans_lt ht.1,ht.2⟩)
  · intro t ht z
    have hb : Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤
        4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) := by
      apply rmNorm_footprint_of_closed_stage_bounds K G hslabs hlast
        (4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)) c ?_
        ⟨hc.trans ht.1,ht.2⟩ ht.1 z
      intro x hx A j hf hl y hy u hu hcu
      have htime' : 6 * C * (H.time i.succ - u) * N.scale ≤ 1 := by
        apply le_trans _ htime
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_sub_left hcu _) (by positivity)) N.scale_pos.le
      exact (hclosed x hx A j hf hl y hy u hu htime').2.1
    exact (Real.sqrt_le_iff.mp hb).2


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
