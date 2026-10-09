import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckScalarTime
import DifferentialGeometry.Analysis.Calculus.Derivative.Bounds
import DifferentialGeometry.Analysis.ODE.QuadraticBackwardBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_event_of_mem_Ioo_not_mem_range
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount)
    {t : ℝ} (ht : t ∈ Ioo (H.time first) (H.time i.succ))
    (hne : t ∉ Set.range H.time) :
    ∃ j : Fin H.eventCount, first ≤ j.castSucc ∧ j.castSucc ≤ i.castSucc ∧
      t ∈ Ioo (H.time j.castSucc) (H.time j.succ) := by
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1.le, ht.2.le.trans (H.time_le_horizon_at i.succ)⟩
  let k := H.activeStage tH
  have hk : k < i.succ := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt ht.2
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1.le
  let j : Fin H.eventCount := ⟨k.val, by
    have := i.isLt
    change k.val < H.eventCount
    have hkv : k.val < i.val + 1 := hk
    omega⟩
  refine ⟨j, hkfirst, ?_, ?_⟩
  · change k.val ≤ i.val
    have hkv : k.val < i.val + 1 := hk
    omega
  · refine ⟨lt_of_le_of_ne (H.activeStage_time_le tH) ?_, ?_⟩
    · intro he
      apply hne
      exact ⟨j.castSucc, he⟩
    · exact H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)

private local instance {H : ObservedHistory.{u}}
    {first : Fin (H.eventCount + 1)} {i : Fin H.eventCount} {hle : first ≤ i.castSucc}
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let _ : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let _ : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

private theorem abs_derivWithin_scalar_localPullback_le_of_mem_slab
    {E J M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace J] {I : ModelWithCorners ℝ E J}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace J M]
    [IsManifold I ∞ M] [T2Space M]
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ i.castSucc), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (Phi : M → H.backwardSurvivorFootprintInterior first i hle K)
    (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {Q θ q : ℝ} {C : ℝ≥0} (hQ : 0 < Q)
    (hmetric : ∀ s ∈ Icc (-θ) 0, S.base.metric s =
      localPullMetric (scaleMetric Q hQ (G (H.time i.succ + s / Q))) Phi hPhi)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {s : ℝ} (hs : s ∈ Ioo (-θ) 0)
    (ht : H.time i.succ + s / Q ∈ Ioo (H.time j.castSucc) (H.time j.succ))
    (hbound : ∀ x : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (x : M) (hhigh : q / Q < S.scalar s x) :
    |derivWithin (fun v => S.scalar v x) (Iic s) s| ≤ C * S.scalar s x ^ 2 := by
  let y := H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl (Phi x).val.val
  let r := fun t => (H.event j).incoming.flow.scalar t y
  have heq : (fun v => S.scalar v x) =ᶠ[𝓝 s]
      (fun v => Q⁻¹ * r (H.time i.succ + v / Q)) := by
    have htime : ContinuousAt (fun v : ℝ => H.time i.succ + v / Q) s := by fun_prop
    filter_upwards [Ioo_mem_nhds hs.1 hs.2,
      htime.eventually (Ioo_mem_nhds ht.1 ht.2)] with v hv htv
    change metricScalarAt (S.base.metric v) x = _
    rw [hmetric v ⟨hv.1.le,hv.2.le⟩, metricScalarAt_localPull, metricScalarAt_scaleMetric,
      H.metricScalarAt_backwardSurvivorFootprint first i hle K G hslabs hlast
        j hf hl ⟨htv.1.le,htv.2⟩ (Phi x)]
  have hdiff : DifferentiableWithinAt ℝ r (Iic (H.time i.succ + s / Q))
      (H.time i.succ + s / Q) :=
    ((H.event j).incoming.equation.scalarTime ht Ioo_subset_Ico_self y).differentiableAt
      (Ioo_mem_nhds ht.1 ht.2) |>.differentiableWithinAt
  rw [heq.derivWithin_eq_of_nhds, heq.eq_of_nhds]
  apply DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq hQ hdiff
    (hbound y _ ht)
  rwa [← heq.eq_of_nhds]

theorem abs_derivWithin_scalar_parabolic_backwardSurvivorFootprint_le
    {E J M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace J] {I : ModelWithCorners ℝ E J}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace J M]
    [IsManifold I ∞ M] [T2Space M]
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ i.castSucc), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (Phi : M → H.backwardSurvivorFootprintInterior first i hle K)
    (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {Q θ q : ℝ} {C : ℝ≥0} (hQ : 0 < Q)
    (hmetric : ∀ s ∈ Icc (-θ) 0, S.base.metric s =
      localPullMetric (scaleMetric Q hQ (G (H.time i.succ + s / Q))) Phi hPhi)
    (hS : IsSolutionOn S) (hcarrier : Ioo (-θ) 0 ⊆ D.carrier)
    (hstart : H.time first ≤ H.time i.succ - θ / Q)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    {s : ℝ} (hs : s ∈ Ioo (-θ) 0) (x : M) (hhigh : q / Q < S.scalar s x) :
    |derivWithin (fun v => S.scalar v x) (Iic s) s| ≤ C * S.scalar s x ^ 2 := by
  let A : Set ℝ := (fun τ => Q * (τ - H.time i.succ)) '' Set.range H.time
  have hA : A.Finite := (Set.finite_range H.time).image _
  have hdiff (v : ℝ) (hv : v ∈ Ioo (-θ) 0) :
      DifferentiableAt ℝ (fun w => S.scalar w x) v :=
    (hS.scalarTime hv hcarrier x).differentiableAt (Ioo_mem_nhds hv.1 hv.2)
  have hderiv (v : ℝ) (hv : v ∈ Ioo (-θ) 0) :
      derivWithin (fun w => S.scalar w x) (Iic v) v = deriv (fun w => S.scalar w x) v :=
    (hdiff v hv).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic v)
  rw [hderiv s hs]
  apply DifferentialGeometry.Analysis.abs_deriv_le_quadratic_of_finite_exception
    hA hdiff ?_ s hs hhigh
  intro v hv hvA hvhigh
  have hphysical : H.time i.succ + v / Q ∈ Ioo (H.time first) (H.time i.succ) := by
    have hlo := div_lt_div_of_pos_right hv.1 hQ
    have hhi := div_neg_of_neg_of_pos hv.2 hQ
    simp only [neg_div] at hlo
    constructor <;> linarith
  have hnot : H.time i.succ + v / Q ∉ Set.range H.time := by
    intro ht
    apply hvA
    refine ⟨H.time i.succ + v / Q, ht, ?_⟩
    dsimp only
    field_simp
    ring
  obtain ⟨j, hf, hl, hj⟩ := exists_event_of_mem_Ioo_not_mem_range H first i hphysical hnot
  rw [← hderiv v hv]
  exact abs_derivWithin_scalar_localPullback_le_of_mem_slab H first i hle K G hslabs hlast
    Phi hPhi S hQ hmetric j hf hl hv hj (hbound j hf hl) x hvhigh

theorem scalar_le_max_at_time_of_backwardSurvivorFootprint_strongNeck
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ i.castSucc), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hS : IsSolutionOn S) {a b q : ℝ}
    (hmetric : ∀ r ∈ Icc a b, S.base.metric r = G r)
    (hstrip : Icc a b ⊆ D.carrier)
    (x : H.backwardSurvivorFootprintInterior first i hle K)
    (hneck : ∀ r ∈ Ioo a b, q < S.scalar r x → ∃ eps : ℝ, Nonempty (Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck S eps x r))
    (hregular : ∀ r ∈ Ioo a b, q < S.scalar r x → ∀ s ∈ Ioo (-1 : ℝ) 0,
      parabolicTime r (S.scalar r x) s ∈ D.regular)
    (j k : Fin H.eventCount) (hjf : first ≤ j.castSucc) (hji : j.castSucc ≤ i.castSucc)
    (hkf : first ≤ k.castSucc) (hki : k.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ Icc a b)
    (htj : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hbk : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) :
    (H.event j).incoming.flow.scalar t
      (H.backwardSurvivorMap first i.castSucc hle j.castSucc hjf hji x.val.val) ≤
      max q ((H.event k).incoming.flow.scalar b
        (H.backwardSurvivorMap first i.castSucc hle k.castSucc hkf hki x.val.val)) := by
  have hh := Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_max_terminal_of_strongNeck_above hS x hstrip hneck hregular ht
  change metricScalarAt (S.base.metric t) x ≤ max q (metricScalarAt (S.base.metric b) x) at hh
  rw [hmetric t ht, hmetric b ⟨ht.1.trans ht.2,le_rfl⟩,
    H.metricScalarAt_backwardSurvivorFootprint first i hle K G hslabs hlast j hjf hji htj x,
    H.metricScalarAt_backwardSurvivorFootprint first i hle K G hslabs hlast k hkf hki hbk x] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
