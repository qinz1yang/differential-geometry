import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.TerminalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FlowConvergenceAssembly

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.convergesOn_of_halfLineMetricConvergenceData
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : ConnectedSpace P.limit.M)
    (hprecompact : ∀ i, IsCompact (closure (P.maps.source i)))
    (hsourceconn : ∀ i, IsConnected (P.maps.source i))
    (hnested : ∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1))
    (hcapture : MetricSourceCapture P.maps)
    (hnonnegative : SecLower P.limit.metric 0 Set.univ)
    (hzero : ∀ i, 0 ∈ (X.interval i).carrier)
    (hwindow : ∀ A : ℝ, ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (X.interval i).carrier ∧ Ioo (-A) 0 ⊆ (X.interval i).regular)
    {C : ℝ} (hcurv : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ y, PointedFlowData.rmNormSq (X.term i) t y ≤ C)
    {bf : BumpFamily (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {hsrc : SourceIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {htgt : TargetIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    (co : HalfLineMetricConvergenceData (FlowSequence.singletonTimeMaps P.maps 0 hzero)
      P.limit.metric bf hsrc htgt) :
    ConvergesOn (subsequenceMaps P.maps co.φ co.strictMono)
      (flowOn (N := P.limit.M) ancientTimeInterval co.gInf) := by
  apply convergesOn_of_eventually_metricComparisonOn
    (subsequenceMaps P.maps co.φ co.strictMono)
    (flowOn (N := P.limit.M) ancientTimeInterval co.gInf)
  · intro a b hab hsub
    have hb : b ≤ 0 := by
      simpa only [ancientTimeInterval_carrier, mem_Iic] using hsub (right_mem_Icc.mpr hab)
    filter_upwards [(P.strictMono.comp co.strictMono).tendsto_atTop.eventually
      (hwindow (|a| + 1))] with i hi
    intro t ht
    exact hi.1 ⟨by linarith [neg_le_abs a, ht.1], ht.2.trans hb⟩
  · intro K hK a b hab hsub order epsilon hepsilon
    have hb : b ≤ 0 := by
      simpa only [ancientTimeInterval_carrier, mem_Iic] using hsub (right_mem_Icc.mpr hab)
    let delta : ℝ := |a| + 1
    have hd : 0 < delta := by dsimp only [delta]; positivity
    have hw : 0 < delta + 1 := by linarith
    have hwd : delta + 1 < delta + 2 := by linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((P.strictMono.comp co.strictMono).tendsto_atTop.eventually (hwindow (delta + 2)))
    let k : ℕ → ℕ := fun i => co.φ (i + N)
    have hk : StrictMono k := co.strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
    have hcarrier : ∀ i, Icc (-(delta + 2)) 0 ⊆
        (X.interval (P.subseq (k i))).carrier := fun i => (hN (i + N) (by omega)).1
    have hregular : ∀ i, Ioo (-(delta + 2)) 0 ⊆
        (X.interval (P.subseq (k i))).regular := fun i => (hN (i + N) (by omega)).2
    let L := MetricCompactLimit.staticTerminalLimitOfWindow P hcanonical hconnected
      hprecompact hsourceconn hnested hcapture hnonnegative k hk hcarrier hregular hcurv
    obtain ⟨cg, ksrc, ktgt, hconv⟩ :=
      MetricCompactLimit.window_bumpMetricConvergence_of_halfLine P hcanonical hconnected
        hprecompact hsourceconn hnested hcapture hnonnegative hzero co hw hwd N
        hcarrier hregular hcurv
    have hslab := L.slabComparison_of_bumpMetricConvergence hw hwd
      cg ksrc ktgt strictMono_id hconv hd (by linarith : delta < delta + 1)
    have hsub' : Icc a b ⊆ Icc (-delta) 0 := by
      intro t ht
      exact ⟨by dsimp only [delta]; linarith [neg_le_abs a, ht.1], ht.2.trans hb⟩
    have htail := hslab K hK a b hab hsub' order epsilon hepsilon
    obtain ⟨J, hJ⟩ := eventually_atTop.mp htail
    refine eventually_atTop.mpr ⟨J + N, fun i hi => ?_⟩
    have hNi : N ≤ i := by omega
    obtain ⟨j, rfl⟩ : ∃ j, i = j + N := ⟨i - N, (Nat.sub_add_cancel hNi).symm⟩
    exact hJ j (by omega)

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.isSolutionOn_of_halfLineMetricConvergenceData
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : ConnectedSpace P.limit.M)
    (hprecompact : ∀ i, IsCompact (closure (P.maps.source i)))
    (hsourceconn : ∀ i, IsConnected (P.maps.source i))
    (hnested : ∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1))
    (hcapture : MetricSourceCapture P.maps)
    (hnonnegative : SecLower P.limit.metric 0 Set.univ)
    (hzero : ∀ i, 0 ∈ (X.interval i).carrier)
    (hwindow : ∀ A : ℝ, ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (X.interval i).carrier ∧ Ioo (-A) 0 ⊆ (X.interval i).regular)
    {C : ℝ} (hcurv : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ y, PointedFlowData.rmNormSq (X.term i) t y ≤ C)
    {bf : BumpFamily (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {hsrc : SourceIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {htgt : TargetIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    (co : HalfLineMetricConvergenceData (FlowSequence.singletonTimeMaps P.maps 0 hzero)
      P.limit.metric bf hsrc htgt) :
    IsSolutionOn (flowOn (N := P.limit.M) ancientTimeInterval co.gInf) := by
  apply isSolutionOn_of_closed_backward_windows
    (flowOn (N := P.limit.M) ancientTimeInterval co.gInf)
    (T := 0) (by intro t ht; exact ht)
  intro n
  let width : ℝ := ((n + 1 : ℕ) : ℝ)
  have hw : 0 < width := by dsimp only [width]; positivity
  have hwd : width < width + 1 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((P.strictMono.comp co.strictMono).tendsto_atTop.eventually (hwindow (width + 1)))
  let k : ℕ → ℕ := fun i => co.φ (i + N)
  have hk : StrictMono k := co.strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hcarrier : ∀ i, Icc (-(width + 1)) 0 ⊆
      (X.interval (P.subseq (k i))).carrier := fun i => (hN (i + N) (by omega)).1
  have hregular : ∀ i, Ioo (-(width + 1)) 0 ⊆
      (X.interval (P.subseq (k i))).regular := fun i => (hN (i + N) (by omega)).2
  let L := MetricCompactLimit.staticTerminalLimitOfWindow P hcanonical hconnected
    hprecompact hsourceconn hnested hcapture hnonnegative k hk hcarrier hregular hcurv
  obtain ⟨cg, ksrc, ktgt, hconv⟩ :=
    MetricCompactLimit.window_bumpMetricConvergence_of_halfLine P hcanonical hconnected
      hprecompact hsourceconn hnested hcapture hnonnegative hzero co hw hwd N
      hcarrier hregular hcurv
  have hflow := L.isSolutionOn_of_bumpMetricConvergence hw hwd
    cg ksrc ktgt strictMono_id hconv
  apply isSolutionOn_timeRestrict hflow
  · intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.terminal_metric_eq_of_halfLineMetricConvergenceData
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hzero : ∀ i, 0 ∈ (X.interval i).carrier)
    {bf : BumpFamily (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {hsrc : SourceIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {htgt : TargetIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    (co : HalfLineMetricConvergenceData (FlowSequence.singletonTimeMaps P.maps 0 hzero)
      P.limit.metric bf hsrc htgt) :
    co.gInf 0 = P.limit.metric := by
  let Φ := FlowSequence.singletonTimeMaps P.maps 0 hzero
  let coZero : FlowMetricConvergenceData Φ P.limit.metric bf hsrc htgt 0 0 := {
    φ := co.φ
    strictMono := co.strictMono
    gInf := co.gInf
    convergence := by simpa only [Nat.cast_zero, neg_zero] using (co.convergenceOn 0).convergence
    convergencePt := by simpa only [Nat.cast_zero, neg_zero] using (co.convergenceOn 0).convergencePt }
  apply gInf_zero_eq Φ P.limit.metric bf hsrc htgt 0 0 coZero
    ⟨le_rfl, le_rfl⟩ P.limit.metric
  intro x v w epsilon hepsilon
  have hconv0 : ∀ K : Set P.limit.M, IsCompact K →
      metricSourceConvergesOn P.maps
        (CanonicalMetricCompactness.canonicalSourceData P.maps) K 0 := by
    intro K hK
    have h := P.convergence.metrics.converges K hK 0
    rwa [show P.convergence.metrics.domain = CanonicalMetricCompactness.canonicalSourceData P.maps
      from funext hcanonical] at h
  have hh := pointed_metric_inner_tendsto hconv0 x v w
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh epsilon hepsilon
  refine ⟨N, fun i hi hx => ?_⟩
  rw [KappaSolutions.pointed_srcMetric_inner_eq_pullback]
  exact (Real.dist_eq _ _ ▸ hN i hi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
