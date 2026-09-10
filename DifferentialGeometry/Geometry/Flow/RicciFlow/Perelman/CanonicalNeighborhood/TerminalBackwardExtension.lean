import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

section FlowOn

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]

def flowOn (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I3 N) :
    SolutionOn (I := I3) (M := N) D :=
  { base := { metric := g } }

omit [T2Space N] [SigmaCompactSpace N] in
@[simp] theorem flowOn_metric (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I3 N) (t : ℝ) :
    (flowOn (N := N) D g).base.metric t = g t :=
  rfl

end FlowOn

structure StaticTerminalLimit (X : FlowSequence.{u}) (depthBound : ℝ) where
  carrier_window : ∀ i, Set.Icc (-depthBound) 0 ⊆ (X.interval i).carrier
  regular_window : ∀ i, Set.Ioo (-depthBound) 0 ⊆ (X.interval i).regular
  space : PointedRiemannianManifold.{u, 0, 0} I3
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : PointedRiemannianConvergenceMaps (X.atTime 0) space subseq
  converges : MetricConvergenceData maps
  canonical_domains : ∀ k,
    converges.domain k = CanonicalMetricCompactness.canonicalSourceData maps k
  capture : MetricSourceCapture maps
  precompact : ∀ i, IsCompact (closure (maps.partialDiffeomorph i).source)
  connected_domains : ∀ i, IsConnected (maps.partialDiffeomorph i).source
  nested : ∀ i,
    closure (maps.partialDiffeomorph i).source ⊆ (maps.partialDiffeomorph (i + 1)).source
  connected : ConnectedSpace space.M
  complete : MetricComplete space
  nonnegative : SecLower space.metric 0 Set.univ
  slab_bounds : ∀ K : Set space.M, IsCompact K → ∀ width : ℝ, 0 < width →
    width < depthBound → ∃ C : ℝ, ∀ᶠ i in Filter.atTop,
      ∀ t ∈ Set.Icc (-width) 0, ∀ y ∈ K,
        PointedFlowData.rmNormSq (X.term (subseq i)) t ((maps.partialDiffeomorph i) y) ≤ C

theorem StaticTerminalLimit.window_subset_carrier {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hle : delta ≤ depthBound) (i : ℕ) :
    Set.Icc (-delta) 0 ⊆ (X.interval i).carrier :=
  (Set.Icc_subset_Icc (by linarith) le_rfl).trans (L.carrier_window i)

theorem StaticTerminalLimit.open_window_subset_regular {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hle : delta ≤ depthBound) (i : ℕ) :
    Set.Ioo (-delta) 0 ⊆ (X.interval i).regular :=
  (Set.Ioo_subset_Ioo (by linarith) le_rfl).trans (L.regular_window i)

structure TerminalBackwardSlab {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (D : RealTimeInterval) where
  solution : SolutionOn (I := I3) (M := L.space.M) D
  isSolution : IsSolutionOn solution
  terminal : solution.base.metric 0 = L.space.metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  convergence : ConvergesOn (subsequenceMaps L.maps subseq strictMono) solution
  complete : ∀ t ∈ D.carrier,
    MetricComplete { L.space with metric := solution.base.metric t }
  nonnegative : ∀ t ∈ D.carrier, SecLower (solution.base.metric t) 0 Set.univ
  compact_time_bound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, FlowMetricBall.rmNormSq solution t x ≤ C

def TerminalBackwardSlab.pointed {X : FlowSequence.{u}} {depthBound : ℝ}
    {L : StaticTerminalLimit X depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab L D) : PointedFlowData.{u, 0, 0} I3 D where
  M := L.space.M
  topology := L.space.topology
  charted := L.space.charted
  smooth := L.space.smooth
  sigmaCompact := L.space.sigmaCompact
  t2 := L.space.t2
  t2TangentBundle := L.space.t2TangentBundle
  basepoint := L.space.basepoint
  S := B.solution
  isSolution := B.isSolution

theorem TerminalBackwardSlab.pointed_atTime_zero {X : FlowSequence.{u}} {depthBound : ℝ}
    {L : StaticTerminalLimit X depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab L D) : B.pointed.atTime 0 = L.space :=
  congrArg
    (fun m =>
      ({ M := L.space.M
         topology := L.space.topology
         charted := L.space.charted
         smooth := L.space.smooth
         sigmaCompact := L.space.sigmaCompact
         t2 := L.space.t2
         t2TangentBundle := L.space.t2TangentBundle
         basepoint := L.space.basepoint
         metric := m } : PointedRiemannianManifold.{u, 0, 0} I3))
    B.terminal

def IsSlabLimit {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧ ∃ k : ℕ → ℕ, ∃ hk : StrictMono k,
    ConvergesOn (subsequenceMaps L.maps k hk)
      (flowOn (N := L.space.M)
        (RealTimeInterval.closed (-delta) 0 (by linarith)) g)

def SlabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (k : ℕ → ℕ)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
    Set.Icc a b ⊆ Set.Icc (-delta) 0 → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps →
      ∀ᶠ i in Filter.atTop,
        Nonempty (MetricComparisonOn (fun s => g s)
          (fun s => (X.term (L.subseq (k i))).S.base.metric s)
          (L.maps.partialDiffeomorph (k i)) K (Set.Icc a b) order eps)

theorem convergesOn_of_slabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) :
    ConvergesOn (subsequenceMaps L.maps k hk)
      (flowOn (N := L.space.M)
        (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  intro K hK a b hab hsub order eps heps
  obtain ⟨k0, hk0⟩ := L.maps.source_subset hK
  filter_upwards [hcomp K hK a b hab hsub order eps heps,
    Filter.eventually_ge_atTop k0] with i hi hik0
  refine ⟨fun t ht => L.window_subset_carrier hle _ (hsub ht), ?_, hi⟩
  exact hk0 (k i) (hik0.trans (StrictMono.le_apply hk))

theorem isSlabLimit_of_slabComparison {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} (hg0 : g 0 = L.space.metric)
    (hcomp : SlabComparison L delta k g) :
    IsSlabLimit L delta hd g :=
  ⟨hg0, k, hk, convergesOn_of_slabComparison L hd hle hk hcomp⟩

def SlabLimitExists {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, g 0 = L.space.metric ∧
    ∃ k : ℕ → ℕ, StrictMono k ∧ SlabComparison L delta k g

def SlabLimitIsFlow {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    IsSolutionOn (flowOn (N := L.space.M)
      (RealTimeInterval.closed (-delta) 0 (by linarith)) g)

def SlabLimitSliceGeometry {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    (∀ t ∈ Set.Icc (-delta) 0, MetricComplete { L.space with metric := g t }) ∧
      ∀ t ∈ Set.Icc (-delta) 0, SecLower (g t) 0 Set.univ

def SlabLimitCurvatureBound {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc (-delta) 0 → ∃ C : ℝ,
      ∀ t ∈ Set.Icc a b, ∀ x : L.space.M,
        FlowMetricBall.rmNormSq (flowOn (N := L.space.M)
          (RealTimeInterval.closed (-delta) 0 (by linarith)) g) t x ≤ C

theorem exists_terminalBackwardFlow_of_delta {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound)
    (h1 : SlabLimitExists L delta) (h2 : SlabLimitIsFlow L delta hd) :
    ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M,
      IsSlabLimit L delta hd g ∧
        IsSolutionOn (flowOn (N := L.space.M)
          (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  obtain ⟨g, hg0, k, hk, hcomp⟩ := h1
  have hlim : IsSlabLimit L delta hd g :=
    isSlabLimit_of_slabComparison L hd hle hk hg0 hcomp
  exact ⟨g, hlim, h2 g hlim⟩

theorem exists_terminalBackwardSlab_of_delta {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} (hd : 0 < delta)
    (hle : delta ≤ depthBound)
    (h1 : SlabLimitExists L delta) (h2 : SlabLimitIsFlow L delta hd)
    (h3 : SlabLimitSliceGeometry L delta hd) (h4 : SlabLimitCurvatureBound L delta hd) :
    Nonempty (TerminalBackwardSlab L
      (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨g, hlim, hflow⟩ := exists_terminalBackwardFlow_of_delta L hd hle h1 h2
  have hgeometry := h3 g hlim
  have hbound := h4 g hlim
  obtain ⟨hg0, k, hk, hconv⟩ := hlim
  refine ⟨{ solution := flowOn (N := L.space.M)
              (RealTimeInterval.closed (-delta) 0 (by linarith)) g
            isSolution := hflow
            terminal := hg0
            subseq := k
            strictMono := hk
            convergence := hconv
            complete := ?_
            nonnegative := ?_
            compact_time_bound := ?_ }⟩
  · exact fun t ht => hgeometry.1 t ht
  · exact fun t ht => hgeometry.2 t ht
  · exact fun a b hab hsub => hbound a b hab hsub

def TerminalSlabAnalyticInputs {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) : Prop :=
  ∃ delta : ℝ, ∃ hd : 0 < delta, delta ≤ depthBound ∧
    SlabLimitExists L delta ∧ SlabLimitIsFlow L delta hd ∧
      SlabLimitSliceGeometry L delta hd ∧ SlabLimitCurvatureBound L delta hd

theorem exists_terminalBackwardSlab {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (h : TerminalSlabAnalyticInputs L) :
    ∃ delta : ℝ, ∃ hd : 0 < delta,
      Nonempty (TerminalBackwardSlab L
        (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨delta, hd, hle, h1, h2, h3, h4⟩ := h
  exact ⟨delta, hd, exists_terminalBackwardSlab_of_delta L hd hle h1 h2 h3 h4⟩

theorem terminalJetContinuous_of_terminalBackwardSlab
    {X : FlowSequence.{u}}
    {depthBound : ℝ} {L : StaticTerminalLimit X depthBound} {delta : ℝ}
    (hd : 0 < delta)
    (B : TerminalBackwardSlab L (RealTimeInterval.closed (-delta) 0 (by linarith))) :
    TerminalJetContinuous (I := I3) B.pointed 0 := by
  intro k x v
  exact solution_nablaKRm04_eval_continuousWithinAt_terminal
    B.solution B.isSolution (a := -delta) (b := 0)
    (by linarith) (fun t ht => ht) (fun t ht => ht) k x v

def FlowSequence.ofPointedFlowSeq (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) :
    FlowSequence.{u} where
  interval _ := Y.D
  term i := Y.term i

@[simp] theorem FlowSequence.ofPointedFlowSeq_interval
    (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) (i : ℕ) :
    (FlowSequence.ofPointedFlowSeq Y).interval i = Y.D :=
  rfl

@[simp] theorem FlowSequence.ofPointedFlowSeq_atTime
    (Y : PointedFlowSeq.{u, 0, 0} (I := I3)) (t : ℝ) :
    (FlowSequence.ofPointedFlowSeq Y).atTime t = Y.atTime t :=
  rfl

theorem ancient_carrier_window {a : ℝ} : Set.Icc a 0 ⊆ ancientTimeInterval.carrier :=
  fun _ ht => ht.2

theorem ancient_regular_window {a : ℝ} : Set.Ioo a 0 ⊆ ancientTimeInterval.regular :=
  fun _ ht => ht.2

def TerminalSlabBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    (depthBound : ℝ) : Prop :=
  ∀ K : Set L.space.M, IsCompact K → ∀ width : ℝ, 0 < width →
    width < depthBound → ∃ C : ℝ, ∀ᶠ i in Filter.atTop,
      ∀ t ∈ Set.Icc (-width) 0, ∀ y ∈ K,
        PointedFlowData.rmNormSq (Y.term (L.subseq i)) t
          ((L.maps.partialDiffeomorph i) y) ≤ C

def TerminalLimit.toStatic {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    {depthBound : ℝ} (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound) :
    StaticTerminalLimit Y.toFlowSequence depthBound where
  carrier_window i := by
    rw [Y.carrier_eq i]
    have h := Y.depth_buffer i
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  regular_window i := by
    rw [Y.regular_eq i]
    have h := Y.depth_buffer i
    exact Set.Ioo_subset_Ioo (by linarith) le_rfl
  space := L.space
  subseq := L.subseq
  strictMono := L.strictMono
  maps := L.maps
  converges := L.converges
  canonical_domains := L.canonical_domains
  capture := L.capture
  precompact := L.precompact
  connected_domains := L.connected_domains
  nested := L.nested
  connected := L.connected
  complete := L.complete
  nonnegative := L.nonnegative
  slab_bounds := hb

def TerminalBackwardSlab.toBackwardExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit Y}
    {depthBound : ℝ} {hdepth : depthBound ≤ 2 * modelDepth eps}
    {hb : TerminalSlabBounds L depthBound} {D : RealTimeInterval}
    (B : TerminalBackwardSlab (L.toStatic hdepth hb) D) : BackwardExtension L D where
  solution := B.solution
  isSolution := B.isSolution
  terminal := B.terminal
  subseq := B.subseq
  strictMono := B.strictMono
  convergence := B.convergence
  complete := B.complete
  nonnegative := B.nonnegative
  compact_time_bound := B.compact_time_bound

theorem first_backward_slab_of_terminal {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit Y)
    {depthBound : ℝ} (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound)
    (h : TerminalSlabAnalyticInputs (L.toStatic hdepth hb)) :
    ∃ delta : ℝ, ∃ hd : 0 < delta,
      Nonempty (BackwardExtension L
        (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨delta, hd, hslab⟩ := exists_terminalBackwardSlab (L.toStatic hdepth hb) h
  exact ⟨delta, hd, ⟨TerminalBackwardSlab.toBackwardExtension hslab.some⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
