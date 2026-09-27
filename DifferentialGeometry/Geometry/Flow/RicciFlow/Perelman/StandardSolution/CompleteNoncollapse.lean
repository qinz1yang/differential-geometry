import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ConnectedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ComponentBallTransfer
import DifferentialGeometry.Geometry.Metric.ConnectedComponentInjectivity
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem fixed_terminal_ball_noncollapsed_complete
    (H K c : ℝ) (hH : 0 < H) (hK : 0 < K) (hc : 0 < c)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (time : RealTimeInterval.FlowTime D) (hT : 0 < (time : ℝ)) (hTH : (time : ℝ) ≤ H)
    (hnonneg : D.carrier ⊆ Ici (0 : ℝ))
    (hcarrier : Icc (0 : ℝ) (time : ℝ) ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) (time : ℝ) ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hbounded : ∃ Q : ℝ, ∀ t ∈ Icc (0 : ℝ) (time : ℝ), ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q)
    (hinit : ∀ z : M,
      Real.sqrt (normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0)
        (hcomplete 0 ⟨le_rfl, hT.le⟩) p)
    (B : FlowMetricBall S time)
    (hballSlab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hRm : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      B.radius ^ 4 * FlowMetricBall.rmNormSq S t z ≤ 1) :
    B.IsKappaNoncollapsed
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) := by
  let C := connectedComponentOpen (I := I) B.center
  let : SigmaCompactSpace C :=
    (isClosed_connectedComponent (x := B.center)).sigmaCompactSpace
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := I) B.center
  let : T2Space (TangentBundle I C) := inferInstance
  let SC : SolutionOn (I := I) (M := C) D := solutionOnRestrictOpen (I := I) S C
  let BC : FlowMetricBall SC time := FlowMetricBall.onConnectedComponent B
  have hSC : IsSolutionOn SC := isSolutionOn_restrict_connCompOpen S hS B.center
  have hcompleteC : ∀ t ∈ Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (SC.base.metric t) := by
    intro t ht
    exact riemannianMetricComplete_restrictOpen_connCompOpen
      (I := I) (S.base.metric t) B.center (hcomplete t ht)
  have hnormC (t : ℝ) (x : C) :
      FlowMetricBall.rmNormSq SC t x = FlowMetricBall.rmNormSq S t (x : M) :=
    rmNormSq_restrict_connCompOpen S B.center t x
  have hboundedC : ∃ Q : ℝ, ∀ t ∈ Icc (0 : ℝ) (time : ℝ), ∀ z : C,
      normSq0S (I := I) (SC.base.metric t) z 4 (SC.base.rm04 t z) ≤ Q := by
    obtain ⟨Q, hQ⟩ := hbounded
    refine ⟨Q, ?_⟩
    intro t ht z
    change FlowMetricBall.rmNormSq SC t z ≤ Q
    rw [hnormC]
    exact hQ t ht (z : M)
  have hinitC : ∀ z : C,
      Real.sqrt (normSq0S (I := I) (SC.base.metric 0) z 4 (SC.base.rm04 0 z)) ≤ K := by
    intro z
    change Real.sqrt (FlowMetricBall.rmNormSq SC 0 z) ≤ K
    rw [hnormC]
    exact hinit (z : M)
  have hInjC : ∀ p : C, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (SC.base.metric 0)
        (hcompleteC 0 ⟨le_rfl, hT.le⟩) p := by
    intro p
    exact (hInj (p : M)).trans
      (intrinsicInjectivityRadiusOf_le_restrictOpen_connCompOpen (I := I)
        (S.base.metric 0) (hcomplete 0 ⟨le_rfl, hT.le⟩) B.center p)
  obtain ⟨hballSlabC, hRmC⟩ :=
    FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent B hballSlab hRm
  have hBC : BC.IsKappaNoncollapsed
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) :=
    fixed_terminal_ball_noncollapsed_connected H K c hH hK hc SC hSC time hT hTH
      hnonneg hcarrier hregular hcompleteC hboundedC hinitC hInjC BC hballSlabC hRmC
  exact (FlowMetricBall.onConnectedComponent_noncollapsed_iff B
    (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c)).mp hBC

end DifferentialGeometry.PDE.RicciFlow

end
