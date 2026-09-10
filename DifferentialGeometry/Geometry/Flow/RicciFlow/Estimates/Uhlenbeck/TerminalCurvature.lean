import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.KernelEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FrameExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorHeatReaction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Matrix BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance terminalUhlenbeckC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalUhlenbeckC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalUhlenbeckC3 : IsManifold I 3 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem solution_uhlenbeckCurvatureMatrix_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (x : M)
    (hiota : ∀ i j, ContinuousWithinAt (fun t => iota t x i j) (Set.Iio b) b) :
    ContinuousWithinAt
      (fun t => uhlenbeckCurvatureOperatorMatrixAsMatrix
        (uhlenbeckPullbackRmInFrame iota
          (fun t x i j k l => tensor04StandardAt (S.base.rm04 t x)
            (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))) t x)
      (Set.Iio b) b := by
  have hdim : Module.finrank ℝ E = 3 := by
    calc
      Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) :=
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.finrank_eq.symm
      _ = 3 := by simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (basisAt x)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hRm (i j k l : Fin 3) : ContinuousWithinAt
      (fun t => tensor04StandardAt (S.base.rm04 t x)
        (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l)) (Set.Iio b) b := by
    have h := solution_nablaKRm04_eval_continuousWithinAt_terminal
      S hS hab hslab hreg 0 x
      (vec4 (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))
    simpa only [nablaKRm04Field_zero, tensor04StandardAt] using
      h.mono Set.Iio_subset_Iic_self
  refine continuousWithinAt_pi.mpr fun i => continuousWithinAt_pi.mpr fun j => ?_
  change ContinuousWithinAt
    (fun t => ∑ p : Fin 3, ∑ q : Fin 3, ∑ r : Fin 3, ∑ s : Fin 3,
      iota t x (bivectorIndex3 i).1 p * iota t x (bivectorIndex3 i).2 q *
        iota t x (bivectorIndex3 j).2 r * iota t x (bivectorIndex3 j).1 s *
        tensor04StandardAt (S.base.rm04 t x)
          (basisAt x p) (basisAt x q) (basisAt x r) (basisAt x s)) (Set.Iio b) b
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ =>
    tendsto_finsetSum _ fun r _ => tendsto_finsetSum _ fun s _ => ?_
  exact ((((hiota (bivectorIndex3 i).1 p).mul
    (hiota (bivectorIndex3 i).2 q)).mul (hiota (bivectorIndex3 j).2 r)).mul
      (hiota (bivectorIndex3 j).1 s)).mul (hRm p q r s)

theorem exists_uhlenbeckFrame_with_terminal_curvature_continuity
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    ∃ iota : MatrixComp M (Fin 3),
      (∀ x a k, iota 0 x a k = if a = k then 1 else 0) ∧
      (∀ x, ContinuousOn (fun t => iota t x) (Set.Icc 0 T)) ∧
      FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
        (uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
          (fun a x => basisAt x a)) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x a b,
        movingFrameGramInFrame (metricCompInFrame S (fun a x => basisAt x a))
          iota t x a b =
        movingFrameGramInFrame (metricCompInFrame S (fun a x => basisAt x a))
          iota 0 x a b) ∧
      (∀ b ∈ Set.Ioc 0 T, ∀ x, ContinuousWithinAt
        (fun t => uhlenbeckCurvatureOperatorMatrixAsMatrix
          (uhlenbeckPullbackRmInFrame iota
            (fun t x i j k l => tensor04StandardAt (S.base.rm04 t x)
              (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))) t x)
        (Set.Iio b) b) := by
  classical
  let gInv := solutionInverseMetricComponents S basisAt
  let frame := fun a x => basisAt x a
  obtain ⟨iota, hzero, hcont, hderiv⟩ := uhlenbeckIotaOfSolution hT S gInv
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_time hT S hS x v w)
    frame (fun a k => if a = k then 1 else 0)
  have hODE : FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      iota (uhlenbeckRupOfSolution S gInv frame) := by
    intro t x a k
    exact (hderiv (t : ℝ) ⟨t.2.1.le, t.2.2⟩ x a k).mono (fun _ hs => hs.1)
  have hcompat := ricciOneUpCompatible_of_inverseMetric S gInv frame
    (fun t x i j => solutionInverseMetricComponents_mul_metric S basisAt t x i j)
    (fun t x i j => solutionInverseMetricComponents_symm S basisAt t x i j)
  have hmetric : MetricCompRicciFlowInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (metricCompInFrame S frame) (ricciCompInFrame S frame) := by
    intro t x i j
    exact metricCompInFrame_timeDeriv S hS frame t x i j
  refine ⟨iota, hzero, hcont, hODE, ?_, ?_⟩
  · intro t ht x a b
    exact movingFrameGramInFrame_eq_initial_of_ricci_flow
      (metricCompInFrame S frame) (ricciCompInFrame S frame)
      iota (uhlenbeckRupOfSolution S gInv frame) hmetric hODE hcompat
      (fun _ hs => hs)
      (fun x a b => movingFrameGram_continuousOn_of_metricFamily
        hT S hS iota hcont frame a b) ht x a b
  · intro b hb x
    refine solution_uhlenbeckCurvatureMatrix_continuousWithinAt_terminal
      S hS hb.1 (fun _ hs => ⟨hs.1, hs.2.trans hb.2⟩)
      (fun _ hs => ⟨hs.1, hs.2.trans_le hb.2⟩) basisAt iota x ?_
    have hc : ContinuousWithinAt (fun t => iota t x) (Set.Iio b) b :=
      (hcont x b ⟨hb.1.le, hb.2⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Ioo_mem_nhdsLT hb.1)
          (fun _ hs => ⟨hs.1.le, hs.2.le.trans hb.2⟩))
    intro i j
    exact continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hc i) j

theorem solution_uhlenbeckCurvatureKernel_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (x : M)
    (hiota : ∀ i j, ContinuousWithinAt (fun t => iota t x i j) (Set.Iio b) b) :
    let A := fun t => uhlenbeckCurvatureOperatorMatrixAsMatrix
      (uhlenbeckPullbackRmInFrame iota
        (fun t x i j k l => tensor04StandardAt (S.base.rm04 t x)
          (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))) t x
    ∀ K : Submodule ℝ (Fin 3 → ℝ),
      (∀ᶠ t in 𝓝[<] b, LinearMap.ker (A t).mulVecLin = K) →
      Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker (A b).mulVecLin) →
      (∀ᶠ t in 𝓝[<] b, LinearMap.ker (A t).mulVecLin ≤
        LinearMap.ker (hamiltonIveyMatrixReaction (A t)).mulVecLin) →
      K = LinearMap.ker (A b).mulVecLin ∧
        LinearMap.ker (A b).mulVecLin ≤
          LinearMap.ker (hamiltonIveyMatrixReaction (A b)).mulVecLin ∧
        ((A b).rank = 0 ∨ (A b).rank = 1 ∨ (A b).rank = 3) := by
  dsimp only
  let A := fun t => uhlenbeckCurvatureOperatorMatrixAsMatrix
    (uhlenbeckPullbackRmInFrame iota
      (fun t x i j k l => tensor04StandardAt (S.base.rm04 t x)
        (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l))) t x
  intro K hfixed hdim hnull
  refine curvatureKernel_endpoint_of_rank_stable A b ?_ ?_ K hfixed hdim hnull
  · exact solution_uhlenbeckCurvatureMatrix_continuousWithinAt_terminal
      S hS hab hslab hreg basisAt iota x hiota
  · apply uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian
      (I := I) (M := M) (basis := basisAt x)
      (A := ⟨uhlenbeckPulledRm04At S basisAt iota b x,
        uhlenbeckPulledRm04At_mem_algebraicCurvatureTensorSubmodule S basisAt iota b x⟩)
    intro i j k l
    exact (uhlenbeckPulledRm04At_apply_basis S basisAt iota b x i j k l).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
