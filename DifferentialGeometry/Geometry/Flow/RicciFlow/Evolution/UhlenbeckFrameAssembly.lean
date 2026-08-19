import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckInverseMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped BigOperators Topology NNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem ricciAt_continuousOn_perPoint
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T) := by
  classical
  let K : Set Real := Set.Icc 0 T
  have hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => S.ricci t x) := by
    exact DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet.mono
      (I := I) (M := M) hS.ricciCont (by intro s hs; exact hs)
  have hcont : Continuous (fun p : K =>
      (S.ricci p.1 x) (fun i : Fin 2 => if i = 0 then v else w)) := by
    have heval :=
      DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet.eval_continuous
        (I := I) (M := M) (s := 2) (K := K) (A := fun t x => S.ricci t x) hA
        (P := K)
        (τ := fun p : K => p.1)
        (b := fun p : K => x)
        continuous_subtype_val (fun p : K => p.2) continuous_const
        (v := fun a : Fin 2 => fun p : K => if a = 0 then v else w)
        (by
          intro a
          fin_cases a
          · simpa using (continuous_const : Continuous (fun p : K =>
              (⟨x, v⟩ : TangentBundle I M)))
          · simpa using (continuous_const : Continuous (fun p : K =>
              (⟨x, w⟩ : TangentBundle I M))))
    simpa [K, vec2] using heval
  rw [continuousOn_iff_continuous_restrict]
  simpa [K, vec2] using hcont

noncomputable def solutionUhlenbeckIota
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    MatrixComp M (Fin 3) :=
  Classical.choose (uhlenbeckIota_isometry (I := I) (M := M) hT S hS
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_perPoint (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun t x i j => solutionInverseMetricComponents_mul_metric
      (I := I) (M := M) S basisAt t x i j)
    (fun t x i j => solutionInverseMetricComponents_symm
      (I := I) (M := M) S basisAt t x i j)
    (fun a k => if a = k then 1 else 0))

omit [SigmaCompactSpace M] in
theorem solutionUhlenbeckIota_spec
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    (∀ x : M, ∀ a k : Fin 3,
      solutionUhlenbeckIota hT S hS basisAt 0 x a k = if a = k then 1 else 0) ∧
    FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (solutionUhlenbeckIota hT S hS basisAt)
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) ∧
    (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (solutionUhlenbeckIota hT S hS basisAt) t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (solutionUhlenbeckIota hT S hS basisAt) 0 x a b) := by
  classical
  exact Classical.choose_spec (uhlenbeckIota_isometry (I := I) (M := M) hT S hS
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_perPoint (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun t x i j => solutionInverseMetricComponents_mul_metric
      (I := I) (M := M) S basisAt t x i j)
    (fun t x i j => solutionInverseMetricComponents_symm
      (I := I) (M := M) S basisAt t x i j)
    (fun a k => if a = k then 1 else 0))

omit [SigmaCompactSpace M] in
theorem solutionUhlenbeckIota_identity_initial_gram
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x : M) (a b : Fin 3) :
    movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
      (solutionUhlenbeckIota hT S hS basisAt) t x a b = if a = b then 1 else 0 := by
  classical
  have hspec := solutionUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt
  have hgram := hspec.2.2 t ht x a b
  rw [hgram]
  have hiota0 := hspec.1 x
  have horth : ∀ i j : Fin 3,
      (S.base.metric 0).inner x (basisAt x i) (basisAt x j) = if i = j then 1 else 0 := by
    intro i j
    simpa [delta3] using horth0 x i j
  simp [movingFrameGramInFrame, hiota0, horth, Finset.sum_ite_eq]

omit [SigmaCompactSpace M] in
theorem exists_uhlenbeckIota_of_finrank
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    ∃ iota : MatrixComp M (Fin 3),
      (∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0) ∧
      FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
        (uhlenbeckRupOfSolution (I := I) S
          (solutionInverseMetricComponents S
            (fun x => Classical.choose (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))))
          (fun a x => (Classical.choose (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))) a)) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
        movingFrameGramInFrame (metricCompInFrame (I := I) S
          (fun a x => (Classical.choose (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))) a))
          iota t x a b = if a = b then 1 else 0) := by
  classical
  let basisAt₀ : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x) :=
    fun x => Classical.choose (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  have horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt₀ x) := by
    intro x
    exact Classical.choose_spec (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  let iota : MatrixComp M (Fin 3) := solutionUhlenbeckIota hT S hS basisAt₀
  have hspec := solutionUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt₀
  refine ⟨iota, ?_, ?_, ?_⟩
  · intro x a k
    dsimp [iota]
    exact hspec.1 x a k
  · dsimp [iota]
    simpa [basisAt₀] using hspec.2.1
  · intro t ht x a b
    dsimp [iota]
    simpa [basisAt₀] using
      solutionUhlenbeckIota_identity_initial_gram (I := I) (M := M) hT S hS basisAt₀ horth0 t ht x a b

end DifferentialGeometry.PDE.RicciFlow
