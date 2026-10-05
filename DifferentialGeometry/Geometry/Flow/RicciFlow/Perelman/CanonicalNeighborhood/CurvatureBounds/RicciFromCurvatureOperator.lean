import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarNonnegativeOfRicciNonnegative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBallProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformRmNormSqProducer

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem metricAlgebraicCurvatureTensorAt_mem_cone_of_pointedFlowNonnegativeCurvatureOperator
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : ℝ)
    (h : PointedFlowNonnegativeCurvatureOperator (I := I) F t) (x : F.M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  rw [mem_algebraicCurvatureOperatorNonnegativeCone]
  intro n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt_coe,
    tensor04StandardAt_apply, SolutionFamily.rm04, metricRm04_apply] using h x n c v w

theorem ricciAt_nonnegative_of_pointedFlowNonnegativeCurvatureOperator
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : ℝ)
    (h : PointedFlowNonnegativeCurvatureOperator (I := I) F t) (x : F.M)
    (v : TangentSpace I x) :
    0 ≤ F.S.ricciAt t x (vec2 (I := I) v v) := by
  have hcone :=
    metricAlgebraicCurvatureTensorAt_mem_cone_of_pointedFlowNonnegativeCurvatureOperator F t h x
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt] using
    metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I) (M := F.M)
      (F.S.base.metric t) x hcone v

theorem pointedFlowScalarBounded_of_scalarUpperBound_and_pointedFlowNonnegativeCurvatureOperator
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (hdim : Module.finrank ℝ E = 3)
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {C : ℝ}
    (hscal : ∀ t ∈ D.carrier, ∀ x : F.M, F.S.scalar t x ≤ C)
    (hcone : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t) :
    PointedFlowScalarBounded (I := I) F C := by
  intro t ht x
  have hcone' :=
    metricAlgebraicCurvatureTensorAt_mem_cone_of_pointedFlowNonnegativeCurvatureOperator F t
      (hcone t ht) x
  refine ⟨?_, hscal t ht x⟩
  have hscalar := metricScalarAt_nonnegative_of_ricci_nonnegative (I := I) (M := F.M)
    (F.S.base.metric t) x hdim
    (fun v => ricciAt_nonnegative_of_pointedFlowNonnegativeCurvatureOperator F t (hcone t ht) x v)
  simpa only [SolutionOn.scalar, SolutionFamily.scalar] using hscalar

abbrev UniformNonnegativeCurvatureOperatorProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
      ∀ t ∈ (X.interval i).carrier,
        PointedFlowNonnegativeCurvatureOperator (X.term i) t

theorem ricciTensorBoundProducer_of_uniformScalarUpperBound_and_uniformNonnegativeCurvatureOperator
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {C epsStar : ℝ} (hC : 0 < C) (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
          (X.term i).S.scalar s x ≤ C)
    (hcone : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0,
          PointedFlowNonnegativeCurvatureOperator (X.term i) s) :
    RicciTensorBoundProducer.{u} kappa sigma Phi :=
  ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative hC hepsStar
    hscal fun eps heps hle X i s hs x =>
      metricAlgebraicCurvatureTensorAt_mem_cone_of_pointedFlowNonnegativeCurvatureOperator
        (X.term i) s (hcone eps heps hle X i s hs) x

theorem
    ricciTensorBoundProducer_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscal : UniformScalarBoundProducer.{u} kappa sigma Phi)
    (hcone : UniformNonnegativeCurvatureOperatorProducer.{u} kappa sigma Phi) :
    RicciTensorBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hb⟩ := hscal
  obtain ⟨epsStar', hepsStar', hcone'⟩ := hcone
  refine ⟨C / 2, by linarith, min epsStar epsStar', lt_min hepsStar hepsStar', ?_⟩
  intro eps heps hle X i s hs x v
  have hwin := (normalizedSequence_modelDepth_window X heps i).1 hs
  have hscal' : (X.term i).S.scalar s x ≤ C :=
    (hb eps heps (hle.trans (min_le_left epsStar epsStar')) X i s hwin x).2
  have hv : 0 ≤ ((X.term i).S.base.metric s).inner x v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact (((X.term i).S.base.metric s).pos x v hv0).le
  have hricNonneg : ∀ w : TangentSpace I3 x,
      0 ≤ (X.term i).S.ricciAt s x (vec2 w w) := fun w =>
    ricciAt_nonnegative_of_pointedFlowNonnegativeCurvatureOperator (X.term i) s
      (hcone' eps heps (hle.trans (min_le_right epsStar epsStar')) X i s hwin) x w
  have hup := metricRicciAt_le_scalar_mul_inner_of_ricci_nonnegative (I := I3)
    ((X.term i).S.base.metric s) x (by simp [ThreeSpace]) hricNonneg v
  have hdim : ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) = C := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    ring
  refine ⟨hricNonneg v, ?_⟩
  calc (X.term i).S.ricciAt s x (vec2 v v)
      ≤ (X.term i).S.scalar s x * ((X.term i).S.base.metric s).inner x v v := by
        simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.scalar,
          SolutionFamily.scalar] using hup
    _ ≤ C * ((X.term i).S.base.metric s).inner x v v :=
        mul_le_mul_of_nonneg_right hscal' hv
    _ = ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) *
          ((X.term i).S.base.metric s).inner x v v := by rw [hdim]

theorem
    terminalDerivativeBoundProducer_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscal : UniformScalarBoundProducer.{u} kappa sigma Phi)
    (hcone : UniformNonnegativeCurvatureOperatorProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundProducer
    (by
      obtain ⟨epsStar, hepsStar, C, hC, hb⟩ := hscal
      obtain ⟨epsStar', hepsStar', hcone'⟩ := hcone
      refine ⟨min epsStar epsStar', lt_min hepsStar hepsStar', fun eps heps hle X => ?_⟩
      exact uniformRmNormSqBound_of_uniformScalarBound_and_curvatureOperatorNonnegative X
        (hb eps heps (hle.trans (min_le_left epsStar epsStar')) X)
        (fun i t ht =>
          hcone' eps heps (hle.trans (min_le_right epsStar epsStar')) X i t ht))
    (ricciTensorBoundProducer_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
      hscal hcone)

theorem
    bounded_curvature_at_distance_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscal : UniformScalarBoundProducer.{u} kappa sigma Phi)
    (hcone : UniformNonnegativeCurvatureOperatorProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    (terminalDerivativeBoundProducer_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
      hscal hcone)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
