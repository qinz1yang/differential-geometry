import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBallProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

def UniformRmNormSqBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ K : ℝ, ∀ i : ℕ, PointedFlowRmNormSqBounded (X.term i) K

theorem exists_bound_of_uniformRmNormSqBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : UniformRmNormSqBound X) :
    ∀ i : ℕ, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C := by
  obtain ⟨K, hK⟩ := h
  exact fun i => ⟨K, hK i⟩

theorem uniformRmNormSqBound_of_eventually {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {K : ℝ}
    (h : ∀ᶠ i : ℕ in Filter.atTop, PointedFlowRmNormSqBounded (X.term i) K) :
    UniformRmNormSqBound X := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have hprefix : ∀ N : ℕ, ∃ C : ℝ,
      ∀ i : ℕ, i < N → PointedFlowRmNormSqBounded (X.term i) C := by
    intro N
    induction N with
    | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ N ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨C', hC'⟩ := X.source_bound N
      refine ⟨max C C', fun i hi t ht y => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact le_trans (hC i hlt t ht y) (le_max_left C C')
      · subst heq
        exact le_trans (hC' t ht y) (le_max_right C C')
  obtain ⟨C, hC⟩ := hprefix N
  refine ⟨max C K, fun i t ht y => ?_⟩
  by_cases hi : i < N
  · exact le_trans (hC i hi t ht y) (le_max_left C K)
  · exact le_trans (hN i (le_of_not_gt hi) t ht y) (le_max_right C K)

theorem pointedFlowRmNormSqBounded_mono
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {C C' : ℝ} (h : C ≤ C') :
    PointedFlowRmNormSqBounded (I := I) F C → PointedFlowRmNormSqBounded (I := I) F C' :=
  fun hb t ht x => le_trans (hb t ht x) h

theorem uniformRmNormSqBound_of_uniformScalarBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C Cn : ℝ} (hCn : 0 ≤ Cn)
    (hC : ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hrm : ∀ i : ℕ, PointedFlowRmNormLeScalar (X.term i) Cn) :
    UniformRmNormSqBound X :=
  ⟨(Cn * C) ^ 2, fun i =>
    pointedFlowRmNormSqBounded_of_scalarBounded (X.term i) hCn (hC i) (hrm i)⟩

theorem pointedFlowRmNormLeScalar_of_nonnegativeCurvatureOperator
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (h : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t) :
    PointedFlowRmNormLeScalar (I := I) F ((Module.finrank ℝ E : ℝ) ^ 2) := by
  intro t ht x
  have hoperator : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have hquad := h t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using hquad
  have hbound := KappaSolutions.sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hoperator
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using hbound

theorem uniformRmNormSqBound_of_uniformScalarBound_and_curvatureOperatorNonnegative
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C : ℝ}
    (hscal : ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hcone : ∀ i : ℕ, ∀ t ∈ (X.interval i).carrier,
      PointedFlowNonnegativeCurvatureOperator (X.term i) t) :
    UniformRmNormSqBound X :=
  uniformRmNormSqBound_of_uniformScalarBound X (sq_nonneg _) hscal
    (fun i => pointedFlowRmNormLeScalar_of_nonnegativeCurvatureOperator (X.term i) (hcone i))

theorem terminalParabolicRmBallBound_of_uniformRmNormSqBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {K : ℝ} (h : ∀ i : ℕ, PointedFlowRmNormSqBounded (X.term i) K)
    (start ρ : ℝ) (hcarrier : ∀ i : ℕ, Set.Icc start 0 ⊆ (X.interval i).carrier) :
    TerminalParabolicRmBallBound X start ρ := by
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right K 1), fun i t ht y _ => ?_⟩
  rw [← rmNormSq_eq_curvDerivNormSq X i t y]
  exact le_trans (h i t (hcarrier i ht) y) (le_max_left K 1)

theorem terminalParabolicCurvatureBound_of_uniformRmNormSqBound_and_ballNesting
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : UniformRmNormSqBound X) (start : ℝ)
    (hcarrier : ∀ i : ℕ, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (hnest : ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X start rho ρ) :
    TerminalParabolicCurvatureBound X start := by
  obtain ⟨K, hK⟩ := h
  exact terminalParabolicCurvatureBound_of_scale_windows X start
    (fun ρ _ => terminalParabolicRmBallBound_of_uniformRmNormSqBound X hK start ρ hcarrier)
    hnest

theorem parabolicCurvatureBoundsAtBase_of_uniformRmNormSqBound_and_ballNesting
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (heps : 0 < eps) (h : UniformRmNormSqBound X)
    (hnest : ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X (-(modelDepth eps)) rho ρ) :
    ParabolicCurvatureBoundsAtBase X :=
  parabolicCurvatureBoundsAtBase_of_terminalParabolicCurvatureControl X heps
    (terminalParabolicCurvatureControl_of_bound X heps
      (terminalParabolicCurvatureBound_of_uniformRmNormSqBound_and_ballNesting X h
        (-(modelDepth eps)) (fun i => (normalizedSequence_modelDepth_window X heps i).1)
        hnest))

theorem terminalDerivativeBounds_of_uniformRmNormSqBound_and_ballNesting
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (heps : 0 < eps) (h : UniformRmNormSqBound X)
    (hnest : ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X (-(modelDepth eps)) rho ρ) :
    TerminalDerivativeBounds X :=
  terminalDerivativeBounds_of_parabolicCurvatureBounds X
    (parabolicCurvatureBoundsAtBase_of_uniformRmNormSqBound_and_ballNesting X heps h hnest)

abbrev UniformRmNormSqBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, UniformRmNormSqBound X

theorem terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, e₂, he₂, hric₂⟩ := hric
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  have hnest := terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK
    (hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X)
  exact terminalDerivativeBounds_of_uniformRmNormSqBound_and_ballNesting X hp
    (hrm₁ eps hp (hle.trans (min_le_left e₁ e₂)) X) hnest

theorem bounded_curvature_at_distance_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    (terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundProducer
      hrm hric)

theorem exists_pointwise_bound_not_uniform :
    ∃ P : ℕ → ℝ → Prop, (∀ i C C', C ≤ C' → P i C → P i C') ∧
      (∀ i : ℕ, ∃ C : ℝ, P i C) ∧ ¬ ∃ K : ℝ, ∀ i : ℕ, P i K := by
  refine ⟨fun i C => (i : ℝ) ≤ C, fun i C C' hle hC => le_trans hC hle,
    fun i => ⟨(i : ℝ), le_rfl⟩, ?_⟩
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt K
  exact not_le.mpr hn (hK n)

theorem standardRmNormSq3_roundSphere_unit :
    standardRmNormSq3 (standardRmDiag3 2 2 2) = 12 := by
  rw [standardRmNormSq3_diag]
  norm_num [rmSecNormSq3, sec12Ric3, sec13Ric3, sec23Ric3]

theorem standardRmNormSq3_roundSphere_le_twelve (l : ℝ)
    (h0 : 0 ≤ l) (h2 : l ≤ 2) :
    standardRmNormSq3 (standardRmDiag3 l l l) ≤ 12 := by
  rw [standardRmNormSq3_diag]
  simp only [rmSecNormSq3, sec12Ric3, sec13Ric3, sec23Ric3]
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h2)]

theorem standardRmNormSq3_roundSphere_scalar_one_le_twelve :
    standardRmNormSq3 (standardRmDiag3 (1 / 3) (1 / 3) (1 / 3)) ≤ 12 := by
  rw [standardRmNormSq3_roundSphere_scalar_one]
  norm_num

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
