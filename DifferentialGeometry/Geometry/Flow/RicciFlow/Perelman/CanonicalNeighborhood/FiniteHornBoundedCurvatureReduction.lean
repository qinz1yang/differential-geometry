import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RicciTensorBoundOfCurvatureOperatorProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RicciTensorBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformScalarBoundProducer

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem terminalWindow_subset_carrier {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    Set.Icc (-(modelDepth eps)) 0 ⊆ (X.interval i).carrier := by
  intro s hs
  rw [X.carrier_eq i]
  exact ⟨by linarith [X.depth_buffer i, X.depth_pos i, hs.1], hs.2⟩

private theorem terminalWindowRmNormSqLe_of_scalarUpperBound_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C : ℝ}
    (hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C) {i : ℕ} (hQ : 1 ≤ X.scale i)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) 0) (y : (X.term i).M) :
    (X.term i).rmNormSq s y ≤
      (2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2 := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hquarter : 4 * (max C 1 / 4) = max C 1 := by ring
  have hP : 0 < max C 1 / 4 := by positivity
  have hub : (X.term i).S.scalar s y ≤ 4 * (max C 1 / 4) := by
    rw [hquarter]
    exact le_trans (hscal i s hs y) (le_max_left C 1)
  have hbridge : RmNormBoundOn (I := I3) (X.term i).S (2 * Real.sqrt 3) :=
    fun t' w' basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (I := I3) (X.term i).S t' w'
        basis horth ha
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3) (by positivity) hbridge
    (hPhi.rescale (X.scale_pos i)) (X.pinching i) hdim (terminalWindow_subset_carrier X i hs)
    y hP hub
  have hfour := rescalePinchingFunction_le_phi_one_mul_max hPhi hQ (C := C)
    (u := 4 * (max C 1 / 4)) (by rw [hquarter])
  have hzero := rescalePinchingFunction_le_phi_one_mul_max hPhi hQ (C := C) (u := 0)
    (show (0 : ℝ) ≤ max C 1 from le_trans zero_le_one (le_max_right C 1))
  have hle : 2 * (2 * Real.sqrt 3) *
      (max C 1 / 4 + rescalePinchingFunction (X.scale i) Phi (4 * (max C 1 / 4)) +
        rescalePinchingFunction (X.scale i) Phi 0) ≤
      2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1)) := by
    have hsqrt3 : (0 : ℝ) ≤ 2 * Real.sqrt 3 := by positivity
    have hK : (0 : ℝ) ≤ Phi 1 * max C 1 :=
      le_of_lt (mul_pos (hPhi.pos 1) (lt_of_lt_of_le zero_lt_one (le_max_right C 1)))
    nlinarith [hfour, hzero, hsqrt3, hK]
  have hsqrt : Real.sqrt (FlowMetricBall.rmNormSq (I := I3) (X.term i).S s y) ≤
      2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1)) :=
    le_trans hrm hle
  have hnonneg : 0 ≤ FlowMetricBall.rmNormSq (I := I3) (X.term i).S s y :=
    Tensor0SBundle.normSq0S_nonneg (I := I3) ((X.term i).S.base.metric s) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric s) y)
  have hsq : FlowMetricBall.rmNormSq (I := I3) (X.term i).S s y ≤
      (2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2 := by
    rw [← Real.sq_sqrt hnonneg]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  calc (X.term i).rmNormSq s y
      = curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric s) y :=
        rmNormSq_eq_curvDerivNormSq X i s y
    _ = FlowMetricBall.rmNormSq (I := I3) (X.term i).S s y := rfl
    _ ≤ (2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2 := hsq

private theorem exists_terminalWindowRmNormSqBound_prefix
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (N : ℕ) :
    ∃ K : ℝ, ∀ i : ℕ, i < N → ∀ s ∈ Set.Icc (-(modelDepth eps)) 0,
      ∀ x : (X.term i).M, (X.term i).rmNormSq s x ≤ K := by
  induction N with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨K', hK'⟩ := X.source_bound N
    refine ⟨max K K', fun i hi s hs x => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (hK i hlt s hs x) (le_max_left K K')
    · subst heq
      exact le_trans (hK' s (terminalWindow_subset_carrier X _ hs) x) (le_max_right K K')

theorem terminalWindowRmNormSqBound_of_scalarUpperBound_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C : ℝ}
    (hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0,
      ∀ x : (X.term i).M, (X.term i).rmNormSq s x ≤ K := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (X.scale_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ)))
  obtain ⟨K₀, hK₀⟩ := exists_terminalWindowRmNormSqBound_prefix X N
  refine ⟨max K₀ ((2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2),
    le_trans (sq_nonneg _) (le_max_right K₀ _), fun i s hs x => ?_⟩
  by_cases hi : i < N
  · exact le_trans (hK₀ i hi s hs x) (le_max_left K₀ _)
  · exact le_trans
      (terminalWindowRmNormSqLe_of_scalarUpperBound_and_pinching hPhi X hscal
        (hN i (le_of_not_gt hi)) hs x) (le_max_right K₀ _)

theorem terminalWindowRmNormSqBound_of_scalarUpperBound_and_curvatureOperatorCone
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {C : ℝ}
    (hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C)
    (hcone : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      metricAlgebraicCurvatureTensorAt (I := I3) (M := (X.term i).M)
          ((X.term i).S.base.metric s) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := (X.term i).M)) :
    ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).rmNormSq s x ≤ ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * C) ^ 2 := by
  intro i s hs x
  have hbound := KappaSolutions.sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I3)
    ((X.term i).S.base.metric s) x (hcone i s hs x)
  have hsqrt : Real.sqrt ((X.term i).rmNormSq s x) ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (X.term i).S.scalar s x := by
    simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
      metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using hbound
  have hle : Real.sqrt ((X.term i).rmNormSq s x) ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * C :=
    le_trans hsqrt (mul_le_mul_of_nonneg_left (hscal i s hs x) (by positivity))
  have hnn : 0 ≤ (X.term i).rmNormSq s x := by
    have h : (X.term i).rmNormSq s x =
        FlowMetricBall.rmNormSq (I := I3) (X.term i).S s x := by
      calc (X.term i).rmNormSq s x
          = curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric s) x :=
            rmNormSq_eq_curvDerivNormSq X i s x
        _ = FlowMetricBall.rmNormSq (I := I3) (X.term i).S s x := rfl
    rw [h]
    exact Tensor0SBundle.normSq0S_nonneg (I := I3) ((X.term i).S.base.metric s) x 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric s) x)
  calc (X.term i).rmNormSq s x = (Real.sqrt ((X.term i).rmNormSq s x)) ^ 2 :=
        (Real.sq_sqrt hnn).symm
    _ ≤ ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * C) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

theorem terminalParabolicRmBallBound_of_terminalWindowRmNormSqBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).rmNormSq s x ≤ K) (ρ : ℝ) :
    TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ := by
  refine ⟨K + 1, by linarith, fun i t ht y _ => ?_⟩
  rw [← rmNormSq_eq_curvDerivNormSq X i t y]
  exact le_trans (h i t ht y) (by linarith)

theorem bounded_curvature_at_distance_of_terminalWindowScalarUpperBoundShell_and_curvatureOperatorConeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscl : TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi)
    (hcone : TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e₁, he₁, hs⟩ := hscl
  obtain ⟨e₂, he₂, hc⟩ := hcone
  refine bounded_curvature_at_distance_of_terminalParabolicCurvatureBound
    ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  obtain ⟨C, hC, hCbound⟩ := hs eps hp (le_trans hle (min_le_left e₁ e₂)) X
  have hconeX := hc eps hp (le_trans hle (min_le_right e₁ e₂)) X
  have hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C := fun i s hs' x => hCbound i s hs' x
  have hrm : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ :=
    fun ρ _ => terminalParabolicRmBallBound_of_terminalWindowRmNormSqBound X (sq_nonneg _)
      (terminalWindowRmNormSqBound_of_scalarUpperBound_and_curvatureOperatorCone X hscal hconeX)
      ρ
  obtain ⟨K', hK', hric'⟩ := terminalRicciTensorBound_of_scalarUpperBound_and_ricciNonnegative
    X hC hscal fun i s hs' x v =>
      metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I3)
        ((X.term i).S.base.metric s) x (hconeX i s hs' x) v
  exact terminalParabolicCurvatureBound_of_scale_windows X (-(modelDepth eps)) hrm
    (terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK' hric')

theorem bounded_curvature_at_distance_of_terminalWindowScalarUpperBoundShell_and_ricciNonnegativeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi)
    (hric : TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e₁, he₁, hs⟩ := hscl
  obtain ⟨e₂, he₂, hr⟩ := hric
  refine bounded_curvature_at_distance_of_terminalParabolicCurvatureBound
    ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  obtain ⟨C, hC, hCbound⟩ := hs eps hp (le_trans hle (min_le_left e₁ e₂)) X
  have hricX := hr eps hp (le_trans hle (min_le_right e₁ e₂)) X
  have hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C := fun i s hs' x => hCbound i s hs' x
  obtain ⟨K, hK, hb⟩ :=
    terminalWindowRmNormSqBound_of_scalarUpperBound_and_pinching hPhi X hscal
  have hrm : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ :=
    fun ρ _ => terminalParabolicRmBallBound_of_terminalWindowRmNormSqBound X hK hb ρ
  obtain ⟨K', hK', hric'⟩ := terminalRicciTensorBound_of_scalarUpperBound_and_ricciNonnegative
    X hC hscal fun i s hs' x v => hricX i s hs' x v
  exact terminalParabolicCurvatureBound_of_scale_windows X (-(modelDepth eps)) hrm
    (terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK' hric')

theorem terminalWindowShells_of_uniformScalarUpperBoundShell_and_curvatureOperatorConeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscl : UniformScalarUpperBoundShell.{u} kappa sigma Phi)
    (hcone : TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi ∧
      TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi :=
  ⟨terminalWindowScalarUpperBoundShell_of_uniformScalarUpperBoundShell hscl,
    terminalWindowRicciNonnegativeShell_of_curvatureOperatorConeShell hcone⟩

theorem terminalWindowCurvatureOperatorConeShell_of_uniformNonnegativeCurvatureOperatorProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformNonnegativeCurvatureOperatorProducer.{u} kappa sigma Phi) :
    TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hcone⟩ := h
  refine ⟨e, he, fun eps hp hle X i s hs x => ?_⟩
  exact metricAlgebraicCurvatureTensorAt_mem_cone_of_pointedFlowNonnegativeCurvatureOperator
    (X.term i) s (hcone eps hp hle X i s ((terminalWindow_subset_carrier X i hs))) x

theorem terminalWindowShells_of_uniformScalarBound_and_nonnegativeCurvatureOperatorProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscl : UniformScalarBoundProducer.{u} kappa sigma Phi)
    (hcone : UniformNonnegativeCurvatureOperatorProducer.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi ∧
      TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi :=
  ⟨terminalWindowScalarUpperBoundShell_of_uniformScalarBoundProducer hscl,
    terminalWindowCurvatureOperatorConeShell_of_uniformNonnegativeCurvatureOperatorProducer hcone⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
