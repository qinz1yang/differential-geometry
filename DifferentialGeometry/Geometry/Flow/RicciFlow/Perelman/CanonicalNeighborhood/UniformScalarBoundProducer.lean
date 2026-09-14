import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalPropagationOfHarnackCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformRmNormSqProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

abbrev UniformScalarUpperBoundShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∃ C : ℝ, 0 < C ∧
      ∀ i : ℕ, ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
        (X.term i).S.scalar t x ≤ C

abbrev UniformTerminalScalarUpperBoundShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∃ C : ℝ, 0 < C ∧
      ∀ i : ℕ, ∀ x : (X.term i).M, (X.term i).S.scalar 0 x ≤ C

theorem uniformScalarUpperBoundShell_of_uniformScalarBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarBoundProducer.{u} kappa sigma Phi) :
    UniformScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal⟩ := h
  exact ⟨epsStar, hepsStar, fun eps heps hle X =>
    ⟨C, hC, fun i t ht x => (hscal eps heps hle X i t ht x).2⟩⟩

theorem uniformScalarUpperBoundShell_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    UniformScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal, _⟩ := h
  exact ⟨epsStar, hepsStar, fun eps heps hle X =>
    ⟨C, hC, fun i t ht x => (hscal eps heps hle X i t ht x).2⟩⟩

theorem uniformTerminalScalarUpperBoundShell_of_uniformScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarUpperBoundShell.{u} kappa sigma Phi) :
    UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨C, hC, hbd⟩ := hb eps heps hle X
  exact ⟨C, hC, fun i x => hbd i 0 (by rw [X.carrier_eq i]; exact
    ⟨by linarith [X.depth_pos i], le_rfl⟩) x⟩

theorem boundedAtDistance_of_terminalScalarUpperBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {C : ℝ} (h : ∀ i : ℕ, ∀ x : (X.term i).M, (X.term i).S.scalar 0 x ≤ C) :
    BoundedAtDistance X :=
  fun _ _ => ⟨C, fun i y _ => h i y⟩

theorem boundedAtDistanceShell_of_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨C, _hC, hbd⟩ := hb eps heps hle X
  exact boundedAtDistance_of_terminalScalarUpperBound X hbd

theorem boundedAtDistanceShell_of_uniformScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarUpperBoundShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_uniformTerminalScalarUpperBoundShell
    (uniformTerminalScalarUpperBoundShell_of_uniformScalarUpperBoundShell h)

theorem exists_curvatureBoundedWithin_of_uniformTerminalScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformTerminalScalarUpperBoundShell.{u} kappa sigma Phi) :
    ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, 1, hepsStar, one_pos, fun eps heps hle X => ?_⟩
  obtain ⟨C, _hC, hbd⟩ := hb eps heps hle X
  exact ⟨C, fun i y _ => hbd i y⟩

theorem pointedFlowRmNormSqBounded_of_scalarUpperBounded_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) {C : ℝ}
    (hscal : ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
      (X.term i).S.scalar t x ≤ C) (hQ : 1 ≤ X.scale i) :
    PointedFlowRmNormSqBounded (X.term i)
      ((2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2) := by
  intro t ht y
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hquarter : 4 * (max C 1 / 4) = max C 1 := by ring
  have hP : 0 < max C 1 / 4 := by positivity
  have hub : (X.term i).S.scalar t y ≤ 4 * (max C 1 / 4) := by
    rw [hquarter]
    exact le_trans (hscal t ht y) (le_max_left C 1)
  have hbridge : RmNormBoundOn (I := I3) (X.term i).S (2 * Real.sqrt 3) :=
    fun t' w' basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (I := I3) (X.term i).S t' w'
        basis horth ha
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3) (by positivity) hbridge
    (hPhi.rescale (X.scale_pos i)) (X.pinching i) hdim ht y hP hub
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
  have hsqrt : Real.sqrt (FlowMetricBall.rmNormSq (I := I3) (X.term i).S t y) ≤
      2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1)) :=
    le_trans hrm hle
  have hnonneg : 0 ≤ FlowMetricBall.rmNormSq (I := I3) (X.term i).S t y :=
    Tensor0SBundle.normSq0S_nonneg (I := I3) ((X.term i).S.base.metric t) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric t) y)
  have hsq : FlowMetricBall.rmNormSq (I := I3) (X.term i).S t y ≤
      (2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2 := by
    rw [← Real.sq_sqrt hnonneg]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  calc (X.term i).rmNormSq t y
      = curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y :=
        rmNormSq_eq_curvDerivNormSq X i t y
    _ = FlowMetricBall.rmNormSq (I := I3) (X.term i).S t y := rfl
    _ ≤ (2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2 := hsq

theorem uniformRmNormSqBound_of_uniformScalarUpperBound_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C : ℝ}
    (hscal : ∀ i : ℕ, ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
      (X.term i).S.scalar t x ≤ C) :
    UniformRmNormSqBound X :=
  uniformRmNormSqBound_of_eventually X
    ((X.scale_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ))).mono fun i hi =>
      pointedFlowRmNormSqBounded_of_scalarUpperBounded_and_pinching hPhi X i (hscal i) hi)

theorem uniformRmNormSqBoundProducer_of_uniformScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (h : UniformScalarUpperBoundShell.{u} kappa sigma Phi) :
    UniformRmNormSqBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨C, _hC, hbd⟩ := hb eps heps hle X
  exact uniformRmNormSqBound_of_uniformScalarUpperBound_and_pinching hPhi X hbd

theorem uniformScalarUpperBoundShell_of_uniformRmNormSqBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformRmNormSqBoundProducer.{u} kappa sigma Phi) :
    UniformScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨K, hK⟩ := hb eps heps hle X
  refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max K 0) + 1,
    by positivity, ?_⟩
  intro i t ht x
  have hrm : normSq0S (I := I3) ((X.term i).S.base.metric t) x 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric t) x) ≤ max K 0 :=
    le_trans (hK i t ht x) (le_max_left K 0)
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I3)
    ((X.term i).S.base.metric t) x
  have hdimT : Module.finrank ℝ (TangentSpace I3 x) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdimT] at hscal
  have hkey : (X.term i).S.scalar t x ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max K 0) :=
    le_trans (le_abs_self _) (le_trans hscal
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))
  linarith

theorem uniformScalarUpperBoundShell_iff_uniformRmNormSqBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) :
    UniformScalarUpperBoundShell.{u} kappa sigma Phi ↔
      UniformRmNormSqBoundProducer.{u} kappa sigma Phi :=
  ⟨uniformRmNormSqBoundProducer_of_uniformScalarUpperBoundShell hPhi,
    uniformScalarUpperBoundShell_of_uniformRmNormSqBoundProducer⟩

theorem exists_scalarUpperBound_of_source_bound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
      (X.term i).S.scalar t x ≤ C := by
  obtain ⟨C', hC'⟩ := X.source_bound i
  refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C' 0) + 1,
    by positivity, ?_⟩
  intro t ht x
  have hrm : normSq0S (I := I3) ((X.term i).S.base.metric t) x 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric t) x) ≤ max C' 0 :=
    le_trans (hC' t ht x) (le_max_left C' 0)
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I3)
    ((X.term i).S.base.metric t) x
  have hdimT : Module.finrank ℝ (TangentSpace I3 x) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdimT] at hscal
  have hkey : (X.term i).S.scalar t x ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C' 0) :=
    le_trans (le_abs_self _) (le_trans hscal
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))
  linarith

theorem exists_curvatureBoundedWithin_of_harnackCollapseBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r := by
  obtain ⟨epsStar, r, hepsStar, hr, hbound⟩ :=
    exists_pos_curvatureBoundedWithin_of_modelScale (kappa := kappa)
      (modelCurvatureBoundNearBase_of_harnackCollapseBound (I := I3) (by simp [ThreeSpace]) h)
  exact ⟨epsStar, r, hepsStar, hr, fun eps heps hle X =>
    hbound eps heps hle sigma hsigma Phi hPhi X⟩

theorem boundedAtDistanceShell_of_harnackCollapseBound_and_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (hesc : NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_noSubsequenceCurvatureEscapeShell
    (exists_curvatureBoundedWithin_of_harnackCollapseBound hsigma hPhi h) hesc

theorem noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_harnackCollapseBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi ↔
      BoundedAtDistanceShell.{u} kappa sigma Phi :=
  noSubsequenceCurvatureEscapeShell_iff_boundedAtDistanceShell_of_smallScale
    (exists_curvatureBoundedWithin_of_harnackCollapseBound hsigma hPhi h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
