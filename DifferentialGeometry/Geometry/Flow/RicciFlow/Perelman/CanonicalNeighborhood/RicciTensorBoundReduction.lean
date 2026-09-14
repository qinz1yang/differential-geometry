import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalDerivativeBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalShiDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformScalarBoundProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

abbrev TerminalWindowScalarUpperBoundShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∃ C : ℝ, 0 < C ∧
      ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
        (X.term i).S.scalar s x ≤ C

abbrev TerminalWindowRicciNonnegativeShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
      ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v)

abbrev TerminalWindowCurvatureOperatorConeShell.{v} (kappa sigma : ℝ)
    (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
      ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
        metricAlgebraicCurvatureTensorAt (I := I3) (M := (X.term i).M)
          ((X.term i).S.base.metric s) x ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := (X.term i).M)

def TerminalRicciTensorBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0,
    ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
      0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
        (X.term i).S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
            ((X.term i).S.base.metric s).inner x v v

abbrev TerminalRicciTensorBoundShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, TerminalRicciTensorBound X

theorem terminalWindowScalarUpperBoundShell_of_uniformScalarUpperBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarUpperBoundShell.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ?_⟩
  obtain ⟨C, hC, hbd⟩ := hb eps heps hle X
  exact ⟨C, hC, fun i s hs x =>
    hbd i s ((normalizedSequence_modelDepth_window X heps i).1 hs) x⟩

theorem terminalWindowScalarUpperBoundShell_of_uniformScalarBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarBoundProducer.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X => ⟨C, hC, fun i s hs x => ?_⟩⟩
  exact (hscal eps heps hle X i s ((normalizedSequence_modelDepth_window X heps i).1 hs) x).2

theorem terminalWindowScalarUpperBoundShell_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi :=
  terminalWindowScalarUpperBoundShell_of_uniformScalarBoundProducer
    (uniformScalarBoundProducer_of_uniformScalarRicciNonnegativeProducer h)

theorem terminalWindowRicciNonnegativeShell_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal, hric⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X i s hs x v => ?_⟩
  exact hric eps heps hle X i s ((normalizedSequence_modelDepth_window X heps i).1 hs) x v

theorem terminalWindowRicciNonnegativeShell_of_curvatureOperatorConeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi) :
    TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hcone⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle X i s hs x v => ?_⟩
  exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I3)
    ((X.term i).S.base.metric s) x (hcone eps heps hle X i s hs x) v

theorem terminalWindowShells_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi ∧
      TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi :=
  ⟨terminalWindowScalarUpperBoundShell_of_uniformScalarRicciNonnegativeProducer h,
    terminalWindowRicciNonnegativeShell_of_uniformScalarRicciNonnegativeProducer h⟩

theorem terminalRicciTensorBound_of_scalarUpperBound_and_ricciNonnegative
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {C : ℝ} (hC : 0 < C)
    (hscal : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      (X.term i).S.scalar s x ≤ C)
    (hric : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x, 0 ≤ (X.term i).S.ricciAt s x (vec2 v v)) :
    TerminalRicciTensorBound X := by
  have hdim : ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) = C := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    ring
  refine ⟨C / 2, by linarith, fun i s hs x v => ⟨hric i s hs x v, ?_⟩⟩
  have hv : 0 ≤ ((X.term i).S.base.metric s).inner x v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact (((X.term i).S.base.metric s).pos x v hv0).le
  have hup := metricRicciAt_le_scalar_mul_inner_of_ricci_nonnegative (I := I3)
    ((X.term i).S.base.metric s) x (by simp [ThreeSpace])
    (fun w => hric i s hs x w) v
  calc (X.term i).S.ricciAt s x (vec2 v v)
      ≤ metricScalarAt (I := I3) ((X.term i).S.base.metric s) x *
          ((X.term i).S.base.metric s).inner x v v := hup
    _ ≤ C * ((X.term i).S.base.metric s).inner x v v :=
        mul_le_mul_of_nonneg_right (hscal i s hs x) hv
    _ = ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) *
          ((X.term i).S.base.metric s).inner x v v := by rw [hdim]

theorem terminalRicciTensorBoundShell_of_scalarUpperBoundShell_and_ricciNonnegativeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hscl : TerminalWindowScalarUpperBoundShell.{u} kappa sigma Phi)
    (hric : TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi) :
    TerminalRicciTensorBoundShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, hs⟩ := hscl
  obtain ⟨e₂, he₂, hr⟩ := hric
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  obtain ⟨C, hC, hb⟩ := hs eps hp (le_trans hle (min_le_left e₁ e₂)) X
  exact terminalRicciTensorBound_of_scalarUpperBound_and_ricciNonnegative X hC
    (fun i s hs' x => hb i s hs' x)
    (fun i s hs' x v => hr eps hp (le_trans hle (min_le_right e₁ e₂)) X i s hs' x v)

theorem terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : UniformRmNormSqBoundProducer.{u} kappa sigma Phi)
    (hric : TerminalRicciTensorBoundShell.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  obtain ⟨e₂, he₂, hric₂⟩ := hric
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  obtain ⟨K, hK, hb⟩ := hric₂ eps hp (le_trans hle (min_le_right e₁ e₂)) X
  exact terminalDerivativeBounds_of_uniformRmNormSqBound_and_ballNesting X hp
    (hrm₁ eps hp (le_trans hle (min_le_left e₁ e₂)) X)
    (terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK hb)

theorem terminalDerivativeBoundProducer_of_uniformScalarUpperBoundShell_and_ricciNonnegativeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : UniformScalarUpperBoundShell.{u} kappa sigma Phi)
    (hric : TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundShell
    (uniformRmNormSqBoundProducer_of_uniformScalarUpperBoundShell hPhi hscl)
    (terminalRicciTensorBoundShell_of_scalarUpperBoundShell_and_ricciNonnegativeShell
      (terminalWindowScalarUpperBoundShell_of_uniformScalarUpperBoundShell hscl) hric)

theorem terminalDerivativeBoundProducer_of_uniformScalarUpperBoundShell_and_coneShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : UniformScalarUpperBoundShell.{u} kappa sigma Phi)
    (hcone : TerminalWindowCurvatureOperatorConeShell.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_uniformScalarUpperBoundShell_and_ricciNonnegativeShell
    hPhi hscl (terminalWindowRicciNonnegativeShell_of_curvatureOperatorConeShell hcone)

theorem terminalDerivativeBoundProducer_of_uniformScalarBoundProducer_and_ricciNonnegativeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : UniformScalarBoundProducer.{u} kappa sigma Phi)
    (hric : TerminalWindowRicciNonnegativeShell.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundShell
    (uniformRmNormSqBoundProducer_of_uniformScalarBoundProducer hPhi hscl)
    (terminalRicciTensorBoundShell_of_scalarUpperBoundShell_and_ricciNonnegativeShell
      (terminalWindowScalarUpperBoundShell_of_uniformScalarBoundProducer hscl) hric)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.Geometry.Curvature

open scoped BigOperators

theorem ricciEigenScalar3_le_half_scalar_add_of_sectional_lower_bounds {l1 l2 l3 K : ℝ}
    (h12 : -K ≤ sec12Ric3 l1 l2 l3) (h13 : -K ≤ sec13Ric3 l1 l2 l3)
    (h23 : -K ≤ sec23Ric3 l1 l2 l3) :
    l1 ≤ ricciEigenScalar3 l1 l2 l3 / 2 + K ∧
      l2 ≤ ricciEigenScalar3 l1 l2 l3 / 2 + K ∧
      l3 ≤ ricciEigenScalar3 l1 l2 l3 / 2 + K := by
  have h1 : l1 = sec12Ric3 l1 l2 l3 + sec13Ric3 l1 l2 l3 := by
    unfold sec12Ric3 sec13Ric3
    ring
  have h2 : l2 = sec12Ric3 l1 l2 l3 + sec23Ric3 l1 l2 l3 := by
    unfold sec12Ric3 sec23Ric3
    ring
  have h3 : l3 = sec13Ric3 l1 l2 l3 + sec23Ric3 l1 l2 l3 := by
    unfold sec13Ric3 sec23Ric3
    ring
  have hscal : ricciEigenScalar3 l1 l2 l3 / 2 =
      sec12Ric3 l1 l2 l3 + sec13Ric3 l1 l2 l3 + sec23Ric3 l1 l2 l3 := by
    unfold ricciEigenScalar3 sec12Ric3 sec13Ric3 sec23Ric3
    ring
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem pairwise_nonneg_iff_two_smallest_sum_nonneg {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (0 ≤ a + b ∧ 0 ≤ a + c ∧ 0 ≤ b + c) ↔ 0 ≤ a + b := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, by linarith, by linarith⟩

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

namespace KLim

theorem ricciAt_nonnegative {kappa : ℝ} (hK : KLim (I := I) kappa F) :
    ∀ t ∈ D.carrier, ∀ x : F.M, ∀ v : TangentSpace I x,
      0 ≤ F.S.ricciAt t x (vec2 v v) := by
  intro t ht x v
  have hR : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v' w'
    have h := hK.nonnegativeCurvatureOperator t ht x n c v' w'
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I)
    (F.S.base.metric t) x hR v

end KLim

theorem pointedFlowSeq_ricciAt_nonnegative_of_kLim
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) {kappa : ℝ}
    (hK : ∀ i, KLim (I := I) kappa (X.term i)) :
    ∀ i, ∀ t ∈ X.D.carrier, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
      0 ≤ (X.term i).S.ricciAt t x (vec2 v v) :=
  fun i => KLim.ricciAt_nonnegative (X.term i) (hK i)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
