import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalDerivativeBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

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

private theorem rescalePinchingFunction_le_phi_one_mul_max_of_one_le_le
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) {Q C u : ℝ}
    (hQ : 1 ≤ Q) (hu1 : 1 ≤ u) (hu : u ≤ max C 1) :
    rescalePinchingFunction Q Phi u ≤ Phi 1 * max C 1 := by
  have ht1 : (1 : ℝ) ≤ Q * u := one_le_mul_of_one_le_of_one_le hQ hu1
  have hquot := hPhi.quotientAntitoneOn (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show Q * u ∈ Set.Ioi 0 from lt_of_lt_of_le zero_lt_one ht1) ht1
  have hquot' : Phi (Q * u) / (Q * u) ≤ Phi 1 := by simpa using hquot
  have hkey : Q⁻¹ * Phi (Q * u) = u * (Phi (Q * u) / (Q * u)) := by
    field_simp
  calc rescalePinchingFunction Q Phi u = Q⁻¹ * Phi (Q * u) := rfl
    _ = u * (Phi (Q * u) / (Q * u)) := hkey
    _ ≤ u * Phi 1 := mul_le_mul_of_nonneg_left hquot' (le_trans zero_le_one hu1)
    _ ≤ max C 1 * Phi 1 := mul_le_mul_of_nonneg_right hu (le_of_lt (hPhi.pos 1))
    _ = Phi 1 * max C 1 := by ring

private theorem rescalePinchingFunction_le_phi_one_mul_max_of_le_one
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) {Q C u : ℝ}
    (hQ : 1 ≤ Q) (hu1 : u ≤ 1) :
    rescalePinchingFunction Q Phi u ≤ Phi 1 * max C 1 := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQu : Q * u ≤ Q := by nlinarith
  have hinv : (0 : ℝ) ≤ Q⁻¹ := le_of_lt (inv_pos.mpr hQpos)
  have hquot := hPhi.quotientAntitoneOn (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show Q ∈ Set.Ioi 0 from hQpos) hQ
  have hquot' : Phi Q / Q ≤ Phi 1 := by simpa using hquot
  have hM : Phi 1 ≤ Phi 1 * max C 1 := by
    nlinarith [hPhi.pos 1, le_max_right C 1]
  calc rescalePinchingFunction Q Phi u = Q⁻¹ * Phi (Q * u) := rfl
    _ ≤ Q⁻¹ * Phi Q := mul_le_mul_of_nonneg_left (hPhi.mono hQu) hinv
    _ = Phi Q / Q := by rw [div_eq_inv_mul]
    _ ≤ Phi 1 := hquot'
    _ ≤ Phi 1 * max C 1 := hM

theorem rescalePinchingFunction_le_phi_one_mul_max
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) {Q C u : ℝ}
    (hQ : 1 ≤ Q) (hu : u ≤ max C 1) :
    rescalePinchingFunction Q Phi u ≤ Phi 1 * max C 1 := by
  rcases le_or_gt 1 u with h1 | h1
  · exact rescalePinchingFunction_le_phi_one_mul_max_of_one_le_le hPhi hQ h1 hu
  · exact rescalePinchingFunction_le_phi_one_mul_max_of_le_one hPhi hQ h1.le

theorem pointedFlowRmNormSqBounded_of_scalarBounded_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) {C : ℝ}
    (hscal : PointedFlowScalarBounded (X.term i) C) (hQ : 1 ≤ X.scale i) :
    PointedFlowRmNormSqBounded (X.term i)
      ((2 * (2 * Real.sqrt 3) * (max C 1 / 4 + 2 * (Phi 1 * max C 1))) ^ 2) := by
  intro t ht y
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hquarter : 4 * (max C 1 / 4) = max C 1 := by ring
  have hP : 0 < max C 1 / 4 := by positivity
  have hub : (X.term i).S.scalar t y ≤ 4 * (max C 1 / 4) := by
    rw [hquarter]
    exact le_trans (hscal t ht y).2 (le_max_left C 1)
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

theorem uniformRmNormSqBound_of_uniformScalarBound_and_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {C : ℝ}
    (hscal : ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C) :
    UniformRmNormSqBound X :=
  uniformRmNormSqBound_of_eventually X
    ((X.scale_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ))).mono fun i hi =>
      pointedFlowRmNormSqBounded_of_scalarBounded_and_pinching hPhi X i (hscal i) hi)

abbrev UniformScalarBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∃ C : ℝ, 0 < C ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
        PointedFlowScalarBounded (X.term i) C

theorem uniformScalarBoundProducer_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    UniformScalarBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal, _⟩ := h
  exact ⟨epsStar, hepsStar, C, hC, hscal⟩

theorem uniformRmNormSqBoundProducer_of_uniformScalarBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (h : UniformScalarBoundProducer.{u} kappa sigma Phi) :
    UniformRmNormSqBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, _, hscal⟩ := h
  exact ⟨epsStar, hepsStar, fun eps heps hle X =>
    uniformRmNormSqBound_of_uniformScalarBound_and_pinching hPhi X (hscal eps heps hle X)⟩

theorem uniformRmNormSqBoundProducer_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    UniformRmNormSqBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, _, hscal, hric⟩ := h
  exact ⟨epsStar, hepsStar, fun eps heps hle X =>
    uniformRmNormSqBound_of_uniformScalarBound_and_ricciNonnegative X
      (hscal eps heps hle X) (hric eps heps hle X)⟩

theorem uniformRmNormSqBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {epsStar C : ℝ} (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hcone : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ t ∈ (X.interval i).carrier,
          PointedFlowNonnegativeCurvatureOperator (X.term i) t) :
    UniformRmNormSqBoundProducer.{u} kappa sigma Phi :=
  ⟨epsStar, hepsStar, fun eps heps hle X =>
    uniformRmNormSqBound_of_uniformScalarBound_and_curvatureOperatorNonnegative X
      (hscal eps heps hle X) (hcone eps heps hle X)⟩

private theorem boundedAtDistance_of_uniformRmNormSqBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : UniformRmNormSqBound X) : BoundedAtDistance X := by
  obtain ⟨K, hK⟩ := h
  refine boundedAtDistance_of_terminalRmBallBound X fun ρ hρ =>
    terminalParabolicRmBallBound_of_uniformRmNormSqBound X hK 0 ρ ?_
  intro i t ht
  rw [X.carrier_eq i]
  exact ⟨by linarith [X.depth_pos i, ht.1], ht.2⟩

private theorem boundedAtDistanceShell_of_uniformRmNormSqBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformRmNormSqBoundProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, hb⟩ := h
  exact ⟨epsStar, hepsStar, fun eps heps hle X =>
    boundedAtDistance_of_uniformRmNormSqBound X (hb eps heps hle X)⟩

theorem boundedAtDistanceShell_of_uniformScalarBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (h : UniformScalarBoundProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_uniformRmNormSqBoundProducer
    (uniformRmNormSqBoundProducer_of_uniformScalarBoundProducer hPhi h)

theorem boundedAtDistanceShell_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_uniformRmNormSqBoundProducer
    (uniformRmNormSqBoundProducer_of_uniformScalarRicciNonnegativeProducer h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
