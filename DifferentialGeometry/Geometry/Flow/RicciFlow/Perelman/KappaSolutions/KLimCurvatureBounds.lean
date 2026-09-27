import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimCurvatureTopology : TopologicalSpace F.M := F.topology
local instance klimCurvatureCharted : ChartedSpace H F.M := F.charted
local instance klimCurvatureSmooth : IsManifold I ∞ F.M := F.smooth
local instance klimCurvatureC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance klimCurvatureT2 : T2Space F.M := F.t2
local instance klimCurvatureSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem pointedFlow_rmNormLeScalar_of_nonnegativeOperator
    (hdim : Module.finrank ℝ E = 3)
    (hop : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t) :
    PointedFlowRmNormLeScalar (I := I) F (Real.sqrt 3) := by
  intro t ht x
  have hnonnegative : curvatureOperatorLowerBoundAt (I := I) (F.S.base.metric t) x
      ⟨F.S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric t) x⟩ 0 := by
    intro n c v w
    have h := hop t ht x n c v w
    simpa [algebraicCurvatureOperatorQuadraticEval,
      algebraicCurvatureIdentityQuadraticEval, tensor04StandardAt] using h
  have hbound := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
    (I := I) F.S hdim t x hnonnegative
  simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq,
    SolutionOn.family] using hbound

variable {kappa : ℝ}

theorem KLim.rmNormLeScalar_three (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    PointedFlowRmNormLeScalar (I := I) F (Real.sqrt 3) :=
  pointedFlow_rmNormLeScalar_of_nonnegativeOperator F hdim hK.nonnegativeCurvatureOperator

theorem KLim.rmNormSq_le_of_terminal_scalar_le (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3) {B t : ℝ} (ht : t ≤ 0)
    (x : F.M) (hB : F.S.scalar 0 x ≤ B) :
    F.rmNormSq (I := I) t x ≤ 3 * B ^ 2 := by
  have htcar : t ∈ D.carrier := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht
  have hroot := (hK.rmNormLeScalar_three F hdim t htcar x).trans
    (mul_le_mul_of_nonneg_left ((hK.scalar_le_terminal ht x).trans hB)
      (Real.sqrt_nonneg 3))
  calc
    _ ≤ (Real.sqrt 3 * B) ^ 2 := (Real.sqrt_le_iff.mp hroot).2
    _ = 3 * B ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem terminalCurvatureNormalizedFlowSeq_scalar_bound_mul (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r B : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ B * F.S.scalar 0 (x i))
    {s : ℝ} (hs : s ≤ 0) (z : F.M)
    (hz : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i))) :
    0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ∧
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ≤ B := by
  rw [terminalCurvatureNormalizedFlowSeq_dist F hK x hQ i z (x i)] at hz
  have hz0 : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r :=
    (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr (hQ i))).mp (by
      simpa only [mul_comm] using hz)
  have hs0 : s / F.S.scalar 0 (x i) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs (hQ i).le
  rw [terminalCurvatureNormalizedFlowSeq_scalar]
  refine ⟨mul_nonneg (inv_nonneg.mpr (hQ i).le) (hK.scalar_nonneg hs0 z), ?_⟩
  calc
    (F.S.scalar 0 (x i))⁻¹ * F.S.scalar (s / F.S.scalar 0 (x i)) z ≤
        (F.S.scalar 0 (x i))⁻¹ * (B * F.S.scalar 0 (x i)) :=
      mul_le_mul_of_nonneg_left ((hK.scalar_le_terminal hs0 z).trans (hlocal z hz0))
        (inv_nonneg.mpr (hQ i).le)
    _ = B := by rw [mul_left_comm, inv_mul_cancel₀ (hQ i).ne', mul_one]

theorem terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound_mul
    (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r B : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ B * F.S.scalar 0 (x i))
    {s : ℝ} (hs : s ≤ 0) (z : F.M)
    (hz : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i))) :
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤
      3 * B ^ 2 := by
  let G := (terminalCurvatureNormalizedFlowSeq F hK x hQ).term i
  have hsign : ∀ t ∈ ancientTimeInterval.carrier,
      PointedFlowNonnegativeCurvatureOperator (I := I) G t :=
    fun t ht => terminalCurvatureNormalizedFlowSeq_nonnegativeCurvatureOperator
      F hK x hQ i ht
  have hroot := pointedFlow_rmNormLeScalar_of_nonnegativeOperator G hdim hsign s hs z
  have hscalar := (terminalCurvatureNormalizedFlowSeq_scalar_bound_mul
    F hK x hQ i r B hlocal hs z hz).2
  have hbound := hroot.trans
    (mul_le_mul_of_nonneg_left hscalar (Real.sqrt_nonneg 3))
  calc
    _ ≤ (Real.sqrt 3 * B) ^ 2 := (Real.sqrt_le_iff.mp hbound).2
    _ = 3 * B ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
