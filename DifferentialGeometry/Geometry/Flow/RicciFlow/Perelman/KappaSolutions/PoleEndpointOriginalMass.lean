import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleRescaledReducedLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointFractionalDensityBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem volume_scale_inv_coefficient {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (Real.sqrt s⁻¹) ^ Module.finrank ℝ E =
      ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log s)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) _]
  congr 1
  rw [← Real.exp_log (pow_pos (Real.sqrt_pos.mpr (inv_pos.mpr hs)) _),
    Real.log_pow, Real.log_sqrt (inv_nonneg.mpr hs.le), Real.log_inv]
  congr 1
  ring

theorem poleEndpoint_lintegral_original_redLength
    (hcar : ancientTimeInterval.carrier = Iic 0) (hreg : ancientTimeInterval.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (p : F.M) :
    let Y := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
    let c : ℝ := Real.exp
      (((Module.finrank ℝ E : ℝ) / 2) * (Real.log (tau i + b) - Real.log (tau i)))
    ENNReal.ofReal (c * Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) *
      (∫⁻ x : F.M, ENNReal.ofReal (Real.exp (-redLength F.S 0 p x (tau i)))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)) =
      intrinsicReducedVolume F.S 0 p (tau i) := by
  dsimp only
  rw [poleEndpointRescaledFlowSeq_volume_zero F hcar hreg b hbmem tau q hsigma i,
    lintegral_smul_measure, smul_eq_mul, volume_scale_inv_coefficient (hsigma i)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hcoeff :
      Real.exp (((Module.finrank ℝ E : ℝ) / 2) *
        (Real.log (tau i + b) - Real.log (tau i))) *
        Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (tau i + b)) =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (tau i) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hcoeff]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold intrinsicReducedVolume
  rw [zero_sub]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  unfold redLength
  ring

theorem poleEndpoint_lintegral_pole_redLength
    (hcar : ancientTimeInterval.carrier = Iic 0) (hreg : ancientTimeInterval.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (p : F.M) :
    let U := poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
    let Y := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
    ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) *
      (∫⁻ x : F.M, ENNReal.ofReal (Real.exp (-redLength (U.term i).S 0 p x 1))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)) =
      intrinsicReducedVolume F.S b p (tau i + b) := by
  dsimp only
  simp_rw [poleRescaledFlowSeq_redLength_one F hcar hreg b hbmem tau q hsigma i p]
  rw [poleEndpointRescaledFlowSeq_volume_zero F hcar hreg b hbmem tau q hsigma i,
    lintegral_smul_measure, smul_eq_mul, volume_scale_inv_coefficient (hsigma i)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold intrinsicReducedVolume
  rw [show b - (tau i + b) = -tau i by ring]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  unfold redLength
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
