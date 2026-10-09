import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood (ancientTimeInterval)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth

theorem poleRescaledFlowSeq_redLength_one
    (hcar : ancientTimeInterval.carrier = Iic 0) (hreg : ancientTimeInterval.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (i : ℕ) (p x : F.M) :
    redLength ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p x 1 =
      redLength F.S b p x (tau i + b) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  change redLength (parabolicSolution F.S b (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) hbmem)
    0 p x 1 = _
  have h := redLength_parabolic F.S b (tau i + b)⁻¹ b (tau i + b)
    (inv_pos.mpr (hsigma i)) hbmem (hsigma i).le p x
  simpa only [parabolicBackward, sub_self, mul_zero, inv_mul_cancel₀ (hsigma i).ne'] using h


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
