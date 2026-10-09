import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CollapsedReducedVolume


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff


def universalKappaTheta : ℝ :=
  Classical.choose (exists_collapsedVolumeTail_small (27 / 2))

theorem universalKappaTheta_spec :
    0 < universalKappaTheta ∧ universalKappaTheta ≤ 1 ∧
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta < Real.exp (-1) / 4 :=
  Classical.choose_spec (exists_collapsedVolumeTail_small (27 / 2))


def universalKappaConstant : ℝ :=
  (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ) *
    Real.exp (-((27 / 2 : ℝ) * universalKappaTheta)) * Real.exp (-1) / 4

theorem universalKappaConstant_pos : 0 < universalKappaConstant := by
  have htheta := universalKappaTheta_spec.1
  unfold universalKappaConstant
  positivity


theorem universalKappaConstant_normalization :
    (4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
      Real.exp ((27 / 2 : ℝ) * universalKappaTheta) * universalKappaConstant =
        Real.exp (-1) / 4 := by
  have hb : 0 < 4 * Real.pi * universalKappaTheta := by
    have htheta := universalKappaTheta_spec.1
    positivity
  have hp : (4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
      (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero]
  have he : Real.exp ((27 / 2 : ℝ) * universalKappaTheta) *
      Real.exp (-((27 / 2 : ℝ) * universalKappaTheta)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold universalKappaConstant
  calc
    _ = ((4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
          (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ)) *
        (Real.exp ((27 / 2 : ℝ) * universalKappaTheta) *
          Real.exp (-((27 / 2 : ℝ) * universalKappaTheta))) * Real.exp (-1) / 4 := by ring
    _ = _ := by rw [hp, he]; ring

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance universalKappaTopology : TopologicalSpace F.M := F.topology
local instance universalKappaCharted : ChartedSpace H F.M := F.charted
local instance universalKappaSmooth : IsManifold I ∞ F.M := F.smooth
local instance universalKappaT2 : T2Space F.M := F.t2
local instance universalKappaSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩


theorem ancientKappaThree_terminal_universal_noncollapsed
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) (p : F.M)
    {r : ℝ} (hr : 0 < r)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) :
    ENNReal.ofReal (universalKappaConstant * r ^ 3) ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (F.S.base.metric 0) p r) := by
  by_contra hvolume
  have htheta := universalKappaTheta_spec.1
  have hlower := ancientKappaThree_reducedVolume_lower F hF hdim hnotround p
    (mul_pos htheta (sq_pos_of_pos hr))
  have hupper := ancientKappaThree_collapsedBall_reducedVolume_upper F hF hdim p hr
    universalKappaConstant_pos htheta hcontrol (lt_of_not_ge hvolume)
  rw [universalKappaConstant_normalization] at hupper
  have hsmall : Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta < Real.exp (-1) := by
    have htail := universalKappaTheta_spec.2.2
    have he := Real.exp_pos (-1 : ℝ)
    linarith
  have hnonneg : 0 ≤ Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta :=
    add_nonneg (by positivity) (collapsedReducedVolumeTail_nonneg (27 / 2) htheta)
  exact not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).mpr hsmall)
    (hlower.trans hupper)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
