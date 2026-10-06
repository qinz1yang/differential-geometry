import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepShift
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicScale

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

theorem contMDiff_shift_CPA2 {b : ℝ} (hb : 0 ≤ b) :
    ContMDiff halfCollarModel halfCollarModel ∞ (shift_CPA2 b) :=
  contMDiff_fst.prodMk ((contMDiff_halfShift_CPA2 hb).comp contMDiff_snd)

/-- The shifted cusp parametrization is an isometric immersion for the rescaled cusp. -/
theorem deepCuspIsometry_CPA2 {b : ℝ} (hb : 0 ≤ b) (i : Fin T.count) (p : CuspHalfSpace)
    (v w : TangentSpace halfCollarModel p) :
    H.metric.inner (deepCuspMap_CPA2 T b i p)
      (mfderiv halfCollarModel (𝓡 3) (deepCuspMap_CPA2 T b i) p v)
      (mfderiv halfCollarModel (𝓡 3) (deepCuspMap_CPA2 T b i) p w) =
      (deepCusp_CPA (T.cusp i) b).metric.inner p v w := by
  have hde : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) (shift_CPA2 b p) :=
    (T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp)
  have hds : MDifferentiableAt halfCollarModel halfCollarModel (shift_CPA2 b) p :=
    (contMDiff_shift_CPA2 hb).mdifferentiableAt (by simp)
  have hcomp : mfderiv halfCollarModel (𝓡 3) (deepCuspMap_CPA2 T b i) p =
      (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (shift_CPA2 b p)).comp
        (mfderiv halfCollarModel halfCollarModel (shift_CPA2 b) p) :=
    mfderiv_comp p hde hds
  rw [hcomp, mfderiv_shift_CPA2 hb]
  have h1 := T.cuspIsometry i (shift_CPA2 b p) v w
  have hf1 := (T.cusp i).metric_formula (shift_CPA2 b p) v w
  have hf2 := (deepCusp_CPA (T.cusp i) b).metric_formula p v w
  have h3 := deepCusp_torusMetric_inner_CPA (T.cusp i) b p.1 v.1 w.1
  rw [h3] at hf2
  change H.metric.inner (T.cuspMap i (shift_CPA2 b p))
      (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (shift_CPA2 b p) v)
      (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (shift_CPA2 b p) w) = _
  rw [h1, hf1, hf2, shift_height_CPA2 hb, neg_add, Real.exp_add]
  have : (shift_CPA2 b p).1 = p.1 := rfl
  rw [this]
  ring

end GC.LongTime.CuspP1
