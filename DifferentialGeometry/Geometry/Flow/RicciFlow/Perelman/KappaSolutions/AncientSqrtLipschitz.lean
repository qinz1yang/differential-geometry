import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostSupport
import DifferentialGeometry.Geometry.Comparison.Distance.SqrtSupport

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance lipschitzTopology : TopologicalSpace F.M := F.topology
local instance lipschitzCharted : ChartedSpace H F.M := F.charted
local instance lipschitzSmooth : IsManifold I ∞ F.M := F.smooth
local instance lipschitzT2 : T2Space F.M := F.t2
local instance lipschitzSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x y : F.M) {tau : ℝ} (htau : 0 < tau)
    (hcont : Continuous (fun z ↦ redLength F.S 0 p z tau))
    (hmin : ∀ z : F.M, ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = p ∧ alpha (Real.sqrt tau) = z ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    Real.sqrt (redLength F.S 0 p y tau) ≤ Real.sqrt (redLength F.S 0 p x tau) +
      Real.sqrt 3 / (2 * Real.sqrt tau) * (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal := by
  let _ : ConnectedSpace F.M := hF.connected
  have htime : -tau ∈ ancientTimeInterval.carrier := by
    simpa only [ancientTimeInterval_carrier, mem_Iic] using neg_nonpos.mpr htau.le
  apply DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support
    (F.S.base.metric (-tau)) ⟨MetricComplete.complete (F.atTime (-tau)) (hF.complete (-tau) htime)⟩ hcont
    (by positivity : 0 ≤ Real.sqrt 3 / (2 * Real.sqrt tau)) ?_ x y
    (DifferentialGeometry.riemannianEDistOf_ne_top _ _ _)
  intro gamma t hgamma _hpos
  let beta : ℝ → F.M := fun r ↦ gamma (r + t)
  have hbeta : IsGeodesicAt (I := I) (F.S.base.metric (-tau)) beta 0 := by
    simpa only [sub_self] using DifferentialGeometry.Geometry.isGeodesicAt_comp_add hgamma t
  obtain ⟨alpha, halpha, halpha0, hend, hgeo, hcost⟩ := hmin (gamma t)
  have hbeta0 : beta 0 = alpha (Real.sqrt tau) := by simpa only [beta, zero_add] using hend.symm
  obtain ⟨phi, d, heq, hupper, hd, hbound⟩ :=
    exists_redLength_upper_support_of_ancient_minimizer F hF p htau alpha beta
      halpha halpha0 hgeo hcost hbeta hbeta0
  have hshift : Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (0 : ℝ)) := by
    have hh : Continuous (fun r : ℝ ↦ r - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hh.tendsto t
  have hupper' : (fun r ↦ redLength F.S 0 p (gamma r) tau) ≤ᶠ[𝓝 t]
      (fun r ↦ phi (r - t)) := by
    filter_upwards [hshift hupper] with r hr
    change redLength F.S 0 p (gamma ((r - t) + t)) tau ≤ phi (r - t) at hr
    simpa only [sub_add_cancel] using hr
  have hderiv : HasDerivAt (fun r ↦ phi (r - t)) d t := by
    have hd' : HasDerivAt phi d (t - t) := by simpa only [sub_self] using hd
    have hp := HasDerivAt.comp t (h₂ := phi) (h := fun r : ℝ ↦ r - t) hd' ((hasDerivAt_id t).sub_const t)
    convert hp using 1 <;> first | rfl | simp only [mul_one]
  have hgammaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (0 + t) := by
    simpa only [zero_add] using (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hgamma).mdifferentiableAt (by simp)
  have hvelocity : lVelocity (I := I) beta 0 = mfderiv 𝓘(ℝ, ℝ) I gamma t 1 := by
    have hv := DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one 0 t hgammaDiff
    have hm : (mfderiv 𝓘(ℝ, ℝ) I gamma (0 + t) (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ) : E) :=
      congrArg (fun s : ℝ ↦ (mfderiv 𝓘(ℝ, ℝ) I gamma s (1 : ℝ) : E)) (zero_add t)
    rw [hm] at hv
    exact hv
  refine ⟨fun r ↦ phi (r - t), d, ?_, hupper'.filter_mono nhdsWithin_le_nhds, hderiv, ?_⟩
  · simpa only [sub_self, beta, zero_add] using heq
  · have hbound' : d ≤ Real.sqrt 3 / Real.sqrt tau * Real.sqrt (redLength F.S 0 p (gamma t) tau) *
      Real.sqrt ((F.S.base.metric (-tau)).inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)) := by
      simp only [hvelocity] at hbound
      have hbase : beta 0 = gamma t := congrArg gamma (zero_add t)
      have hmetric : (F.S.base.metric (-tau)).inner (beta 0) =
          (F.S.base.metric (-tau)).inner (gamma t) := congrArg _ hbase
      rw [hmetric, hbase] at hbound
      exact hbound
    have hfactor : 2 * (Real.sqrt 3 / (2 * Real.sqrt tau)) = Real.sqrt 3 / Real.sqrt tau := by ring
    rw [hfactor]
    exact hbound'

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
