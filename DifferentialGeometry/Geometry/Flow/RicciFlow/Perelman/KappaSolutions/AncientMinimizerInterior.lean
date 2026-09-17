import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMinimizerC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import DifferentialGeometry.Topology.Manifold.CurveIntervalExtension

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter MeasureTheory Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped ContDiff Manifold _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance ancientMinimizerInteriorTopology : TopologicalSpace F.M := F.topology
local instance ancientMinimizerInteriorCharted : ChartedSpace H F.M := F.charted
local instance ancientMinimizerInteriorSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientMinimizerInteriorT2 : T2Space F.M := F.t2
local instance ancientMinimizerInteriorSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ (gamma : ℝ → F.M) (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → F.M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc 0 (Real.sqrt tau)) ∧
      IsLRegularizedGeodesicOn F.S 0 gamma (Ioo 0 (Real.sqrt tau)) ∧
      Continuous gamma ∧ gamma 0 = x ∧ gamma (Real.sqrt tau) = y ∧
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last m) = Real.sqrt tau ∧
      (∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, EqOn (u i).toFun
        (fun r => extChartAt I (p i) (gamma (t i.castSucc + r)))
        (Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
      IntervalIntegrable (lRegularizedLagrangian F.S 0 gamma) volume 0 (Real.sqrt tau) ∧
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) = lCost F.S 0 x y tau ∧
      ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
        delta 0 = x → delta (Real.sqrt tau) = y →
        lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
          lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨gamma, m, t, p, u, hc1, hgamma, hga, hgb, ht, ht0, htl, hsrc, hrep,
    hint, heq, hmin⟩ := exists_lRegularizedMin_contMDiffOn_one_of_ancient F hF x y htau
  have hmin' : ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = gamma 0 → delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
        lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
    intro delta hd hda hdb
    exact hmin delta hd (hda.trans hga) (hdb.trans hgb)
  have hgeo : IsLRegularizedGeodesicOn F.S 0 gamma (Ioo 0 (Real.sqrt tau)) := by
    apply lMinCurve_regularizedGeodesicOn_of_spatial_derivatives F.S F.isSolution 0 0 (Real.sqrt tau)
      t ht ht0 htl p gamma hgamma u hsrc hrep
      (Iic 0) (by simpa only [ancientTimeInterval_carrier] using (Subset.rfl : Iic (0 : ℝ) ⊆ Iic 0))
      ?_ ?_ ?_ ?_ hmin'
    · intro r hr
      simpa only [zero_sub, mem_Iic] using neg_nonpos.mpr (sq_nonneg r)
    · intro r hr
      rw [ancientTimeInterval_regular, mem_Iio, zero_sub]
      exact neg_neg_of_pos (sq_pos_of_pos hr.1)
    · intro q
      exact (solution_chartGramOp_spatial_fderiv_continuousOn_carrier F.S F.isSolution
        ancientTimeInterval_carrier ancientTimeInterval_regular q).mono
        (fun _ hz => ⟨hz.1, interior_subset hz.2⟩)
    · intro q
      exact (solution_chartScalar_fderiv_continuousOn_carrier F.S F.isSolution
        ancientTimeInterval_carrier ancientTimeInterval_regular q).mono
        (fun _ hz => ⟨hz.1, interior_subset hz.2⟩)
  exact ⟨gamma, m, t, p, u, hc1, hgeo, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter MeasureTheory Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped ContDiff Manifold _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance ancientGlobalMinimizerInteriorTopology : TopologicalSpace F.M := F.topology
local instance ancientGlobalMinimizerInteriorCharted : ChartedSpace H F.M := F.charted
local instance ancientGlobalMinimizerInteriorSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientGlobalMinimizerInteriorT2 : T2Space F.M := F.t2
local instance ancientGlobalMinimizerInteriorSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)) ∧ alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) = lCost F.S 0 x y tau ∧
      ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
        delta 0 = x → delta (Real.sqrt tau) = y →
        lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) ≤
          lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
  obtain ⟨gamma, m, t, p, u, hc1, hgeo, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩ := exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient F hF x y htau
  obtain ⟨alpha, halpha, heqOn⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_extension_Icc (k := 1) hc1
  have hact : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) := by
    apply lRegularizedAction_congr F.S 0
    intro s hs
    rw [uIoo_of_le (Real.sqrt_nonneg tau)] at hs
    exact heqOn ⟨hs.1.le, hs.2.le⟩
  have hgeoAlpha : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)) := by
    apply hgeo.congr_of_eventuallyEq
    intro r hr
    exact heqOn.eventuallyEq_of_mem (mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Icc_self)
  refine ⟨alpha, halpha, hgeoAlpha,
    (heqOn ⟨le_rfl, Real.sqrt_nonneg tau⟩).trans hga,
    (heqOn ⟨Real.sqrt_nonneg tau, le_rfl⟩).trans hgb,
    hact.trans heq, ?_⟩
  intro delta hd hda hdb
  rw [hact]
  exact hmin delta hd hda hdb

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
