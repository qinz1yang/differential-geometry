import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CarrierRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.CarrierRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Existence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter MeasureTheory Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped ContDiff Manifold Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance ancientMinimizerC1Topology : TopologicalSpace F.M := F.topology
local instance ancientMinimizerC1Charted : ChartedSpace H F.M := F.charted
local instance ancientMinimizerC1Smooth : IsManifold I ∞ F.M := F.smooth
local instance ancientMinimizerC1T2 : T2Space F.M := F.t2
local instance ancientMinimizerC1Sigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_lRegularizedMin_contMDiffOn_one_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ (gamma : ℝ → F.M) (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → F.M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc 0 (Real.sqrt tau)) ∧
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
  obtain ⟨gamma, m, t, p, u, hgamma, hga, hgb, ht, ht0, htl, hsrc, hrep,
    hint, heq, hmin⟩ := exists_lRegularizedMin_of_ancient F hF x y htau
  have hmin' : ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = gamma 0 → delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
        lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
    intro delta hd hda hdb
    exact hmin delta hd (hda.trans hga) (hdb.trans hgb)
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc 0 (Real.sqrt tau)) := by
    apply lMinCurve_c1_of_spatial_derivatives F.S F.isSolution 0 0 (Real.sqrt tau)
      (Real.sqrt_pos.mpr htau) t ht ht0 htl p gamma hgamma u hsrc hrep
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
  exact ⟨gamma, m, t, p, u, hc1, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
