import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedCostAsymptotics
import DifferentialGeometry.Analysis.Real.NormalizedCostComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_ancientKappa_redLength_baseTime_mul_add_bounds
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {d delta : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) :
    ∃ C T : ℝ, 0 ≤ C ∧ d < T ∧ ∀ tau > T, ∀ p q : F.M,
      redLength F.S (-d) p q (tau - d) ≤
          (1 + delta) * redLength F.S 0 p q tau + C / Real.sqrt tau ∧
        redLength F.S 0 p q tau ≤
          (1 + delta) * redLength F.S (-d) p q (tau - d) + C / Real.sqrt tau := by
  let epsilon : ℝ := min (delta / 4) (1 / 4)
  have heps : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsQuarter : epsilon ≤ 1 / 4 := min_le_right _ _
  have hfour : 4 * epsilon ≤ delta := by
    have h := min_le_left (delta / 4) (1 / 4 : ℝ)
    dsimp only [epsilon]
    linarith
  obtain ⟨C, T0, hC, hdT0, hcost⟩ :=
    exists_ancientKappa_lCost_baseTime_mul_add_bounds F hdim hF hd heps
  let T : ℝ := max T0 (d + d / epsilon)
  have hdT : d < T := hdT0.trans_le (le_max_left _ _)
  refine ⟨C, T, hC, hdT, ?_⟩
  intro tau htau p q
  have htau0 : T0 < tau := lt_of_le_of_lt (le_max_left _ _) htau
  have htauEps : d + d / epsilon < tau := lt_of_le_of_lt (le_max_right _ _) htau
  have hsigma : 0 < tau - d := sub_pos.mpr (hdT.trans htau)
  have htaupos : 0 < tau := hd.trans (hdT.trans htau)
  have hv : 0 < Real.sqrt (tau - d) := Real.sqrt_pos.mpr hsigma
  have hvu : Real.sqrt (tau - d) ≤ Real.sqrt tau :=
    Real.sqrt_le_sqrt (sub_le_self _ hd.le)
  have hde : d ≤ epsilon * (tau - d) := by
    have h := (div_lt_iff₀ heps).mp (show d / epsilon < tau - d by linarith)
    nlinarith
  have hsqrtRatio : Real.sqrt tau ≤ (1 + epsilon) * Real.sqrt (tau - d) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by positivity) hv.le, ?_⟩
    rw [mul_pow, Real.sq_sqrt hsigma.le]
    nlinarith [mul_nonneg heps.le hsigma.le,
      mul_nonneg (sq_nonneg epsilon) hsigma.le]
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  have hnonneg (T lag : ℝ) (hT : T ≤ 0) (hlag : 0 ≤ lag) :
      0 ≤ lCost F.S T p q lag :=
    lCost_nonneg_of_scalar_nonneg F.S T hlag
      (fun s hs x => (hR _ ((sub_le_self T hs.1).trans hT) x).1) p q
  have hnormalized := DifferentialGeometry.Analysis.normalized_cost_comparison
    (hnonneg (-d) (tau - d) (neg_nonpos.mpr hd.le) hsigma.le)
    (hnonneg 0 tau le_rfl htaupos.le) hC hv hvu hsqrtRatio heps.le hepsQuarter hfour
    (hcost tau htau0 p q).1 (hcost tau htau0 p q).2
  simpa only [redLength, mul_div_assoc] using hnormalized

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
