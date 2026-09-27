import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeRatio


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_redLength_le_uniform_time_ratio
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b tau A : ℝ} (ha : 0 < a)
    (htau : tau ∈ Icc a b) (hbase : redLength F.S 0 p q 1 ≤ A) :
    redLength F.S 0 p q tau ≤ max (b ^ 2) ((1 / a) ^ 2) * A := by
  have htau0 : 0 < tau := ha.trans_le htau.1
  have hb0 : 0 < b := htau0.trans_le htau.2
  have hnonneg : 0 ≤ redLength F.S 0 p q 1 := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 zero_le_one
    intro r hr x
    exact (hC (0 - r) (by
      simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
        neg_nonpos.mpr hr.1) x).1
  have hsquare : tau ^ 2 ≤ b ^ 2 := by
    simpa only [pow_two] using mul_le_mul htau.2 htau.2 htau0.le hb0.le
  have hinv : 1 / tau ≤ 1 / a := one_div_le_one_div_of_le ha htau.1
  have hinv0 : 0 < 1 / tau := one_div_pos.mpr htau0
  have hia0 : 0 < 1 / a := one_div_pos.mpr ha
  have hinvSquare : (1 / tau) ^ 2 ≤ (1 / a) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hinv hinv hinv0.le hia0.le
  have hratioBound : max (tau ^ 2) ((1 / tau) ^ 2) ≤ max (b ^ 2) ((1 / a) ^ 2) :=
    max_le_max hsquare hinvSquare
  have hratio := ancient_redLength_le_mul_time_ratio F hF p q zero_lt_one htau0
  simp only [div_one] at hratio
  exact hratio.trans ((mul_le_mul_of_nonneg_right hratioBound hnonneg).trans
    (mul_le_mul_of_nonneg_left hbase ((sq_nonneg b).trans (le_max_left _ _))))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
