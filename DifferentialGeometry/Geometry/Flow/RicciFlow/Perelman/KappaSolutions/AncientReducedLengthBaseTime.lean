import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_redLength_base_time_bounds_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ {R T tau : ℝ}, R ≤ T → T ≤ 0 → 0 < tau →
      ∀ p q : F.M,
        redLength F.S T p q tau - tau * C * (T - R) ≤ redLength F.S R p q tau ∧
        redLength F.S R p q tau ≤ Real.exp (K * (T - R)) * redLength F.S T p q tau := by
  obtain ⟨C, hC, hlo⟩ := exists_lCost_base_time_bound_of_ancient F hF
  obtain ⟨K, hK, hhi⟩ := exists_lCost_base_time_exp_bound_of_ancient F hF
  refine ⟨C, K, hC, hK, ?_⟩
  intro R T tau hRT hT htau p q
  have hs : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hs2 : Real.sqrt tau ^ 2 = tau := Real.sq_sqrt htau.le
  have hd : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) hs
  constructor
  · have h := div_le_div_of_nonneg_right (hlo hRT hT htau p q) hd.le
    rw [add_div] at h
    have heq : (2 * Real.sqrt tau ^ 3 * C * (T - R)) / (2 * Real.sqrt tau) =
        tau * C * (T - R) := by
      conv_rhs => rw [← hs2]
      field_simp
    rw [heq] at h
    change lCost F.S T p q tau / (2 * Real.sqrt tau) - tau * C * (T - R) ≤
      lCost F.S R p q tau / (2 * Real.sqrt tau)
    linarith only [h]
  · have h := div_le_div_of_nonneg_right (hhi hRT hT htau p q) hd.le
    simpa only [redLength, mul_div_assoc] using h

theorem tendstoLocallyUniformlyOn_redLength_terminal_base_time
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    TendstoLocallyUniformlyOn
      (fun R (z : ℝ × F.M) => redLength F.S R p z.2 z.1)
      (fun z => redLength F.S 0 p z.2 z.1) (𝓝[≤] (0 : ℝ)) (Ioi 0 ×ˢ univ) := by
  obtain ⟨C, K, hC, hK, hbounds⟩ := exists_redLength_base_time_bounds_of_ancient F hF
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro epsilon hepsilon x hx
  let A := |redLength F.S 0 p x.2 x.1| + 1
  let B := |x.1| + 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let V := {z : ℝ × F.M | z ∈ Ioi 0 ×ˢ univ ∧ redLength F.S 0 p z.2 z.1 < A ∧ z.1 < B}
  have hV : V ∈ 𝓝[Ioi 0 ×ˢ univ] x := by
    have hv := (continuousOn_redLength_space_time_of_ancient F hF p x hx).eventually
      (Iio_mem_nhds (show redLength F.S 0 p x.2 x.1 < A by dsimp only [A]; linarith [le_abs_self (redLength F.S 0 p x.2 x.1)]))
    have ht : ∀ᶠ z : ℝ × F.M in 𝓝[Ioi 0 ×ˢ univ] x, z.1 < B :=
      (continuousAt_fst.eventually (Iio_mem_nhds
        (show x.1 < B by dsimp only [B]; linarith [le_abs_self x.1]))).filter_mono nhdsWithin_le_nhds
    exact (show ∀ᶠ z in 𝓝[Ioi 0 ×ˢ univ] x, z ∈ Ioi 0 ×ˢ univ from
      self_mem_nhdsWithin).and (hv.and ht)
  let err : ℝ → ℝ := fun R => (Real.exp (K * (-R)) - 1) * A + B * C * (-R)
  have herr : Continuous err := by dsimp only [err]; fun_prop
  have hezero : err 0 = 0 := by simp only [err, neg_zero, mul_zero, Real.exp_zero, sub_self, zero_mul, add_zero]
  have hevent : ∀ᶠ R in 𝓝[≤] (0 : ℝ), err R < epsilon :=
    (herr.continuousAt.eventually (Iio_mem_nhds (show err 0 < epsilon by rw [hezero]; exact hepsilon))).filter_mono nhdsWithin_le_nhds
  refine ⟨V, hV, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hevent] with R hR hsmall
  intro z hz
  obtain ⟨hzt, hzA, hzB⟩ := hz
  have hb := hbounds hR le_rfl hzt.1 p z.2
  simp only [zero_sub] at hb
  have he : 0 ≤ Real.exp (K * (-R)) - 1 := sub_nonneg.mpr
    (Real.one_le_exp (mul_nonneg hK (neg_nonneg.mpr hR)))
  have hu := mul_le_mul_of_nonneg_left hzA.le he
  have hl := mul_le_mul_of_nonneg_right hzB.le (mul_nonneg hC (neg_nonneg.mpr hR))
  have hupperpos : 0 ≤ (Real.exp (K * (-R)) - 1) * A := mul_nonneg he hA
  have hlowerpos : 0 ≤ B * C * (-R) := mul_nonneg (mul_nonneg hB hC) (neg_nonneg.mpr hR)
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ hsmall
  apply abs_le.mpr
  dsimp only [err]
  constructor <;> nlinarith only [hb.1, hb.2, hu, hl, hupperpos, hlowerpos]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
