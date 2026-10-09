import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostTimeSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostTimeContinuity
import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ratioTopology : TopologicalSpace F.M := F.topology
private local instance ratioCharted : ChartedSpace H F.M := F.charted
private local instance ratioSmooth : IsManifold I ∞ F.M := F.smooth
private local instance ratioT2 : T2Space F.M := F.t2
private local instance ratioSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_cube_mul_lCost_le_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ^ 3 * lCost F.S 0 p q (a ^ 2) ≤ b ^ 3 * lCost F.S 0 p q (b ^ 2) := by
  have hcont : ContinuousOn (fun r => lCost F.S 0 p q (r ^ 2)) (Icc a b) :=
    (ancient_lCost_continuousOn F hF p q).mono (fun _ hr => ha.trans_le hr.1)
  have hmono : MonotoneOn (fun r => r ^ 3 * lCost F.S 0 p q (r ^ 2))
      (Icc a b) := by
    apply DifferentialGeometry.monotoneOn_of_deriv_upper_support_nonneg
      ((continuousOn_id.pow 3).mul hcont)
    intro t ht
    have htpos : 0 < t := ha.trans ht.1
    obtain ⟨phi, d, htouch, hupper, hderiv, hbound⟩ :=
      exists_lCost_time_upper_support_of_ancient F hF p q htpos
    refine ⟨fun r => r ^ 3 * phi r, 3 * t ^ 2 * phi t + t ^ 3 * d, ?_, ?_, ?_, ?_⟩
    · change t ^ 3 * phi t = t ^ 3 * lCost F.S 0 p q (t ^ 2)
      rw [htouch]
    · have hupper' := hupper.filter_mono (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t)
      have hpos' := Filter.Eventually.filter_mono
        (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t) (Ioi_mem_nhds htpos)
      filter_upwards [hupper', hpos'] with r hr hrpos
      exact mul_le_mul_of_nonneg_left hr (pow_nonneg hrpos.le 3)
    · convert! ((hasDerivAt_id t).pow 3).mul hderiv using 1
      all_goals norm_num
    · rw [htouch]
      have htd := (div_le_iff₀ htpos).mp hbound
      have hp := mul_le_mul_of_nonneg_left htd (sq_nonneg t)
      nlinarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem ancient_redLength_le_mul_sq_time_ratio_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau₁ tau₂ : ℝ} (h₁ : 0 < tau₁) (h₁₂ : tau₁ ≤ tau₂) :
    redLength F.S 0 p q tau₁ ≤
      (tau₂ / tau₁) ^ 2 * redLength F.S 0 p q tau₂ := by
  have h₂ : 0 < tau₂ := h₁.trans_le h₁₂
  have ha := Real.sqrt_pos.mpr h₁
  have hb := Real.sqrt_pos.mpr h₂
  have h := ancient_cube_mul_lCost_le_of_le F hF p q ha (Real.sqrt_le_sqrt h₁₂)
  rw [Real.sq_sqrt h₁.le, Real.sq_sqrt h₂.le] at h
  have hsq₁ : tau₁ ^ 2 = (Real.sqrt tau₁) ^ 4 := by
    calc
      tau₁ ^ 2 = ((Real.sqrt tau₁) ^ 2) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) (Real.sq_sqrt h₁.le).symm
      _ = (Real.sqrt tau₁) ^ 4 := by ring
  have hsq₂ : tau₂ ^ 2 = (Real.sqrt tau₂) ^ 4 := by
    calc
      tau₂ ^ 2 = ((Real.sqrt tau₂) ^ 2) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) (Real.sq_sqrt h₂.le).symm
      _ = (Real.sqrt tau₂) ^ 4 := by ring
  unfold redLength
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt tau₁)).mpr
  have halgebra :
      (tau₂ / tau₁) ^ 2 * (lCost F.S 0 p q tau₂ / (2 * Real.sqrt tau₂)) *
          (2 * Real.sqrt tau₁) =
        ((Real.sqrt tau₂) ^ 3 * lCost F.S 0 p q tau₂) /
          (Real.sqrt tau₁) ^ 3 := by
    rw [div_pow, hsq₁, hsq₂]
    field_simp [ha.ne', hb.ne']
  rw [halgebra]
  apply (le_div_iff₀ (pow_pos ha 3)).mpr
  simpa only [mul_comm] using h

theorem ancient_redLength_le_mul_time_ratio
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau₁ tau₂ : ℝ} (h₁ : 0 < tau₁) (h₂ : 0 < tau₂) :
    redLength F.S 0 p q tau₂ ≤
      max ((tau₂ / tau₁) ^ 2) ((tau₁ / tau₂) ^ 2) * redLength F.S 0 p q tau₁ := by
  have hnonneg : 0 ≤ redLength F.S 0 p q tau₁ := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 h₁.le
    intro r hr x
    exact (hC (0 - r) (by
      simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
        neg_nonpos.mpr hr.1) x).1
  rcases le_total tau₁ tau₂ with h₁₂ | h₂₁
  · have hratio : 1 ≤ tau₂ / tau₁ := (le_div_iff₀ h₁).mpr (by simpa using h₁₂)
    have hsq : tau₂ / tau₁ ≤ (tau₂ / tau₁) ^ 2 := by nlinarith
    exact (ancient_redLength_le_mul_time_ratio_of_le F hF p q h₁ h₁₂).trans
      (mul_le_mul_of_nonneg_right (hsq.trans (le_max_left _ _)) hnonneg)
  · exact (ancient_redLength_le_mul_sq_time_ratio_of_le F hF p q h₂ h₂₁).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
