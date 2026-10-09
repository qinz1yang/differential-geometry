import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Retiming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricRetiming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
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

theorem ancientKappa_scalar_le_mul_sq
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    {b c a s : ℝ} (hc : 1 ≤ c) (hs : s ∈ Icc 0 a)
    (hbound : (c ^ 2 - 1) * a ^ 2 ≤ -b) (x : F.M) :
    F.S.scalar (b - s ^ 2) x ≤ F.S.scalar (-((c * s) ^ 2)) x := by
  have hcoef : 0 ≤ c ^ 2 - 1 := by nlinarith
  have hsquare : s ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hscaled : (c ^ 2 - 1) * s ^ 2 ≤ -b :=
    (mul_le_mul_of_nonneg_left hsquare hcoef).trans hbound
  have horder : b - s ^ 2 ≤ -((c * s) ^ 2) := by nlinarith only [hscaled]
  have htime : -((c * s) ^ 2) ≤ 0 := neg_nonpos.mpr (sq_nonneg (c * s))
  exact hF.scalar_monotoneOn x (horder.trans htime) htime horder

theorem exists_ancientKappa_lRegularizedAction_mul_le
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ 0, ∀ c a : ℝ, 1 ≤ c → 0 ≤ a →
      (c ^ 2 - 1) * a ^ 2 ≤ -b →
      ∀ alpha : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      lRegularizedAction F.S b (fun s => alpha (c * s)) 0 a ≤
        Real.exp (K * (-b)) * c * lRegularizedAction F.S 0 alpha 0 (c * a) := by
  obtain ⟨K, hK, hmetric⟩ := exists_ancientKappa_metric_inner_le_exp_mul_sq F hF
  refine ⟨K, hK, ?_⟩
  intro b hb c a hc ha hbound alpha halpha
  apply lRegularizedAction_mul_le_of_metric_comparison F.S F.isSolution ha hc
    (Real.one_le_exp_iff.mpr (mul_nonneg hK (neg_nonneg.mpr hb)))
  · intro s _
    exact (sub_le_self b (sq_nonneg s)).trans hb
  · intro s _
    exact neg_nonpos.mpr (sq_nonneg s)
  · exact hmetric b c a hc hbound
  · intro s hs x
    exact ancientKappa_scalar_le_mul_sq F hF hc hs hbound x
  · intro s _ x
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    exact (hB _ (neg_nonpos.mpr (sq_nonneg (c * s))) x).1
  · exact halpha

theorem exists_ancientKappa_lCost_baseTime_le
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ 0, ∀ c a : ℝ, 1 ≤ c → 0 < a →
      (c ^ 2 - 1) * a ^ 2 ≤ -b → ∀ p q : F.M,
      lCost F.S b p q (a ^ 2) ≤
        Real.exp (K * (-b)) * c * lCost F.S 0 p q ((c * a) ^ 2) := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨K, hK, haction⟩ := exists_ancientKappa_lRegularizedAction_mul_le F hF
  refine ⟨K, hK, ?_⟩
  intro b hb c a hc ha hbound p q
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hca : 0 < c * a := mul_pos hcpos ha
  have hfactor : 0 < Real.exp (K * (-b)) * c := mul_pos (Real.exp_pos _) hcpos
  by_contra! hlt
  have hthreshold : lCost F.S 0 p q ((c * a) ^ 2) <
      lCost F.S b p q (a ^ 2) / (Real.exp (K * (-b)) * c) :=
    (lt_div_iff₀ hfactor).mpr (by simpa only [mul_comm] using hlt)
  obtain ⟨alpha, halpha, hstart, hend, hsmall⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected F.S 0 p q
      ((c * a) ^ 2) (sq_pos_of_pos hca) _ hthreshold
  rw [Real.sqrt_sq hca.le] at hend hsmall
  have hcomp := haction b hb c a hc ha.le hbound alpha halpha
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha (c * s)) :=
    halpha.comp (contDiff_const.mul contDiff_id).contMDiff
  have hupper := lCost_le_lRegularizedAction_of_scalar_nonneg F.S (T := b) (sq_nonneg a)
    (fun s hs x => by
      obtain ⟨B, hB⟩ := hF.globalScalarBound
      exact (hB _ ((sub_le_self b hs.1).trans hb) x).1)
    (fun s => alpha (c * s)) hbeta
  simp only [Real.sqrt_sq ha.le, mul_zero, hstart, hend] at hupper
  have hstrict :
      Real.exp (K * (-b)) * c * lRegularizedAction F.S 0 alpha 0 (c * a) <
        lCost F.S b p q (a ^ 2) := by
    simpa only [mul_comm] using (lt_div_iff₀ hfactor).mp hsmall
  exact (not_lt_of_ge (hupper.trans hcomp)) hstrict

theorem exists_ancientKappa_redLength_baseTime_le
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ 0, ∀ c a : ℝ, 1 ≤ c → 0 < a →
      (c ^ 2 - 1) * a ^ 2 ≤ -b → ∀ p q : F.M,
      redLength F.S b p q (a ^ 2) ≤
        Real.exp (K * (-b)) * c ^ 2 * redLength F.S 0 p q ((c * a) ^ 2) := by
  obtain ⟨K, hK, hcost⟩ := exists_ancientKappa_lCost_baseTime_le F hF
  refine ⟨K, hK, ?_⟩
  intro b hb c a hc ha hbound p q
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have h := div_le_div_of_nonneg_right (hcost b hb c a hc ha hbound p q)
    (by positivity : 0 ≤ 2 * a)
  simp only [redLength, Real.sqrt_sq ha.le, Real.sqrt_sq (mul_pos hcpos ha).le]
  convert h using 1
  first | rfl | field_simp [ha.ne', hcpos.ne']


theorem exists_ancientKappa_redLength_shift_le
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ 0, ∀ tau : ℝ, 0 < tau + b → ∀ p q : F.M,
      redLength F.S b p q (tau + b) ≤
        Real.exp (K * (-b)) * (tau / (tau + b)) * redLength F.S 0 p q tau := by
  obtain ⟨K, hK, hred⟩ := exists_ancientKappa_redLength_baseTime_le F hF
  refine ⟨K, hK, ?_⟩
  intro b hb tau hsigma p q
  have htau : 0 < tau := by linarith
  let a : ℝ := Real.sqrt (tau + b)
  let c : ℝ := Real.sqrt (tau / (tau + b))
  have ha : 0 < a := Real.sqrt_pos.mpr hsigma
  have ha2 : a ^ 2 = tau + b := Real.sq_sqrt hsigma.le
  have hratio : 1 ≤ tau / (tau + b) :=
    (le_div_iff₀ hsigma).mpr (by linarith)
  have hc : 1 ≤ c := Real.one_le_sqrt.mpr hratio
  have hc2 : c ^ 2 = tau / (tau + b) :=
    Real.sq_sqrt (div_nonneg htau.le hsigma.le)
  have hca2 : (c * a) ^ 2 = tau := by
    rw [mul_pow, hc2, ha2]
    exact div_mul_cancel₀ _ hsigma.ne'
  have hshift : (c ^ 2 - 1) * a ^ 2 = -b := by
    rw [hc2, ha2]
    field_simp [hsigma.ne']
    ring
  simpa only [ha2, hc2, hca2] using hred b hb c a hc ha hshift.le p q

theorem exists_ancientKappa_redLength_shift_bound
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ, -2 * b ≤ tau →
      ∀ p q : F.M, ∀ A : ℝ, 0 ≤ A → redLength F.S 0 p q tau ≤ A →
        redLength F.S b p q (tau + b) ≤ C * A := by
  obtain ⟨K, _, hred⟩ := exists_ancientKappa_redLength_shift_le F hF
  refine ⟨2 * Real.exp (K * (-b)), mul_pos (by norm_num) (Real.exp_pos _), ?_⟩
  intro tau htau p q A hA hlength
  have hsigma : 0 < tau + b := by linarith
  have htaupos : 0 < tau := by linarith
  have hratio : 0 ≤ tau / (tau + b) := div_nonneg htaupos.le hsigma.le
  have hratio2 : tau / (tau + b) ≤ 2 :=
    (div_le_iff₀ hsigma).mpr (by linarith)
  calc
    redLength F.S b p q (tau + b) ≤
        Real.exp (K * (-b)) * (tau / (tau + b)) * redLength F.S 0 p q tau :=
      hred b hb.le tau hsigma p q
    _ ≤ Real.exp (K * (-b)) * (tau / (tau + b)) * A :=
      mul_le_mul_of_nonneg_left hlength (mul_nonneg (Real.exp_pos _).le hratio)
    _ ≤ Real.exp (K * (-b)) * 2 * A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio2 (Real.exp_pos _).le) hA
    _ = (2 * Real.exp (K * (-b))) * A := by ring


theorem exists_ancientKappa_eventually_redLength_shift_le
    {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0)
    {A : ℝ} (hA : 0 ≤ A) (p : F.M) {tau : ℕ → ℝ}
    (htau : Tendsto tau atTop atTop) (q : ℕ → F.M)
    (hlength : ∀ᶠ i in atTop, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop,
      0 < tau i + b ∧ redLength F.S b p (q i) (tau i + b) ≤ C * A := by
  obtain ⟨C, hC, hbound⟩ := exists_ancientKappa_redLength_shift_bound F hF hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [htau.eventually_ge_atTop (-2 * b), hlength] with i htime hi
  exact ⟨by linarith, hbound (tau i) htime p (q i) A hA hi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
