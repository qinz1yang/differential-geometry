import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.BaseTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedCostDyadicComparison
import DifferentialGeometry.Analysis.Asymptotics.MultiplicativeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

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

omit [I.Boundaryless] in
private theorem lCost_nonneg_of_ancient_time
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 ≤ tau) (p q : F.M) :
    0 ≤ lCost F.S T p q tau := by
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  exact lCost_nonneg_of_scalar_nonneg F.S T htau
    (fun s hs x => (hR (T - s) ((sub_le_self T hs.1).trans hT) x).1) p q

theorem exists_ancientKappa_lCost_baseTime_mul_add_bounds
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {d delta : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) :
    ∃ C T : ℝ, 0 ≤ C ∧ d < T ∧ ∀ tau > T, ∀ p q : F.M,
      lCost F.S (-d) p q (tau - d) ≤ (1 + delta) * lCost F.S 0 p q tau + C ∧
      lCost F.S 0 p q tau ≤ (1 + delta) * lCost F.S (-d) p q (tau - d) + C := by
  obtain ⟨R, hR, hforward⟩ := exists_ancientKappa_lCost_terminal_le_sqrt_mul_add F hF
  obtain ⟨B, hB, hreverse⟩ := exists_ancientKappa_lCost_shift_le_mul_terminal_add F hdim hF
  obtain ⟨n, hn⟩ := exists_nat_gt (16 / delta)
  have hfrac : 16 / (n + 1 : ℝ) ≤ delta := by
    apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
    have h := (div_lt_iff₀ hdelta).mp hn
    nlinarith
  let a : ℝ := Real.sqrt (d / delta) + 1
  let L : ℝ := 2 * Real.sqrt d + 1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hdL : 4 * d ≤ L ^ 2 := by
    dsimp only [L]
    nlinarith [Real.sq_sqrt hd.le, Real.sqrt_nonneg d]
  have hda : d ≤ delta * a ^ 2 := by
    have hs := Real.sq_sqrt (div_nonneg hd.le hdelta.le)
    have hdiv : delta * (d / delta) = d := mul_div_cancel₀ d hdelta.ne'
    have hlarge : d / delta ≤ a ^ 2 := by
      dsimp only [a]
      nlinarith [Real.sqrt_nonneg (d / delta)]
    nlinarith [mul_le_mul_of_nonneg_left hlarge hdelta.le]
  have hfactor : Real.sqrt (a ^ 2 + d) / a ≤ 1 + delta := by
    apply (div_le_iff₀ ha).mpr
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by positivity) ha.le, ?_⟩
    nlinarith [mul_nonneg hdelta.le (sq_nonneg a),
      mul_nonneg (sq_nonneg delta) (sq_nonneg a)]
  let C1 : ℝ := 2 * R * (Real.sqrt (a ^ 2 + d)) ^ 3
  let C2 : ℝ := B * (L * (4 : ℝ) ^ n) ^ 3
  let T : ℝ := max (a ^ 2 + d) ((L * (4 : ℝ) ^ n) ^ 2) + d + 1
  have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp only [C2]; positivity
  have hT : d < T := by
    dsimp only [T]
    have hmax := (sq_nonneg (L * (4 : ℝ) ^ n)).trans (le_max_right (a ^ 2 + d) _)
    linarith
  refine ⟨max C1 C2, T, hC1.trans (le_max_left _ _), hT, ?_⟩
  intro tau htau p q
  have hforwardTime : a ^ 2 + d < tau := by
    have hmax := le_max_left (a ^ 2 + d) ((L * (4 : ℝ) ^ n) ^ 2)
    dsimp only [T] at htau
    linarith
  have hreverseTime : (L * (4 : ℝ) ^ n) ^ 2 < tau := by
    have hmax := le_max_right (a ^ 2 + d) ((L * (4 : ℝ) ^ n) ^ 2)
    dsimp only [T] at htau
    linarith
  have hpos : 0 < tau := hd.trans (hT.trans htau)
  have hsigma : 0 < tau - d := sub_pos.mpr (hT.trans htau)
  constructor
  · apply (hreverse d L tau n hd hL hdL hreverseTime p q).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right (add_le_add_right hfrac 1)
        (lCost_nonneg_of_ancient_time F hF le_rfl hpos.le p q))
      (le_max_right C1 C2)
  · apply (hforward d a tau hd.le ha hforwardTime p q).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right hfactor
        (lCost_nonneg_of_ancient_time F hF (neg_nonpos.mpr hd.le) hsigma.le p q))
      (le_max_left C1 C2)

theorem tendsto_lCost_baseTime_sub_div_sqrt_of_redLength_le
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {d : ℝ} (hd : 0 < d)
    (p : F.M) {tau : ℕ → ℝ} (htau : Tendsto tau atTop atTop) (q : ℕ → F.M)
    {A : ℝ} (hbound : ∀ᶠ i in atTop, redLength F.S 0 p (q i) (tau i) ≤ A) :
    Tendsto (fun i =>
      lCost F.S (-d) p (q i) (tau i - d) / (2 * Real.sqrt (tau i)) -
        redLength F.S 0 p (q i) (tau i)) atTop (𝓝 0) := by
  apply DifferentialGeometry.Analysis.tendsto_sub_zero_of_mul_add_div_sqrt_bounds htau hbound
  · intro delta hdelta
    obtain ⟨C, T, _, _, hcompare⟩ :=
      exists_ancientKappa_lCost_baseTime_mul_add_bounds F hdim hF hd hdelta
    refine ⟨C / 2, ?_⟩
    filter_upwards [htau.eventually_gt_atTop (max T 0)] with i hi
    have ht : T < tau i := lt_of_le_of_lt (le_max_left _ _) hi
    have hpos : 0 < tau i := lt_of_le_of_lt (le_max_right _ _) hi
    have h := div_le_div_of_nonneg_right ((hcompare (tau i) ht p (q i)).1)
      (by positivity : 0 ≤ 2 * Real.sqrt (tau i))
    change lCost F.S (-d) p (q i) (tau i - d) / (2 * Real.sqrt (tau i)) ≤ _
    exact h.trans_eq (by unfold redLength; ring)
  · intro delta hdelta
    obtain ⟨C, T, _, _, hcompare⟩ :=
      exists_ancientKappa_lCost_baseTime_mul_add_bounds F hdim hF hd hdelta
    refine ⟨C / 2, ?_⟩
    filter_upwards [htau.eventually_gt_atTop (max T 0)] with i hi
    have ht : T < tau i := lt_of_le_of_lt (le_max_left _ _) hi
    have hpos : 0 < tau i := lt_of_le_of_lt (le_max_right _ _) hi
    have h := div_le_div_of_nonneg_right ((hcompare (tau i) ht p (q i)).2)
      (by positivity : 0 ≤ 2 * Real.sqrt (tau i))
    change redLength F.S 0 p (q i) (tau i) ≤ _
    exact h.trans_eq (by ring)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
