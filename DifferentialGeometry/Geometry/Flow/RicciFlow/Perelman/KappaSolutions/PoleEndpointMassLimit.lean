import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointOriginalMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointPotentialIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNegativeNonflatness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNegativeScalar

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

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
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem tendsto_normalization_ratio
    {b : ℝ} {tau : ℕ → ℝ} (htau : Tendsto tau atTop atTop) :
    Tendsto (fun i => Real.exp (((Module.finrank ℝ E : ℝ) / 2) *
      (Real.log (tau i + b) - Real.log (tau i)))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun i => b / tau i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htau
  have hratio : Tendsto (fun i => (tau i + b) / tau i) atTop (𝓝 1) := by
    have hone : Tendsto (fun i => (1 : ℝ) + b / tau i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add hinv : Tendsto (fun i => (1 : ℝ) + b / tau i)
          atTop (𝓝 ((1 : ℝ) + 0)))
    apply hone.congr'
    filter_upwards [htau.eventually_gt_atTop 0] with i hi
    rw [add_div, div_self hi.ne']
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (hlog.const_mul ((Module.finrank ℝ E : ℝ) / 2))
  have h' : Tendsto (fun i => Real.exp (((Module.finrank ℝ E : ℝ) / 2) *
      Real.log ((tau i + b) / tau i))) atTop (𝓝 1) := by
    simpa only [Real.log_one, mul_zero, Real.exp_zero, Function.comp_def] using h
  apply h'.congr'
  filter_upwards [htau.eventually_gt_atTop (max 0 (-b))] with i hi
  have hpos : 0 < tau i := lt_of_le_of_lt (le_max_left _ _) hi
  have hsigma : 0 < tau i + b := by
    have h := lt_of_le_of_lt (le_max_right 0 (-b)) hi
    linarith
  rw [Real.log_div hsigma.ne' hpos.ne']

private theorem asymptoticReducedVolume_pole_eq_of_ancient
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (p : F.M) {A : ℝ}
    (hancient : ∀ i, IsAncientKappaSolution kappa
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i))
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i).S
      0 p (q i) 1 ≤ A) :
    asymptoticReducedVolume F.S b p = asymptoticReducedVolume F.S 0 p := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let mu (i : ℕ) : Measure F.M :=
    riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)
  let V0 (i : ℕ) : ℝ := ∫ x : F.M, Real.exp (-redLength F.S 0 p x (tau i)) ∂mu i
  let Vb (i : ℕ) : ℝ := ∫ x : F.M, Real.exp (-redLength (U.term i).S 0 p x 1) ∂mu i
  let k0 : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let c (i : ℕ) : ℝ := Real.exp (((Module.finrank ℝ E : ℝ) / 2) *
    (Real.log (tau i + b) - Real.log (tau i)))
  have hk0 : 0 < k0 := Real.exp_pos _
  have hmonoB : AntitoneOn (intrinsicReducedVolume F.S b p) (Ioi 0) :=
    ancient_reducedVolume_antitone_of_regular_base F hF p hb
  have hmono0 : AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) :=
    ancient_reducedVolume_antitone F hF p
  have hsigmaTop : Tendsto (fun i => tau i + b) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [hescape.eventually_ge_atTop (R - b)] with i hi
    linarith
  have hmassB : Tendsto (fun i => intrinsicReducedVolume F.S b p (tau i + b))
      atTop (𝓝 (asymptoticReducedVolume F.S b p)) := by
    simpa only [mul_one] using intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
      F.S b p hmonoB hsigma hsigmaTop (a := 1) zero_lt_one
  have hmass0 : Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau i))
      atTop (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
    simpa only [mul_one] using intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
      F.S 0 p hmono0 htau hescape (a := 1) zero_lt_one
  obtain ⟨hIntB, hInt0⟩ := poleEndpoint_exp_redLength_integrable
    F hdim hF hb tau htau hescape q hsigma p hancient hbase
  have hfiniteIntegral :
      (∫⁻ x : F.M, ENNReal.ofReal (Real.exp (-redLength (U.term 0).S 0 p x 1))
        ∂mu 0) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable (hIntB 0).aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mpr (hIntB 0)
  have hmassSliceFinite : intrinsicReducedVolume F.S b p (tau 0 + b) ≠ ⊤ := by
    have hraw := poleEndpoint_lintegral_pole_redLength F hF.carrier_eq hF.regular_eq
      b hb.le tau q hsigma 0 p
    rw [← hraw]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfiniteIntegral
  have hmassFinite : asymptoticReducedVolume F.S b p ≠ ⊤ :=
    ne_top_of_le_ne_top hmassSliceFinite
      (iInf_le (fun t : Ioi (0 : ℝ) => intrinsicReducedVolume F.S b p t)
        ⟨tau 0 + b, hsigma 0⟩)
  have hmassBReal := (ENNReal.continuousAt_toReal hmassFinite).tendsto.comp hmassB
  have hBreal (i : ℕ) : k0 * Vb i = (intrinsicReducedVolume F.S b p (tau i + b)).toReal := by
    have hraw := poleEndpoint_lintegral_pole_redLength F hF.carrier_eq hF.regular_eq
      b hb.le tau q hsigma i p
    have hcast := congrArg ENNReal.toReal hraw
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk0.le] at hcast
    have hbochner : Vb i = (∫⁻ x : F.M,
        ENNReal.ofReal (Real.exp (-redLength (U.term i).S 0 p x 1)) ∂mu i).toReal := by
      apply integral_eq_lintegral_of_nonneg_ae
      · exact Eventually.of_forall fun x => (Real.exp_pos _).le
      · with_unfolding_all exact (hIntB i).aestronglyMeasurable
    change k0 * Vb i = _
    change k0 * (∫⁻ x : F.M, ENNReal.ofReal
      (Real.exp (-redLength (U.term i).S 0 p x 1)) ∂mu i).toReal = _ at hcast
    with_unfolding_all rw [← hbochner] at hcast
    exact hcast
  have hVb : Tendsto Vb atTop (𝓝 ((asymptoticReducedVolume F.S b p).toReal / k0)) := by
    have h := hmassBReal.div_const k0
    apply h.congr
    intro i
    simp only [Function.comp_apply]
    rw [← hBreal i]
    exact mul_div_cancel_left₀ (Vb i) hk0.ne'
  have hdiff : Tendsto (fun i => V0 i - Vb i) atTop (𝓝 0) :=
    poleEndpoint_integral_exp_redLength_sub_tendsto_zero
      F hdim hF hb tau htau hescape q hsigma p hancient hbase
  have hV0 : Tendsto V0 atTop (𝓝 ((asymptoticReducedVolume F.S b p).toReal / k0)) := by
    have h := hdiff.add hVb
    simpa only [sub_add_cancel, zero_add] using h
  have hc : Tendsto c atTop (𝓝 1) := tendsto_normalization_ratio (E := E) hescape
  have hscaled : Tendsto (fun i => c i * k0 * V0 i)
      atTop (𝓝 (asymptoticReducedVolume F.S b p).toReal) := by
    have h := (hc.mul_const k0).mul hV0
    have hcancel : k0 * ((asymptoticReducedVolume F.S b p).toReal / k0) =
        (asymptoticReducedVolume F.S b p).toReal :=
      mul_div_cancel₀ _ hk0.ne'
    simpa only [one_mul, hcancel] using h
  have hscaledENN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hscaled
  have hscaledTarget : ENNReal.ofReal (asymptoticReducedVolume F.S b p).toReal =
      asymptoticReducedVolume F.S b p := ENNReal.ofReal_toReal hmassFinite
  rw [hscaledTarget] at hscaledENN
  have heq : ∀ᶠ i in atTop,
      ENNReal.ofReal (c i * k0 * V0 i) = intrinsicReducedVolume F.S 0 p (tau i) := by
    filter_upwards [hInt0] with i hi
    change ENNReal.ofReal (c i * k0 * (∫ x : F.M,
      Real.exp (-redLength F.S 0 p x (tau i)) ∂mu i)) = _
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le hk0.le),
      ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact poleEndpoint_lintegral_original_redLength F hF.carrier_eq hF.regular_eq
      b hb.le tau q hsigma i p
  exact tendsto_nhds_unique (hscaledENN.congr' heq) hmass0


private theorem asymptoticReducedVolume_eq_terminal_of_nonflat_pole
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0)
    (x : F.M)
    (hx : Tensor0SBundle.normSq0S (F.S.base.metric b) x 4 (F.S.base.rm04 b x) ≠ 0)
    (p : F.M) :
    asymptoticReducedVolume F.S b p = asymptoticReducedVolume F.S 0 p := by
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1 - b
  have htau (i : ℕ) : 0 < tau i := by
    dsimp only [tau]
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hsigma (i : ℕ) : 0 < tau i + b := by
    dsimp only [tau]
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hescape : Tendsto tau atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient_of_neg
    F hF p hb (hsigma i)
  have hancient (i : ℕ) : IsAncientKappaSolution kappa
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i) :=
    isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
      F hF b (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) hb.le (q i) le_rfl x hx
  have hbase (i : ℕ) : redLength
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i).S
      0 p (q i) 1 ≤ (Module.finrank ℝ E : ℝ) / 2 := by
    rw [poleRescaledFlowSeq_redLength_one F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma]
    exact hq i
  exact asymptoticReducedVolume_pole_eq_of_ancient
    F hdim hF hb tau htau hescape q hsigma p hancient hbase

theorem asymptoticReducedVolume_eq_terminal_of_negative
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0) (p : F.M) :
    asymptoticReducedVolume F.S b p = asymptoticReducedVolume F.S 0 p := by
  obtain ⟨x, hx⟩ := hF.exists_rmNormSq_ne_zero_at_of_negative hb
  exact asymptoticReducedVolume_eq_terminal_of_nonflat_pole F hdim hF hb x hx p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
