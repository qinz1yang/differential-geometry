import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.DynamicProgramming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMinimizerInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PrescribedTangentInOpenSet
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

private theorem deriv_le_of_eventually_integral_upper_bound
    {f L : ℝ → ℝ} {b d : ℝ} (hf : HasDerivAt f d b)
    (hL : Continuous L)
    (hbound : ∀ᶠ a in 𝓝[<] b, f b ≤ f a + ∫ s in a..b, L s) :
    d ≤ L b := by
  have hI : HasDerivAt (fun a ↦ ∫ s in a..b, L s) (-L b) b :=
    intervalIntegral.integral_hasDerivAt_left
      (by simp) hL.stronglyMeasurable.stronglyMeasurableAtFilter hL.continuousAt
  have hG := hf.add hI
  have hlim := hG.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b)
  have hnonpos : d + -L b ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [hbound, self_mem_nhdsWithin] with a ha hab
    rw [slope_def_field]
    apply div_nonpos_of_nonneg_of_nonpos
    · simpa only [Pi.add_apply, intervalIntegral.integral_same, add_zero, sub_nonneg] using ha
    · exact sub_nonpos.mpr hab.le
  linarith

theorem ancient_lCost_terminal_le_add_lRegularizedAction
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (p : F.M) (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost F.S 0 p (alpha b) (b ^ 2) ≤
      lCost F.S 0 p (alpha a) (a ^ 2) + lRegularizedAction F.S 0 alpha a b := by
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  apply lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier F.S F.isSolution K 0 ha hab
    (fun t ht ↦ ht.2) (fun t ht y ↦ hK t ht.2 y) p alpha halpha

private theorem ancient_lCost_terminal_upper_test_deriv_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {b d : ℝ} (hb : 0 < b)
    (p : F.M) (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (phi : ℝ → ℝ) (hphi : HasDerivAt phi d b)
    (heq : lCost F.S 0 p (alpha b) (b ^ 2) = phi b)
    (hupper : ∀ᶠ a in 𝓝 b, lCost F.S 0 p (alpha a) (a ^ 2) ≤ phi a) :
    d ≤ lRegularizedLagrangian F.S 0 alpha b := by
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hlag : Continuous (fun a ↦ lRegularizedLagrangian F.S 0 alpha a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
    exact h.comp_continuous (continuous_const.prodMk continuous_id)
      (fun a ↦ by change 0 - a ^ 2 ≤ 0; nlinarith [sq_nonneg a])
  apply deriv_le_of_eventually_integral_upper_bound hphi hlag
  filter_upwards [hupper.filter_mono nhdsWithin_le_nhds,
    (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with a haupper ha hab
  rw [← heq]
  exact (ancient_lCost_terminal_le_add_lRegularizedAction F hF ha hab p alpha halpha).trans
    (add_le_add haupper le_rfl)

theorem ancient_lCost_hamilton_jacobi_upper_test_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {b : ℝ} (hb : 0 < b) (p q : F.M) (phi : ℝ → F.M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi z.1 z.2) (b, q))
    (heq : lCost F.S 0 p q (b ^ 2) = phi b q)
    (hupper : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q),
      lCost F.S 0 p z.2 (z.1 ^ 2) ≤ phi z.1 z.2) :
    deriv (fun a ↦ phi a q) b +
        (1 / 2 : ℝ) * (F.S.base.metric (-(b ^ 2))).inner q
          (gradientFun (F.S.base.metric (-(b ^ 2))) (phi b) q)
          (gradientFun (F.S.base.metric (-(b ^ 2))) (phi b) q) -
        2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q ≤ 0 := by
  let g := F.S.base.metric (-(b ^ 2))
  let v := gradientFun g (phi b) q
  obtain ⟨eta, heta, _, heta0, hetav⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Variation.exists_smooth_curve
      q v Set.univ isOpen_univ (Set.mem_univ q)
  let alpha : ℝ → F.M := fun a ↦ eta (a - b)
  have hshift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun a : ℝ ↦ a - b) :=
    contMDiff_id.sub contMDiff_const
  have halpha : ContMDiff 𝓘(ℝ, ℝ) I ∞ alpha := heta.comp hshift
  have halphab : alpha b = q := by simp only [alpha, sub_self, heta0]
  have halphav : mfderiv 𝓘(ℝ, ℝ) I alpha b 1 = v := by
    have h := mfderiv_comp_apply_of_eq b (heta.mdifferentiableAt (by simp))
      (hshift.mdifferentiableAt (by simp)) (sub_self b) (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I alpha b 1 = _ at h
    rw [h]
    have hsd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun a : ℝ ↦ a - b) b 1 = 1 := by
      rw [mfderiv_eq_fderiv]
      change (fderiv ℝ (fun a : ℝ ↦ a - b) b) (1 : ℝ) = 1
      rw [fderiv_apply_one_eq_deriv]
      simpa only [id_eq] using ((hasDerivAt_id b).sub_const b).deriv
    erw [hsd]
    exact hetav
  have htime : HasDerivAt (fun a ↦ phi a (alpha b))
      (deriv (fun a ↦ phi a q) b) b := by
    rw [halphab]
    exact (hphi.comp b (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt.hasDerivAt
  have hcurve := DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve g
    (by simpa only [halphab] using hphi)
    (halpha.mdifferentiableAt (by simp)) htime
  have htend : Tendsto (fun a ↦ (a, alpha a)) (𝓝 b) (𝓝 (b, q)) := by
    simpa only [halphab, id_eq] using ((continuous_id.prodMk halpha.continuous).continuousAt (x := b)).tendsto
  have hbound := ancient_lCost_terminal_upper_test_deriv_le F hF hb p alpha
    (halpha.of_le (by simp)) (fun a ↦ phi a (alpha a)) hcurve
    (by simpa only [halphab] using heq) (htend.eventually hupper)
  simp only [lRegularizedLagrangian, lVelocity, zero_sub] at hbound
  erw [halphav, halphab] at hbound
  change deriv (fun a ↦ phi a q) b + (1 / 2 : ℝ) * g.inner q v v -
    2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q ≤ 0
  change deriv (fun a ↦ phi a q) b + g.inner q v v ≤
    (1 / 2 : ℝ) * g.inner q v v + 2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q at hbound
  linarith

theorem ancient_lCost_hamilton_jacobi_lower_test_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {b : ℝ} (hb : 0 < b) (p q : F.M) (phi : ℝ → F.M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi z.1 z.2) (b, q))
    (heq : lCost F.S 0 p q (b ^ 2) = phi b q)
    (hlower : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q),
      phi z.1 z.2 ≤ lCost F.S 0 p z.2 (z.1 ^ 2)) :
    0 ≤ deriv (fun a ↦ phi a q) b +
        (1 / 2 : ℝ) * (F.S.base.metric (-(b ^ 2))).inner q
          (gradientFun (F.S.base.metric (-(b ^ 2))) (phi b) q)
          (gradientFun (F.S.base.metric (-(b ^ 2))) (phi b) q) -
        2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q := by
  obtain ⟨alpha, halpha, _, hstart, hend, hcost, _⟩ :=
    exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient F hF p q (sq_pos_of_pos hb)
  rw [Real.sqrt_sq hb.le] at hend hcost
  let g := F.S.base.metric (-(b ^ 2))
  have hlag : Continuous (fun a ↦ lRegularizedLagrangian F.S 0 alpha a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
    exact h.comp_continuous (continuous_const.prodMk continuous_id)
      (fun a ↦ by change 0 - a ^ 2 ≤ 0; nlinarith [sq_nonneg a])
  have haction : HasDerivAt (fun a => lRegularizedAction F.S 0 alpha 0 a)
      (lRegularizedLagrangian F.S 0 alpha b) b :=
    intervalIntegral.integral_hasDerivAt_right (hlag.intervalIntegrable 0 b)
      hlag.stronglyMeasurable.stronglyMeasurableAtFilter hlag.continuousAt
  have htime : HasDerivAt (fun a ↦ phi a (alpha b))
      (deriv (fun a ↦ phi a q) b) b := by
    rw [hend]
    exact (hphi.comp b (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt.hasDerivAt
  have hcurve := DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve g
    (by simpa only [hend] using hphi)
    (halpha.mdifferentiableAt (by norm_num)) htime
  have htend : Tendsto (fun a ↦ (a, alpha a)) (𝓝 b) (𝓝 (b, q)) := by
    simpa only [hend, id_eq] using ((continuous_id.prodMk halpha.continuous).continuousAt (x := b)).tendsto
  have hmax : IsLocalMax (fun a => phi a (alpha a) - lRegularizedAction F.S 0 alpha 0 a) b := by
    filter_upwards [htend.eventually hlower, eventually_gt_nhds hb] with a ha hapos
    change phi a (alpha a) - lRegularizedAction F.S 0 alpha 0 a ≤
      phi b (alpha b) - lRegularizedAction F.S 0 alpha 0 b
    have hbound := lCost_le_lRegularizedAction_of_scalar_nonneg F.S (sq_nonneg a)
      (T := 0) (by
        obtain ⟨B, hB⟩ := hF.globalScalarBound
        intro t ht y
        simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1) alpha halpha
    rw [Real.sqrt_sq hapos.le, hstart] at hbound
    rw [hend, hcost, heq]
    linarith
  have heqderiv := hmax.hasDerivAt_eq_zero (hcurve.sub haction)
  let v := mfderiv 𝓘(ℝ, ℝ) I alpha b 1
  let w := gradientFun g (phi b) (alpha b)
  have hsq := metric_inner_self_nonneg g (alpha b) (v - w)
  simp only [map_sub, sub_apply] at hsq
  have hsym := g.symm (alpha b) v w
  simp only [lRegularizedLagrangian, lVelocity, zero_sub] at heqderiv
  change deriv (fun a ↦ phi a q) b + g.inner (alpha b) w v -
    ((1 / 2 : ℝ) * g.inner (alpha b) v v +
      2 * b ^ 2 * F.S.scalar (-(b ^ 2)) (alpha b)) = 0 at heqderiv
  have h := show 0 ≤ deriv (fun a ↦ phi a q) b +
      (1 / 2 : ℝ) * g.inner (alpha b) w w -
        2 * b ^ 2 * F.S.scalar (-(b ^ 2)) (alpha b) by nlinarith
  change 0 ≤ deriv (fun a ↦ phi a q) b +
    (1 / 2 : ℝ) * g.inner (alpha b) (gradientFun g (phi b) (alpha b))
      (gradientFun g (phi b) (alpha b)) - 2 * b ^ 2 * F.S.scalar (-(b ^ 2)) (alpha b) at h
  rw [hend] at h
  exact h

omit [I.Boundaryless] in
private theorem hamiltonian_square_root_rescaling
    {tau : ℝ} (htau : 0 < tau) (q : F.M) (phi : ℝ → F.M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi z.1 z.2) (tau, q)) :
    let b := Real.sqrt tau
    let psi : ℝ → F.M → ℝ := fun a y ↦ 2 * a * phi (a ^ 2) y
    deriv (fun a ↦ psi a q) b +
        (1 / 2 : ℝ) * (F.S.base.metric (-(b ^ 2))).inner q
          (gradientFun (F.S.base.metric (-(b ^ 2))) (psi b) q)
          (gradientFun (F.S.base.metric (-(b ^ 2))) (psi b) q) -
        2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q =
      4 * tau * (deriv (fun a ↦ phi a q) tau +
        (1 / 2 : ℝ) * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q)
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q) -
        (1 / 2 : ℝ) * F.S.scalar (-tau) q + phi tau q / (2 * tau)) := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  let psi : ℝ → F.M → ℝ := fun a y ↦ 2 * a * phi (a ^ 2) y
  have htime : HasDerivAt (fun a ↦ phi a q) (deriv (fun a ↦ phi a q) tau) tau := by
    have htmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun a ↦ phi a q) tau :=
      hphi.comp tau (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    exact htmd.differentiableAt.hasDerivAt
  have hpsitime : HasDerivAt (fun a ↦ psi a q)
      (2 * phi tau q + 4 * tau * deriv (fun a ↦ phi a q) tau) b := by
    have htimeb : HasDerivAt (fun a ↦ phi a q) (deriv (fun a ↦ phi a q) tau) (b ^ 2) := by
      rw [hb2]
      exact htime
    have hsq : HasDerivAt (fun a : ℝ ↦ a ^ 2) (2 * b) b := by
      simpa using hasDerivAt_pow 2 b
    have h := ((hasDerivAt_id b).const_mul 2).mul (htimeb.comp b (h := fun a : ℝ ↦ a ^ 2) hsq)
    apply h.congr_deriv
    simp only [id_eq, Function.comp_apply, hb2, mul_one]
    calc
      2 * phi tau q + 2 * b * (deriv (fun a ↦ phi a q) tau * (2 * b)) =
          2 * phi tau q + 4 * b ^ 2 * deriv (fun a ↦ phi a q) tau := by ring
      _ = _ := by rw [hb2]
  have hspace : MDifferentiableAt I 𝓘(ℝ, ℝ) (phi tau) q :=
    hphi.comp q (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hgrad : gradientFun (F.S.base.metric (-(b ^ 2))) (psi b) q =
      (2 * b) • gradientFun (F.S.base.metric (-tau)) (phi tau) q := by
    rw [hb2]
    change gradientFun (F.S.base.metric (-tau)) ((2 * b) • phi (b ^ 2)) q = _
    rw [hb2, gradientFun_const_smul _ _ hspace]
  change deriv (fun a ↦ psi a q) b + _ - _ = _
  rw [hpsitime.deriv, hgrad, hb2,
    DifferentialGeometry.SmoothRiemannianMetric.metric_inner_smul_self]
  have hs : (2 * b) ^ 2 = 4 * tau := by nlinarith [hb2]
  rw [hs]
  field_simp
  ring

theorem ancient_redLength_hamilton_jacobi_upper_test_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) (phi : ℝ → F.M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi z.1 z.2) (tau, q))
    (heq : redLength F.S 0 p q tau = phi tau q)
    (hupper : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q),
      redLength F.S 0 p z.2 z.1 ≤ phi z.1 z.2) :
    deriv (fun a ↦ phi a q) tau +
        (1 / 2 : ℝ) * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q)
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q) -
        (1 / 2 : ℝ) * F.S.scalar (-tau) q + phi tau q / (2 * tau) ≤ 0 := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  let psi : ℝ → F.M → ℝ := fun a y ↦ 2 * a * phi (a ^ 2) y
  have hmap : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun z : ℝ × F.M ↦ (z.1 ^ 2, z.2)) (b, q) :=
    (mdifferentiableAt_fst.pow 2).prodMk mdifferentiableAt_snd
  have hcomp : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi (z.1 ^ 2) z.2) (b, q) := by
    exact hphi.comp_of_eq (b, q) hmap (by rw [hb2])
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ psi z.1 z.2) (b, q) :=
    (mdifferentiableAt_const.mul mdifferentiableAt_fst).mul hcomp
  have hscale (a : ℝ) (ha : 0 < a) (y : F.M) :
      lCost F.S 0 p y (a ^ 2) = 2 * a * redLength F.S 0 p y (a ^ 2) := by
    simp only [redLength, Real.sqrt_sq ha.le]
    field_simp
  have hpsieq : lCost F.S 0 p q (b ^ 2) = psi b q := by
    change lCost F.S 0 p q (b ^ 2) = 2 * b * phi (b ^ 2) q
    rw [hscale b hb q, hb2, heq]
  have htend : Tendsto (fun z : ℝ × F.M ↦ (z.1 ^ 2, z.2))
      (𝓝 (b, q)) (𝓝 (tau, q)) := by
    simpa only [hb2] using hmap.continuousAt.tendsto
  have hpsiupper : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q),
      lCost F.S 0 p z.2 (z.1 ^ 2) ≤ psi z.1 z.2 := by
    have hpos : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q), 0 < z.1 :=
      (continuous_fst.continuousAt.tendsto).eventually (eventually_gt_nhds hb)
    filter_upwards [htend.eventually hupper, hpos] with z hz hzp
    rw [hscale z.1 hzp z.2]
    exact mul_le_mul_of_nonneg_left hz (by positivity)
  have hHJ := ancient_lCost_hamilton_jacobi_upper_test_terminal F hF hb p q psi
    hpsi hpsieq hpsiupper
  rw [hamiltonian_square_root_rescaling F htau q phi hphi] at hHJ
  exact nonpos_of_mul_nonpos_right hHJ (by positivity)

theorem ancient_redLength_hamilton_jacobi_lower_test_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) (phi : ℝ → F.M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi z.1 z.2) (tau, q))
    (heq : redLength F.S 0 p q tau = phi tau q)
    (hlower : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q),
      phi z.1 z.2 ≤ redLength F.S 0 p z.2 z.1) :
    0 ≤ deriv (fun a ↦ phi a q) tau +
        (1 / 2 : ℝ) * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q)
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q) -
        (1 / 2 : ℝ) * F.S.scalar (-tau) q + phi tau q / (2 * tau) := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  let psi : ℝ → F.M → ℝ := fun a y ↦ 2 * a * phi (a ^ 2) y
  have hmap : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun z : ℝ × F.M ↦ (z.1 ^ 2, z.2)) (b, q) :=
    (mdifferentiableAt_fst.pow 2).prodMk mdifferentiableAt_snd
  have hcomp : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi (z.1 ^ 2) z.2) (b, q) := by
    exact hphi.comp_of_eq (b, q) hmap (by rw [hb2])
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ psi z.1 z.2) (b, q) :=
    (mdifferentiableAt_const.mul mdifferentiableAt_fst).mul hcomp
  have hscale (a : ℝ) (ha : 0 < a) (y : F.M) :
      lCost F.S 0 p y (a ^ 2) = 2 * a * redLength F.S 0 p y (a ^ 2) := by
    simp only [redLength, Real.sqrt_sq ha.le]
    field_simp
  have hpsieq : lCost F.S 0 p q (b ^ 2) = psi b q := by
    change lCost F.S 0 p q (b ^ 2) = 2 * b * phi (b ^ 2) q
    rw [hscale b hb q, hb2, heq]
  have htend : Tendsto (fun z : ℝ × F.M ↦ (z.1 ^ 2, z.2))
      (𝓝 (b, q)) (𝓝 (tau, q)) := by
    simpa only [hb2] using hmap.continuousAt.tendsto
  have hpsilower : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q),
      psi z.1 z.2 ≤ lCost F.S 0 p z.2 (z.1 ^ 2) := by
    have hpos : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q), 0 < z.1 :=
      (continuous_fst.continuousAt.tendsto).eventually (eventually_gt_nhds hb)
    filter_upwards [htend.eventually hlower, hpos] with z hz hzp
    rw [hscale z.1 hzp z.2]
    exact mul_le_mul_of_nonneg_left hz (by positivity)
  have hHJ := ancient_lCost_hamilton_jacobi_lower_test_terminal F hF hb p q psi
    hpsi hpsieq hpsilower
  rw [hamiltonian_square_root_rescaling F htau q phi hphi] at hHJ
  exact nonneg_of_mul_nonneg_right hHJ (by positivity)

theorem ancient_redLength_hamilton_jacobi_of_mdifferentiableAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M)
    (h : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ redLength F.S 0 p z.2 z.1) (tau, q)) :
    2 * deriv (fun a ↦ redLength F.S 0 p q a) tau +
        (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (fun y => redLength F.S 0 p y tau) q)
          (gradientFun (F.S.base.metric (-tau)) (fun y => redLength F.S 0 p y tau) q) -
        F.S.scalar (-tau) q + redLength F.S 0 p q tau / tau = 0 := by
  have hu := ancient_redLength_hamilton_jacobi_upper_test_terminal F hF htau p q
    (fun a y => redLength F.S 0 p y a) h rfl (Eventually.of_forall (fun _ => le_rfl))
  have hl := ancient_redLength_hamilton_jacobi_lower_test_terminal F hF htau p q
    (fun a y => redLength F.S 0 p y a) h rfl (Eventually.of_forall (fun _ => le_rfl))
  have heq := le_antisymm hu hl
  simp only [div_eq_mul_inv, mul_inv_rev] at heq ⊢
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
